module

public section

/-!
# Narrow POSIX descriptor adapter

Trust-anchor loading reads system files through one unbuffered file
descriptor so descriptor custody is explicit from acquisition through the one
consuming close.  This module is that entire native boundary: the extern
declarations are each one syscall wide, and every constant, validation rule,
and cleanup sequence lives in Lean.
-/

namespace Grpc.Posix

/-! ## Scalar types at the POSIX boundary -/

abbrev Fd := UInt32
abbrev Errno := UInt32
abbrev SysResult (α : Type) := Except Errno α

/-!
## POSIX constants for the supported platforms

These are ABI values, not native behavior.  Keeping them in Lean makes every
policy choice visible in the code that applies it and leaves the C boundary as
a set of raw syscall adapters.  The supported platforms are Darwin and the
Linux architectures on which these values share one ABI (currently x86-64 and
AArch64).
-/

namespace Constants

private def darwin : Bool := System.Platform.isOSX

-- errno(2)
def eperm : UInt32 := 1
def eintr : UInt32 := 4
def eio : UInt32 := 5
def eacces : UInt32 := 13
def einval : UInt32 := 22

-- Integer and descriptor ABI bounds.
def cIntMax : UInt32 := 2_147_483_647
def signedInt64Max : UInt64 := 0x7fff_ffff_ffff_ffff

-- open(2)
def oRdonly : Int32 := 0
def oNonblock : Int32 := if darwin then 0x00000004 else 0x00000800
def oCloexec : Int32 := if darwin then 0x01000000 else 0x00080000

-- stat(2) mode layout.
def fileTypeMask : UInt64 := 0o170000
def regularFileType : UInt64 := 0o100000

end Constants

namespace Errno

def interrupted : Errno := Constants.eintr
def io : Errno := Constants.eio
def invalidArgument : Errno := Constants.einval
def permissionDenied : Errno := Constants.eperm
def accessDenied : Errno := Constants.eacces

end Errno

/-! ## Raw single-operation bindings -/

namespace Native

@[extern "lean_grpc_posix_strerror_raw"]
opaque strerrorRaw (error : Errno) : String

@[extern "lean_grpc_posix_open_raw"]
opaque openRaw
    (path : @& String) (flags : Int32) (mode : UInt32) : IO (SysResult Fd)

@[extern "lean_grpc_posix_read_raw"]
opaque readRaw (descriptor : Fd) (maximumBytes : UInt32) : IO (SysResult ByteArray)

@[extern "lean_grpc_posix_close_raw"]
opaque closeRaw (descriptor : Fd) : IO (SysResult Unit)

@[extern "lean_grpc_posix_fstat_raw"]
opaque fstatRaw (descriptor : Fd) : IO (SysResult (Array UInt64))

end Native

/-! ## Lean-owned policy -/

def strerror (error : Errno) : String :=
  let message := Native.strerrorRaw error
  if message.isEmpty then "unknown error" else message

private def validCInt (value : UInt32) : Bool := value <= Constants.cIntMax

private def validateFd (descriptor : Fd) : SysResult Unit :=
  if validCInt descriptor then .ok () else .error Errno.invalidArgument

private def containsNul (value : String) : Bool :=
  value.toUTF8.data.any (fun byte => byte == 0)

private def validCString (value : String) : Bool := !containsNul value

def close (descriptor : Fd) : IO (SysResult Unit) := do
  match validateFd descriptor with
  | .error error => pure (.error error)
  | .ok () => Native.closeRaw descriptor

/-- Perform exactly one read; callers decide whether to retry `EINTR`. -/
def read (descriptor : Fd) (maximumBytes : UInt32) : IO (SysResult ByteArray) := do
  match validateFd descriptor with
  | .error error => pure (.error error)
  | .ok () => Native.readRaw descriptor maximumBytes

/-- Metadata subset consumed by bounded regular-file input validation. -/
private structure StatSnapshot where
  mode : UInt64
  linkCount : UInt64
  sizeBits : UInt64

private def decodeStat (values : Array UInt64) : SysResult StatSnapshot :=
  match values[0]?, values[1]?, values[2]? with
  | some mode, some linkCount, some sizeBits =>
      .ok { mode, linkCount, sizeBits }
  | _, _, _ => .error Errno.io

private def fstat (descriptor : Fd) : IO (SysResult StatSnapshot) := do
  match ← Native.fstatRaw descriptor with
  | .error error => pure (.error error)
  | .ok values => pure (decodeStat values)

private def isRegular (stat : StatSnapshot) : Bool :=
  stat.mode &&& Constants.fileTypeMask == Constants.regularFileType

private def closeIgnoringErrors (descriptor : Fd) : IO Unit := do
  discard <| Native.closeRaw descriptor

private def closeThenError (descriptor : Fd) (error : Errno) : IO (SysResult α) := do
  closeIgnoringErrors descriptor
  pure (.error error)

private def readableFollowingFileFlags : Int32 :=
  Constants.oRdonly ||| Constants.oNonblock ||| Constants.oCloexec

/--
Open a bounded ordinary file by pathname while following the selected path's
symlink, then validate the opened descriptor with `fstat`.  This narrow
variant exists for system-selected files such as platform trust bundles,
whose stable public path is commonly a symlink.  Callers receive only a
regular, linked, size-bounded descriptor with close-on-exec set, together
with the observed initial size; every rejected open path consumes the
descriptor before its error is published.
-/
def openBoundedRegularInputPathFollowAllowEmpty
    (path : String) (maximumBytes : UInt64) :
    IO (SysResult (Fd × UInt64)) := do
  if !validCString path || maximumBytes == 0 ||
      maximumBytes > Constants.signedInt64Max then
    pure (.error Errno.invalidArgument)
  else
    match ← Native.openRaw path readableFollowingFileFlags 0 with
    | .error error => pure (.error error)
    | .ok descriptor =>
        match ← fstat descriptor with
        | .error error => closeThenError descriptor error
        | .ok stat =>
            if isRegular stat && stat.linkCount > 0 &&
                stat.sizeBits <= maximumBytes then
              pure (.ok (descriptor, stat.sizeBits))
            else
              closeThenError descriptor Errno.permissionDenied

end Grpc.Posix
