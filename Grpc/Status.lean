module

public section

namespace Grpc

inductive Code where
  | ok
  | cancelled
  | unknown
  | invalidArgument
  | deadlineExceeded
  | notFound
  | alreadyExists
  | permissionDenied
  | resourceExhausted
  | failedPrecondition
  | aborted
  | outOfRange
  | unimplemented
  | internal
  | unavailable
  | dataLoss
  | unauthenticated
  deriving Inhabited, Repr, DecidableEq

namespace Code

def toNat : Code -> Nat
  | .ok => 0
  | .cancelled => 1
  | .unknown => 2
  | .invalidArgument => 3
  | .deadlineExceeded => 4
  | .notFound => 5
  | .alreadyExists => 6
  | .permissionDenied => 7
  | .resourceExhausted => 8
  | .failedPrecondition => 9
  | .aborted => 10
  | .outOfRange => 11
  | .unimplemented => 12
  | .internal => 13
  | .unavailable => 14
  | .dataLoss => 15
  | .unauthenticated => 16

def ofNat? : Nat -> Option Code
  | 0 => some .ok
  | 1 => some .cancelled
  | 2 => some .unknown
  | 3 => some .invalidArgument
  | 4 => some .deadlineExceeded
  | 5 => some .notFound
  | 6 => some .alreadyExists
  | 7 => some .permissionDenied
  | 8 => some .resourceExhausted
  | 9 => some .failedPrecondition
  | 10 => some .aborted
  | 11 => some .outOfRange
  | 12 => some .unimplemented
  | 13 => some .internal
  | 14 => some .unavailable
  | 15 => some .dataLoss
  | 16 => some .unauthenticated
  | _ => none

def ofString? (s : String) : Option Code :=
  s.toNat?.bind ofNat?

def toHeaderValue (code : Code) : String :=
  toString code.toNat

def defaultMessage : Code -> String
  | .ok => "OK"
  | .cancelled => "Cancelled"
  | .unknown => "Unknown"
  | .invalidArgument => "Invalid argument"
  | .deadlineExceeded => "Deadline exceeded"
  | .notFound => "Not found"
  | .alreadyExists => "Already exists"
  | .permissionDenied => "Permission denied"
  | .resourceExhausted => "Resource exhausted"
  | .failedPrecondition => "Failed precondition"
  | .aborted => "Aborted"
  | .outOfRange => "Out of range"
  | .unimplemented => "Unimplemented"
  | .internal => "Internal"
  | .unavailable => "Unavailable"
  | .dataLoss => "Data loss"
  | .unauthenticated => "Unauthenticated"

end Code

instance : ToString Code where
  toString code := code.toHeaderValue

structure Status where
  code : Code
  message : Option String := none
  deriving Inhabited, Repr, DecidableEq

namespace Status

def ok : Status := { code := .ok }

def error (code : Code) (message : String) : Status :=
  { code := code, message := some message }

def cancelled (message : String) : Status :=
  error .cancelled message

def unknown (message : String) : Status :=
  error .unknown message

def isOk (status : Status) : Bool :=
  status.code == .ok

def messageD (status : Status) : String :=
  status.message.getD status.code.defaultMessage

def internal (message : String) : Status :=
  error .internal message

def invalidArgument (message : String) : Status :=
  error .invalidArgument message

def deadlineExceeded (message : String) : Status :=
  error .deadlineExceeded message

def resourceExhausted (message : String) : Status :=
  error .resourceExhausted message

def unimplemented (message : String) : Status :=
  error .unimplemented message

def dispatchCancelledMessage : String :=
  "gRPC stream dispatch was cancelled"

def ofIOError (err : IO.Error) : Status :=
  match err with
  | .interrupted _ _ _ => cancelled (toString err)
  | .timeExpired _ _ => deadlineExceeded (toString err)
  | .resourceExhausted _ _ _ => resourceExhausted (toString err)
  | .userError message =>
      if message == dispatchCancelledMessage then
        cancelled message
      else
        unknown (toString err)
  | _ => unknown (toString err)

end Status

abbrev GrpcM := ExceptT Status IO

namespace GrpcM

def ofExcept (result : Except Status α) : GrpcM α :=
  ExceptT.mk (pure result)

end GrpcM

end Grpc
