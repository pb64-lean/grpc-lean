module

public import Std.Async.DNS

public section

/-!
# Narrow DNS adapter

This is the entire effectful name-resolution boundary. Input validation and
error wrapping happen in Lean, and the pinned standard library owns the libuv
`getaddrinfo` adapter. The result is deliberately reduced to numeric address
strings so policy and deduplication remain in Lean.
-/

namespace Grpc.Dns

inductive Error where
  | embeddedNul
  | resolver (error : IO.Error)

namespace Error

def render : Error → String
  | .embeddedNul => "DNS hostname contains NUL"
  | .resolver error => s!"DNS resolution failed: {error}"

end Error

instance : ToString Error := ⟨Error.render⟩

private def containsNul (value : String) : Bool :=
  value.toList.any (· == Char.ofNat 0)

/--
Perform exactly one standard-library `getaddrinfo` operation.

The port is supplied as the numeric service so the platform applies the same
socket-address filtering as the eventual connector. `IO.Error` is retained
unchanged in `Error.resolver`.
-/
def getAddrInfo
    (host : String) (port : UInt16) :
    IO (Except Error (Array String)) := do
  if containsNul host then
    pure (.error .embeddedNul)
  else
    try
      let addresses ←
        (Std.Async.DNS.getAddrInfo host (toString port.toNat)).block
      pure (.ok (addresses.map toString))
    catch error =>
      pure (.error (.resolver error))

end Grpc.Dns
