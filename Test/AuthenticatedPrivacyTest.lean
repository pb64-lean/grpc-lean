import Grpc

namespace Test.AuthenticatedPrivacy

/--
error: Unknown constant `Grpc.Authenticated.mk`
-/
#guard_msgs(error) in
#check Grpc.Authenticated.mk

/--
error: invalid {...} notation, constructor for `Grpc.Authenticated` is marked as private
-/
#guard_msgs(error) in
example : Grpc.Authenticated Nat := { value := 1 }

/--
error: invalid {...} notation, constructor for `Grpc.Authenticated` is marked as private
-/
#guard_msgs(error) in
example (authenticated : Grpc.Authenticated Nat) : Grpc.Authenticated Nat :=
  { authenticated with value := 2 }

end Test.AuthenticatedPrivacy

def main : IO Unit := pure ()
