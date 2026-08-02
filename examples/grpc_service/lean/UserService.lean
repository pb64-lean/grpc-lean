import Grpc
import GrpcServiceExample.user_service
import Handlers

namespace UserService

private abbrev ProofEnvelope := _root_.«userservice».«ProofEnvelope»
private abbrev GetUserWithEmailMatchesResponse :=
  _root_.«userservice».«GetUserWithEmailMatchesResponse»

/-! ## UserService implementation

The PostgreSQL repository is still implemented through C++ FFI, but the gRPC
server surface is pure Lean: generated protobuf records are constructed in
Lean and registered through the generated pure-Lean service bindings.
-/

def emailMatchPropSource (queriedId returnedId : UInt64) : String :=
  s!"(({returnedId} : UInt64) = ({queriedId} : UInt64))"

def emailMatchProofSource (returnedId : UInt64) : String :=
  s!"(@Eq.refl UInt64 ({returnedId} : UInt64))"

def liftRepository (action : IO α) : Grpc.GrpcM α :=
  ExceptT.mk do
    try
      pure (.ok (← action))
    catch e =>
      pure (.error (Grpc.Status.ofIOError e))

def getUserWithEmailMatches (userId : UInt64) :
    IO GetUserWithEmailMatchesResponse := do
  let resp ← Handlers.userRepositoryGetUserWithEmailMatches userId
  if resp.found then
    match resp.user with
    | some user =>
        let envelope : ProofEnvelope := {
          proof_term := emailMatchProofSource user.id
          prop_term := emailMatchPropSource userId user.id
        }
        pure { resp with proof := some envelope }
    | none => pure resp
  else
    pure resp

def service : _root_.«userservice».«UserService» := {
  handleCreateUser := fun req =>
    liftRepository <| Handlers.userRepositoryCreateUser req.username req.email

  handleGetUser := fun req =>
    liftRepository <| Handlers.userRepositoryGetUser req.user_id

  handleUpdateUser := fun req =>
    liftRepository <|
      Handlers.userRepositoryUpdateUser req.user_id req.username req.email req.status

  handleDeleteUser := fun req =>
    liftRepository <| Handlers.userRepositoryDeleteUser req.user_id

  handleListUsers := fun req =>
    liftRepository <|
      Handlers.userRepositoryListUsers req.limit req.offset req.status_filter

  handleGetUserWithEmailMatches := fun req =>
    liftRepository <| getUserWithEmailMatches req.user_id
}

end UserService
