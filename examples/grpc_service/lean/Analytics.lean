import GrpcServiceExample.analytics_service
import GrpcServiceExample.user_service
import ProofTransport
import UserService

namespace Analytics

private abbrev VerifyResponse := _root_.«emailanalytics».«VerifyResponse»

private def expectedPropSource (queriedId returnedId : UInt64) : String :=
  s!"(({returnedId} : UInt64) = ({queriedId} : UInt64))"

def verifyUserEmailGroup (userId : UInt64) : IO VerifyResponse := do
  let resp ← UserService.getUserWithEmailMatches userId
  if !resp.found then
    throw (IO.userError s!"UserService returned not-found for user {userId}")

  let some user := resp.user
    | throw (IO.userError "UserService response was found but omitted user")
  let some proof := resp.proof
    | throw (IO.userError "UserService response omitted proof envelope")

  let expectedProp := expectedPropSource userId user.id
  IO.eprintln s!"[Analytics] queried user {userId}, UserService returned id={user.id}"
  IO.eprintln s!"[Analytics]   shipped proof: {proof.proof_term}"
  IO.eprintln s!"[Analytics]   shipped prop:  {proof.prop_term}"
  IO.eprintln s!"[Analytics]   local expected prop: {expectedProp}"

  let verified ← ProofTransport.verifyProof proof.proof_term expectedProp
  if verified then
    IO.eprintln s!"[Analytics] VERIFIED: kernel accepted the proof"
    pure {}
  else
    throw (IO.userError "proof verification failed")

end Analytics
