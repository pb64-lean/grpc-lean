import GrpcServiceExample.user_service
import Protobuf.Base64

namespace Handlers

private abbrev Status := _root_.«userservice».«Status»
private abbrev User := _root_.«userservice».«User»
private abbrev ProofEnvelope := _root_.«userservice».«ProofEnvelope»
private abbrev CreateUserResponse := _root_.«userservice».«CreateUserResponse»
private abbrev GetUserResponse := _root_.«userservice».«GetUserResponse»
private abbrev GetUserWithEmailMatchesResponse :=
  _root_.«userservice».«GetUserWithEmailMatchesResponse»
private abbrev UpdateUserResponse := _root_.«userservice».«UpdateUserResponse»
private abbrev DeleteUserResponse := _root_.«userservice».«DeleteUserResponse»
private abbrev ListUsersResponse := _root_.«userservice».«ListUsersResponse»

private structure DecodeState where
  tokens : List String

private abbrev DecodeM := StateT DecodeState (Except String)

@[extern "user_repository_create_user"]
private opaque userRepositoryCreateUserRaw : String -> String -> IO String

@[extern "user_repository_get_user"]
private opaque userRepositoryGetUserRaw : UInt64 -> IO String

@[extern "user_repository_get_user_with_email_matches"]
private opaque userRepositoryGetUserWithEmailMatchesRaw : UInt64 -> IO String

@[extern "user_repository_update_user"]
private opaque userRepositoryUpdateUserRaw :
  UInt64 -> Bool -> String -> Bool -> String -> Bool -> UInt32 -> IO String

@[extern "user_repository_delete_user"]
private opaque userRepositoryDeleteUserRaw : UInt64 -> IO String

@[extern "user_repository_list_users"]
private opaque userRepositoryListUsersRaw : UInt32 -> UInt32 -> Bool -> UInt32 -> IO String

private def take (label : String) : DecodeM String := do
  let state ← get
  match state.tokens with
  | [] => throw s!"missing {label}"
  | token :: rest =>
      set ({ tokens := rest } : DecodeState)
      pure token

private def takeNat (label : String) : DecodeM Nat := do
  let token ← take label
  match token.toNat? with
  | some value => pure value
  | none => throw s!"invalid {label}: {token}"

private def takeBool (label : String) : DecodeM Bool := do
  let value ← takeNat label
  if value == 0 then
    pure false
  else if value == 1 then
    pure true
  else
    throw s!"invalid {label}: expected 0 or 1, got {value}"

private def takeUInt64 (label : String) : DecodeM UInt64 := do
  pure (UInt64.ofNat (← takeNat label))

private def takeUInt32 (label : String) : DecodeM UInt32 := do
  pure (UInt32.ofNat (← takeNat label))

private def decodeStringToken (label token : String) : Except String String :=
  if token == "-" then
    pure ""
  else
    match Protobuf.Base64.decodeBase64String token with
    | .ok value => pure value
    | .error err => throw s!"invalid {label}: {err}"

private def takeString (label : String) : DecodeM String := do
  let token ← take label
  match decodeStringToken label token with
  | .ok value => pure value
  | .error err => throw err

def statusToUInt32 (status : Status) : UInt32 :=
  UInt32.ofNat (Int.toNat (Int32.toInt (_root_.«userservice».«Status».toInt32 status)))

private def statusOfUInt32 (status : UInt32) : Status :=
  _root_.«userservice».«Status».fromInt32 status.toInt32

private def emptyProof : ProofEnvelope := {
  proof_term := ""
  prop_term := ""
}

private def takeUser : DecodeM User := do
  let id ← takeUInt64 "user.id"
  let username ← takeString "user.username"
  let email ← takeString "user.email"
  let status ← takeUInt32 "user.status"
  pure {
    id := id
    username := username
    email := email
    status := statusOfUInt32 status
  }

private def takeUsers (count : Nat) : DecodeM (Array User) := do
  let mut out := #[]
  for _ in List.range count do
    out := out.push (← takeUser)
  pure out

private def tokenize (raw : String) : List String :=
  raw.splitOn " " |>.filter (fun token => !token.isEmpty)

private def runDecode (raw : String) (decoder : DecodeM α) : Except String α :=
  match decoder.run { tokens := tokenize raw } with
  | .ok (value, state) =>
      match state.tokens with
      | [] => .ok value
      | token :: _ => .error s!"unexpected trailing token {token}"
  | .error err => .error err

private def decodeRaw (operation raw : String) (decoder : DecodeM α) : IO α := do
  match runDecode raw decoder with
  | .ok value => pure value
  | .error err =>
      throw <| IO.userError s!"{operation}: invalid repository response: {err}; raw={raw}"

private def parseCreateUserResponse : DecodeM CreateUserResponse := do
  let success ← takeBool "success"
  let user ← takeUser
  let errorMessage ← takeString "error_message"
  pure {
    success := success
    user := some user
    error_message := errorMessage
  }

private def parseGetUserResponse : DecodeM GetUserResponse := do
  let found ← takeBool "found"
  let user ← takeUser
  pure {
    found := found
    user := some user
  }

private def parseGetUserWithEmailMatchesResponse :
    DecodeM GetUserWithEmailMatchesResponse := do
  let found ← takeBool "found"
  let user ← takeUser
  let count ← takeNat "email_matches.count"
  let emailMatches ← takeUsers count
  pure {
    found := found
    user := some user
    email_matches := emailMatches
    proof := some emptyProof
  }

private def parseUpdateUserResponse : DecodeM UpdateUserResponse := do
  let success ← takeBool "success"
  let user ← takeUser
  let errorMessage ← takeString "error_message"
  pure {
    success := success
    user := some user
    error_message := errorMessage
  }

private def parseDeleteUserResponse : DecodeM DeleteUserResponse := do
  let success ← takeBool "success"
  let errorMessage ← takeString "error_message"
  pure {
    success := success
    error_message := errorMessage
  }

private def parseListUsersResponse : DecodeM ListUsersResponse := do
  let totalCount ← takeUInt32 "total_count"
  let count ← takeNat "users.count"
  let users ← takeUsers count
  pure {
    users := users
    total_count := totalCount
  }

def userRepositoryCreateUser (username email : String) : IO CreateUserResponse := do
  let raw ← userRepositoryCreateUserRaw username email
  decodeRaw "CreateUser" raw parseCreateUserResponse

def userRepositoryGetUser (userId : UInt64) : IO GetUserResponse := do
  let raw ← userRepositoryGetUserRaw userId
  decodeRaw "GetUser" raw parseGetUserResponse

def userRepositoryGetUserWithEmailMatches
    (userId : UInt64) : IO GetUserWithEmailMatchesResponse := do
  let raw ← userRepositoryGetUserWithEmailMatchesRaw userId
  decodeRaw "GetUserWithEmailMatches" raw parseGetUserWithEmailMatchesResponse

def userRepositoryUpdateUser (userId : UInt64)
    (username? : Option String) (email? : Option String) (status? : Option Status) :
    IO UpdateUserResponse := do
  let username := username?.getD ""
  let email := email?.getD ""
  let status := status?.map statusToUInt32 |>.getD 0
  let raw ← userRepositoryUpdateUserRaw userId username?.isSome username
    email?.isSome email status?.isSome status
  decodeRaw "UpdateUser" raw parseUpdateUserResponse

def userRepositoryDeleteUser (userId : UInt64) : IO DeleteUserResponse := do
  let raw ← userRepositoryDeleteUserRaw userId
  decodeRaw "DeleteUser" raw parseDeleteUserResponse

def userRepositoryListUsers (limit offset : UInt32) (statusFilter? : Option Status) :
    IO ListUsersResponse := do
  let statusFilter := statusFilter?.map statusToUInt32 |>.getD 0
  let raw ← userRepositoryListUsersRaw limit offset statusFilter?.isSome statusFilter
  decodeRaw "ListUsers" raw parseListUsersResponse

end Handlers
