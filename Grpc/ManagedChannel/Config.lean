module

public import Grpc.CallCredentials
public import Grpc.Endpoint

public section

/-!
# Managed-channel configuration

The refined settings handed to the single shared outbound-channel owner: the
parsed endpoint, per-call credentials, a positive relative RPC deadline
bounded by gRPC's eight-digit timeout wire representation, and the transport's
conservative per-message size caps.  The deadline is applied when each call
starts, never when a stub is built.
-/

namespace Grpc

def maxGrpcTimeoutSeconds : Nat := 99_999_999

def isValidDeadlineSeconds (seconds : Nat) : Bool :=
  0 < seconds && seconds <= maxGrpcTimeoutSeconds

/--
A positive relative deadline that fits the gRPC timeout header's eight-digit
seconds form.  It is applied when each call starts, never when a stub is built.
-/
structure RpcDeadline where
  private mk ::
  seconds : Nat
  private valid : isValidDeadlineSeconds seconds = true
deriving BEq, DecidableEq, Repr

namespace RpcDeadline

def ofSeconds? (seconds : Nat) : Option RpcDeadline :=
  if valid : isValidDeadlineSeconds seconds = true then
    some (.mk seconds valid)
  else
    none

def default : RpcDeadline :=
  .mk 10 (by decide)

def grpcTimeoutValue (deadline : RpcDeadline) : String :=
  toString deadline.seconds ++ "S"

theorem positive (deadline : RpcDeadline) : 0 < deadline.seconds := by
  have valid :
      0 < deadline.seconds ∧
        deadline.seconds <= maxGrpcTimeoutSeconds := by
    simpa only [isValidDeadlineSeconds, Bool.and_eq_true, decide_eq_true_eq]
      using deadline.valid
  exact valid.1

theorem bounded (deadline : RpcDeadline) :
    deadline.seconds <= maxGrpcTimeoutSeconds := by
  have valid :
      0 < deadline.seconds ∧
        deadline.seconds <= maxGrpcTimeoutSeconds := by
    simpa only [isValidDeadlineSeconds, Bool.and_eq_true, decide_eq_true_eq]
      using deadline.valid
  exact valid.2

end RpcDeadline

/--
Default cap for one encoded request or decoded response message, matching the
conservative gRPC transport default of four mebibytes.
-/
def defaultMaxMessageBytes : Nat := 4 * 1024 * 1024

/--
Refined settings handed to the single shared outbound-channel owner.  The
default is a fresh ten-second relative deadline for each RPC, anonymous
credentials, and the transport's conservative message-size caps.
-/
structure ManagedChannel.Config where
  endpoint : Endpoint
  credentials : CallCredentials := .anonymous
  deadline : RpcDeadline := .default
  /-- Maximum uncompressed bytes accepted for one outbound request message. -/
  maxSendMessageBytes : Nat := defaultMaxMessageBytes
  /-- Maximum bytes accepted for one inbound response message. -/
  maxReceiveMessageBytes : Nat := defaultMaxMessageBytes
deriving Repr

end Grpc
