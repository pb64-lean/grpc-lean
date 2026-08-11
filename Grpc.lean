module

public import Grpc.CallCredentials
public import Grpc.Cancellation
public import Grpc.Client
public import Grpc.Endpoint
public import Grpc.Framing
public import Grpc.Http2
public import Grpc.Metadata
public import Grpc.Protocol
public import Grpc.Server
public import Grpc.Services.Health
public import Grpc.Services.Reflection
public import Grpc.Status

public section

namespace Grpc
namespace Server

abbrev Config := Http2.Server.Config
abbrev Instance := Http2.Server.Server

def ipv4Address (a b c d : UInt8) (port : UInt16) : Std.Net.SocketAddress :=
  Http2.Server.ipv4Address a b c d port

def loopback (port : UInt16) : Std.Net.SocketAddress :=
  Http2.Server.loopback port

def anyIPv4 (port : UInt16) : Std.Net.SocketAddress :=
  Http2.Server.anyIPv4 port

def bind (config : Config := {}) : IO Instance :=
  Http2.Server.bind config

def serveClientWithState (registry : Registry) (config : Config)
    (client : Std.Async.TCP.Socket.Client) (state : Http2.Connection.State := {}) :
    Std.Async.Async Http2.Connection.State :=
  Http2.Server.serveClientWithState registry config client state

def serveClient (registry : Registry) (config : Config)
    (client : Std.Async.TCP.Socket.Client) : Std.Async.Async Unit :=
  Http2.Server.serveClient registry config client

def acceptOne (server : Instance) (registry : Registry) : Std.Async.Async Unit :=
  Http2.Server.acceptOne server registry

partial def serveForever (server : Instance) (registry : Registry) : Std.Async.Async Unit :=
  Http2.Server.serveForever server registry

def serve (registry : Registry) (config : Config := {}) : IO Instance :=
  Http2.Server.serve registry config

/-- Static TLS server identity/policy (certificate chain + Ed25519 signing key). -/
abbrev TlsConfig := Http2.Server.TlsConfig

/-- Serve gRPC over TLS 1.3 (ALPN "h2"). -/
def serveTls (registry : Registry) (tlsConfig : TlsConfig) (config : Config := {}) :
    IO Instance :=
  Http2.Server.serveTls registry tlsConfig config

def shutdown (server : Instance) : IO Unit :=
  Http2.Server.shutdown server

/-- Wait for graceful drain. After `shutdown`, a finite timeout is followed by
bounded exact-owner cleanup; pass `none` only when an intentionally unbounded
post-shutdown drain is desired. Before `shutdown`, this is intentionally the
serving process's unbounded blocking join. -/
def wait (server : Instance) (drainTimeoutMs : Option Nat := some 30000) : IO Unit :=
  Http2.Server.wait server drainTimeoutMs

def isShutdown (server : Instance) : IO Bool :=
  Http2.Server.isShutdown server

/-- `some err` once the accept loop has died; `none` while it is alive.  A dead accept
loop otherwise shows up only as clients hanging on connect. -/
def acceptFailure? (server : Instance) : IO (Option IO.Error) :=
  Http2.Server.acceptFailure? server

/-- Still accepting connections?  Throws the accept loop's error if it died. -/
def checkAccepting (server : Instance) : IO Bool :=
  Http2.Server.checkAccepting server

/-- Why the most recently finished connections finished. -/
def closedConnections (server : Instance) : IO (Array Http2.Server.ClosedConnection) :=
  Http2.Server.closedConnectionRecords server

end Server
end Grpc
