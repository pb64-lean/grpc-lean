import EmailAnalyticsService
import Grpc
import GrpcServiceExample.analytics_service
import GrpcServiceExample.user_service
import UserService

namespace GrpcServiceExample

def registry : Grpc.Registry :=
  Grpc.Services.Reflection.register <|
    _root_.«emailanalytics».«EmailAnalytics».register
      (_root_.«userservice».«UserService».register Grpc.Registry.empty UserService.service)
      EmailAnalyticsService.service

def portFromArgs (args : List String) : UInt16 :=
  match args with
  | port :: _ => UInt16.ofNat (port.toNat?.getD 50051)
  | [] => 50051

end GrpcServiceExample

def main (args : List String) : IO Unit := do
  let port := GrpcServiceExample.portFromArgs args
  let server ← Grpc.Server.serve GrpcServiceExample.registry {
    address := Grpc.Server.anyIPv4 port
  }
  IO.println s!"Lean grpc_service server listening on {server.localAddress}"
  (← IO.getStdout).flush
  Grpc.Server.wait server
