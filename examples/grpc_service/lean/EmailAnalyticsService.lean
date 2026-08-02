import Analytics
import Grpc
import GrpcServiceExample.analytics_service

namespace EmailAnalyticsService

private def liftIO (action : IO α) : Grpc.GrpcM α :=
  ExceptT.mk do
    try
      pure (.ok (← action))
    catch e =>
      pure (.error (Grpc.Status.ofIOError e))

def service : _root_.«emailanalytics».«EmailAnalytics» := {
  handleVerifyUserEmailGroup := fun req =>
    liftIO <| Analytics.verifyUserEmailGroup req.user_id
}

end EmailAnalyticsService
