module

public import GrpcStandardProto.health
public import GrpcStandardProto.reflection

public section

namespace Grpc
namespace Services

namespace Health

/-- The standard `grpc.health.v1.Health` schema for server reflection. -/
def fileDescriptors : Array Reflection.FileDescriptor :=
  _root_.GrpcStandardProto.FileDescriptors.health_files

end Health

namespace Reflection

/-- The standard stable-v1 server-reflection schema. -/
def v1FileDescriptors : Array FileDescriptor :=
  _root_.GrpcStandardProto.FileDescriptors.reflection_files

end Reflection

end Services
end Grpc
