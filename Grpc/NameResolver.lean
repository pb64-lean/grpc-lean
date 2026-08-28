module

public import Grpc.Endpoint
public import Http2.NameResolver

public section

/-!
# gRPC endpoint resolution

Resolution applies the generic host policy to a parsed gRPC endpoint. Refined
IP literals bypass DNS, while named hosts preserve the resolver's bounded,
ordered, canonical address behavior.
-/

namespace Grpc.NameResolver

def resolveWith
    (lookup : _root_.Http2.NameResolver.Lookup) (endpoint : Endpoint) :
    IO (Except _root_.Http2.NameResolver.Error
      (Array _root_.Http2.NameResolver.Address)) :=
  match endpoint.host with
  | .ipv4 address =>
      pure (.ok #[_root_.Http2.NameResolver.Address.ofIP
        (.v4 address) endpoint.effectivePort])
  | .ipv6 address =>
      pure (.ok #[_root_.Http2.NameResolver.Address.ofIP
        (.v6 address) endpoint.effectivePort])
  | .name name =>
      _root_.Http2.NameResolver.resolveHostWith lookup name.val endpoint.effectivePort

def resolveWithAsync
    (lookup : _root_.Http2.NameResolver.AsyncLookup) (endpoint : Endpoint) :
    Std.Async.Async (Except _root_.Http2.NameResolver.Error
      (Array _root_.Http2.NameResolver.Address)) :=
  match endpoint.host with
  | .ipv4 address =>
      pure (.ok #[_root_.Http2.NameResolver.Address.ofIP
        (.v4 address) endpoint.effectivePort])
  | .ipv6 address =>
      pure (.ok #[_root_.Http2.NameResolver.Address.ofIP
        (.v6 address) endpoint.effectivePort])
  | .name name =>
      _root_.Http2.NameResolver.resolveHostWithAsync lookup name.val endpoint.effectivePort

def resolveAsync (endpoint : Endpoint)
    (cancellation? : Option Std.CancellationToken := none) :
    Std.Async.Async (Except _root_.Http2.NameResolver.Error
      (Array _root_.Http2.NameResolver.Address)) :=
  match endpoint.host with
  | .ipv4 address =>
      pure (.ok #[_root_.Http2.NameResolver.Address.ofIP
        (.v4 address) endpoint.effectivePort])
  | .ipv6 address =>
      pure (.ok #[_root_.Http2.NameResolver.Address.ofIP
        (.v6 address) endpoint.effectivePort])
  | .name name =>
      _root_.Http2.NameResolver.resolveHostAsync
        name.val endpoint.effectivePort cancellation?

def resolve (endpoint : Endpoint) :
    IO (Except _root_.Http2.NameResolver.Error
      (Array _root_.Http2.NameResolver.Address)) :=
  Std.Async.Async.block (resolveAsync endpoint)

end Grpc.NameResolver
