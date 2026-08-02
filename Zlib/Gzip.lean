module

public section

namespace Zlib.Gzip

/-- Compress `data` into gzip format (RFC 1952). -/
@[extern "grpc_zlib_gzip_compress"]
opaque compress (data : ByteArray) : ByteArray

/-- Decompress gzip-format `data`. Returns `none` on corrupt input or if the
inflated size would exceed `maxLen` (decompression-bomb guard). -/
@[extern "grpc_zlib_gzip_decompress"]
opaque decompress (data : ByteArray) (maxLen : UInt32) : Option ByteArray

end Zlib.Gzip
