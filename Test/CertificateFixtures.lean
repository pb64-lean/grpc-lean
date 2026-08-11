namespace CertificateFixtures

/-!
The compact Ed25519 certificate from tls13-lean's X.509 fixtures. Keeping a
real certificate here ensures trust-boundary tests exercise DER parsing rather
than accepting Base64-valid textual armor alone.
-/

def validCertificatePem : String :=
  String.intercalate "\n" [
    "-----BEGIN CERTIFICATE-----",
    "MIIBxDCCAXagAwIBAgICEAMwBQYDK2VwMEYxCzAJBgNVBAYTAlVTMRgwFgYDVQQK",
    "DA90bHMxMy1sZWFuIHRlc3QxHTAbBgNVBAMMFGVkMjU1MTkuZXhhbXBsZS50ZXN0",
    "MCAXDTI0MDEwMTAwMDAwMFoYDzIwNTUwMTAxMDAwMDAwWjBGMQswCQYDVQQGEwJV",
    "UzEYMBYGA1UECgwPdGxzMTMtbGVhbiB0ZXN0MR0wGwYDVQQDDBRlZDI1NTE5LmV4",
    "YW1wbGUudGVzdDAqMAUGAytlcAMhAIuHlpz5E8msuh+OaVVyo4ucvZ1ucyCmkmUF",
    "ki4f0VSWo4GFMIGCMB0GA1UdDgQWBBR77lKMgNx+MPGXsBQkd3e39HGGAzAfBgNV",
    "HSMEGDAWgBR77lKMgNx+MPGXsBQkd3e39HGGAzAlBgNVHREEHjAcghRlZDI1NTE5",
    "LmV4YW1wbGUudGVzdIcEwAACNzAMBgNVHRMBAf8EAjAAMAsGA1UdDwQEAwIHgDAF",
    "BgMrZXADQQC7whcGOodTHOZ3xL4Jqef8LPofYF3E8naNhjytsBsSlBs86KEXOpG7",
    "ibzKOgq5kHJHKYIQVTi2IK7+LOHiM+4B",
    "-----END CERTIFICATE-----"
  ] ++ "\n"

def wellArmoredInvalidDer : String :=
  "-----BEGIN CERTIFICATE-----\nAQID\n-----END CERTIFICATE-----\n"

end CertificateFixtures
