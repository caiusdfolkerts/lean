module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure009GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure009
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_decode_3 2 008 10 32 009
cert_kindSupport_mask_3 2 008 0
cert_kindSupport_checked_5 2 008
cert_kindSupport_decode_3 2 009 10 27 010
cert_kindSupport_mask_3 2 009 1
cert_kindSupport_checked_4 2 009
end Papers.RationalityTen.RootedCaches.RootedSevenPure009
