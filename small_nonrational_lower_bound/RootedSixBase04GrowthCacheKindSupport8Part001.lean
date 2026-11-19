module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
public import RootedSixBase04GrowthCacheKindSupport8Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_decode_4 8 008 12 32 009
cert_kindSupport_mask_4 8 008 0
cert_kindSupport_checked_7 8 008
cert_kindSupport_decode_4 8 009 12 32 010
cert_kindSupport_mask_4 8 009 1
cert_kindSupport_checked_7 8 009
cert_kindSupport_decode_4 8 010 12 16 011
cert_kindSupport_mask_4 8 010 2
cert_kindSupport_checked_6 8 010
end Papers.RationalityTen.RootedCaches.RootedSixBase04
