module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
public import RootedSixBase03GrowthCacheKindSupport8Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_decode_4 8 008 13 20 009
cert_kindSupport_mask_4 8 008 0
cert_kindSupport_checked_6 8 008
end Papers.RationalityTen.RootedCaches.RootedSixBase03
