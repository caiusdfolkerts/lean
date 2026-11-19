module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure013GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure013
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_decode_3 3 008 10 32 009
cert_kindSupport_mask_3 3 008 0
cert_kindSupport_checked_5 3 008
cert_kindSupport_decode_3 3 009 10 27 010
cert_kindSupport_mask_3 3 009 1
cert_kindSupport_checked_4 3 009
end Papers.RationalityTen.RootedCaches.RootedSevenPure013
