module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
public import RootedSixBase01GrowthCacheRidgeSupport840Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_decode_2 840 008 14 32 009
cert_ridgeSupport_mask_2 840 008 0
cert_ridgeSupport_checked_3 840 008
cert_ridgeSupport_decode_2 840 009 14 32 010
cert_ridgeSupport_mask_2 840 009 1
cert_ridgeSupport_checked_3 840 009
cert_ridgeSupport_decode_2 840 010 14 32 011
cert_ridgeSupport_mask_2 840 010 2
cert_ridgeSupport_checked_3 840 010
cert_ridgeSupport_decode_2 840 011 14 5 012
cert_ridgeSupport_mask_2 840 011 3
cert_ridgeSupport_checked_4 840 011
end Papers.RationalityTen.RootedCaches.RootedSixBase01
