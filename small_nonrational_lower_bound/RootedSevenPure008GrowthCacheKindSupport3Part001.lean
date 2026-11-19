module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure008GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure008
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_decode_3 3 008 10 32 009
cert_kindSupport_mask_3 3 008 0
cert_kindSupport_checked_5 3 008
cert_kindSupport_decode_3 3 009 10 32 010
cert_kindSupport_mask_3 3 009 1
cert_kindSupport_checked_5 3 009
cert_kindSupport_decode_3 3 010 10 32 011
cert_kindSupport_mask_3 3 010 2
cert_kindSupport_checked_5 3 010
cert_kindSupport_decode_3 3 011 10 8 012
cert_kindSupport_mask_3 3 011 3
cert_kindSupport_checked_4 3 011
end Papers.RationalityTen.RootedCaches.RootedSevenPure008
