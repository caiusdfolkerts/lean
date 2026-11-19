module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import CertificateNumbers
public import RootedSevenMixed031GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed031
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_decode_2 000 32 001
cert_kindSupport_mask_2 000 0
cert_kindSupport_checked_3 000
cert_kindSupport_decode_2 001 32 002
cert_kindSupport_mask_2 001 1
cert_kindSupport_checked_3 001
cert_kindSupport_decode_2 002 32 003
cert_kindSupport_mask_2 002 2
cert_kindSupport_checked_3 002
cert_kindSupport_decode_2 003 32 004
cert_kindSupport_mask_2 003 3
cert_kindSupport_checked_3 003
cert_kindSupport_decode_2 004 32 005
cert_kindSupport_mask_2 004 4
cert_kindSupport_checked_3 004
cert_kindSupport_decode_2 005 32 006
cert_kindSupport_mask_2 005 5
cert_kindSupport_checked_3 005
cert_kindSupport_decode_2 006 32 007
cert_kindSupport_mask_2 006 6
cert_kindSupport_checked_3 006
cert_kindSupport_decode_2 007 32 008
cert_kindSupport_mask_2 007 7
theorem kindSupport3_007_checked :
    (kindSupport3_007.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
