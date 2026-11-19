module
prelude
public meta import CertificateNumbers
public import HexNatLiteral
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badMasksBlock0040 : Nat := (certNat% 0)
def badMasksBlock0041 : Nat := 0x0

end Papers.RationalityTen.RootedCaches.RootedSixBase00
