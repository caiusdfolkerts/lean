module
prelude
public meta import CertificateNumbers
import HexNatLiteral
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badMasksBlock0000 : Nat := (certNat% 0)
def badMasksBlock0001 : Nat := (certNat% 1)
def badMasksBlock0002 : Nat := (certNat% 2)
def badMasksBlock0003 : Nat := (certNat% 3)

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
