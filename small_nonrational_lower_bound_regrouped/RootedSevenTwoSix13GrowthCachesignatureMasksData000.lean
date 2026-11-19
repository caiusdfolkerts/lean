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
def signatureMasksBlock0000 : Nat := (certNat% 0)
def signatureMasksBlock0001 : Nat := (certNat% 1)
def signatureMasksBlock0002 : Nat := (certNat% 2)
def signatureMasksBlock0003 : Nat := (certNat% 3)

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
