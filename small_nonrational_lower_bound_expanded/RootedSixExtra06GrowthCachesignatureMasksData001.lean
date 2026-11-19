module
prelude
public meta import CertificateNumbers
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def signatureMasksBlock0003 : Nat := (certNat% 0)
def signatureMasksBlock0004 : Nat := (certNat% 1)
def signatureMasksBlock0005 : Nat := (certNat% 2)

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
