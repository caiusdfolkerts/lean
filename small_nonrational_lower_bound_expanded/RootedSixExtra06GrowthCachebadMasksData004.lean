module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badMasksBlock_11 0012 0
cert_badMasksBlock_11 0013 1
def badMasksBlock0014 : Nat := (certNat% 2)

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
