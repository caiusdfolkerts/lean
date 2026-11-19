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
cert_badMasksBlock_11 0031 0
cert_badMasksBlock_9 0032
cert_badMasksBlock_11 0033 1
cert_badMasksBlock_11 0034 2
def badMasksBlock0035 : Nat := (certNat% 3)

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
