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
cert_candidateMasksBlock_9 0008 0
cert_candidateMasksBlock_9 0009 1
cert_candidateMasksBlock_9 0010 2
def candidateMasksBlock0011 : Nat := (certNat% 3)

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
