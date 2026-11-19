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
cert_badMasksBlock_11 0021 0
cert_badMasksBlock_11 0022 1
cert_badMasksBlock_9 0023
cert_badMasksBlock_9 0024
cert_badMasksBlock_9 0025
cert_badMasksBlock_11 0026 2
cert_badMasksBlock_9 0027
cert_badMasksBlock_11 0028 3
cert_badMasksBlock_9 0029
def badMasksBlock0030 : Nat := (certNat% 4)

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
