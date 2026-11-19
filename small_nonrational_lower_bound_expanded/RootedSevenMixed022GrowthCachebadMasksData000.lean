module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import CertificateNumbers
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed022
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badMasksBlock_2 0000 0
cert_badMasksBlock_2 0001 1
cert_badMasksBlock_2 0002 2
cert_badMasksBlock_2 0003 3
cert_badMasksBlock_2 0004 4
cert_badMasksBlock_2 0005 5
cert_badMasksBlock 0006
cert_badMasksBlock 0007
def badMasksBlock0008 : Nat := (certNat% 6)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed022
