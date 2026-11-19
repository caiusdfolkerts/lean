module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import CertificateNumbers
public import HexNatLiteral
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed029
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badMasksBlock_2 0000 0
cert_badMasksBlock_2 0001 1
cert_badMasksBlock_2 0002 2
cert_badMasksBlock_2 0003 3
cert_badMasksBlock 0004
def badMasksBlock0005 : Nat := (certNat% 4)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed029
