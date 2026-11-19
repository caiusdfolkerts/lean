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
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed025
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badMasksBlock_2 0000 0
cert_badMasksBlock_2 0001 1
cert_badMasksBlock_2 0002 2
cert_badMasksBlock_2 0003 3
cert_badMasksBlock_2 0004 4
cert_badMasksBlock_2 0005 5
cert_badMasksBlock_2 0006 6
def badMasksBlock0007 : Nat := (certNat% 7)

end Papers.RationalityTen.RootedCaches.RootedSevenMixed025
