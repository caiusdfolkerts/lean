module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public meta import CertificateNumbers
import HexNatLiteral
public import SignatureCompatibility
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def signatureMasksBlock0000 : Nat := ((certNat% 0))
def signatureMasksBlock0001 : Nat := ((certNat% 1))
cert_signatureMasksBlock_5 0002 2
end Papers.RationalityTen.RootedCaches.RootedSixBase04
