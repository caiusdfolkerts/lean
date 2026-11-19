module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
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
def signatureMasksBlock0003 : Nat := ((certNat% 0))
def signatureMasksBlock0004 : Nat := ((certNat% 1))
cert_signatureMasksBlock_5 0005 2
end Papers.RationalityTen.RootedCaches.RootedSixBase04
