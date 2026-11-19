module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import CertificateNumbers
public import RootedSevenMixed030GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed030
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,46,47,48,49,50,51,52,53,54,55,56,57,64,65]
def kindSupport3_001 : List Nat := [66,67,68,69,76,77,78,79,80,81,88,89,90,91,92,93,103,104,105,106,107,108,109,110,111,112,113,114,124,125,126,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,142,143,144,145,146,147,154,155,156,157,158,159,166,167,168,169,170,171,181,182,183,184,185,186]
def kindSupport3_003 : List Nat := [187,188,189,190,191,192,202,203,204,205,206,207,208,209,210,211,212,213,220,221,222,223,224,225,232,233,234,235,236,237,244,245]
def kindSupport3_004 : List Nat := [246,247,248,249,259,260,261,262,263,264,265,266,267,268,269,270,277,278,279,280,281,282,289,290,291,292,293,294,301,302,303,304]
def kindSupport3_005 : List Nat := [305,306,316,317,318,319,320,321,322,323,324,325,326,327,334,335,336,337,338,339,346,347,348,349,350,351,358,359,360,361,362,363]
def kindSupport3_006 : List Nat := [373,374,375,376,377,378,379,380,381,382,383,384,394,395,396,397,398,399,400,401,402,403,404,405,415,416,417,418,419,420,421,422]
def kindSupport3_007 : List Nat := [423,424,425,426,433,434,435,436,437,438,445,446,447,448,449,450,457,458,459,460,461,462,472,473,474,475,476,477,478,479,480,481]
def kindSupport3_008 : List Nat := [482,483,493,494,495,496,497,498,499,500,501,502,503,504,514,515,516,517,518,519,520,521,522,523,524,525]
def kindSupport3_code : Nat := (certNat% 0)
cert_kindSupport_rest 000 0
cert_kindSupport_rest 001 320
cert_kindSupport_rest 002 640
cert_kindSupport_rest 003 960
cert_kindSupport_rest 004 1280
cert_kindSupport_rest 005 1600
cert_kindSupport_rest 006 1920
cert_kindSupport_rest 007 2240
cert_kindSupport_rest 008 2560
cert_kindSupport_rest 009 2820
def kindSupport3_suffix_009 : List Nat := []
cert_kindSupport_suffix 008 009
cert_kindSupport_suffix 007 008
cert_kindSupport_suffix 006 007
cert_kindSupport_suffix 005 006
cert_kindSupport_suffix 004 005
cert_kindSupport_suffix 003 004
cert_kindSupport_suffix 002 003
cert_kindSupport_suffix 001 002
cert_kindSupport_suffix 000 001
theorem kindSupport3_source : kindRows 3 =
    (PackedRawNatGrowth.readList 10 282 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenMixed030
