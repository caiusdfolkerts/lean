module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public meta import CertificateNumbers
public import RootedSevenMixed026GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed026
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,136,137,138,139,140,141,151,152,153,154,155,156,157,158,159,160,161,162,169,170,171,172,173,174]
def kindSupport3_003 : List Nat := [181,182,183,184,185,186,193,194,195,196,197,198,208,209,210,211,212,213,214,215,216,217,218,219,229,230,231,232,233,234,235,236]
def kindSupport3_004 : List Nat := [237,238,239,240,247,248,249,250,251,252,259,260,261,262,263,264,271,272,273,274,275,276,286,287,288,289,290,291,292,293,294,295]
def kindSupport3_005 : List Nat := [296,297,307,308,309,310,311,312,313,314,315,316,317,318,325,326,327,328,329,330,337,338,339,340,341,342,349,350,351,352,353,354]
def kindSupport3_006 : List Nat := [364,365,366,367,368,369,370,371,372,373,374,375,382,383,384,385,386,387,394,395,396,397,398,399,406,407,408,409,410,411,421,422]
def kindSupport3_007 : List Nat := [423,424,425,426,427,428,429,430,431,432,442,443,444,445,446,447,448,449,450,451,452,453,463,464,465,466,467,468,469,470,471,472]
def kindSupport3_008 : List Nat := [473,474,484,485,486,487,488,489,490,491,492,493,494,495]
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
cert_kindSupport_rest 009 2700
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
    (PackedRawNatGrowth.readList 10 270 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenMixed026
