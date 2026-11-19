module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure025GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure025
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,136,137,138,139,140,141,151,152,153,154,155,156,157,158,159,160,161,162,172,173,174,175,176,177]
def kindSupport3_003 : List Nat := [178,179,180,181,182,183,190,191,192,193,194,195,202,203,204,205,206,207,214,215,216,217,218,219,229,230,231,232,233,234,235,236]
def kindSupport3_004 : List Nat := [237,238,239,240,250,251,252,253,254,255,256,257,258,259,260,261,268,269,270,271,272,273,280,281,282,283,284,285,292,293,294,295]
def kindSupport3_005 : List Nat := [296,297,307,308,309,310,311,312,313,314,315,316,317,318,325,326,327,328,329,330,337,338,339,340,341,342,349,350,351,352,353,354]
def kindSupport3_006 : List Nat := [364,365,366,367,368,369,370,371,372,373,374,375,385,386,387,388,389,390,391,392,393,394,395,396,403,404,405,406,407,408,415,416]
def kindSupport3_007 : List Nat := [417,418,419,420,427,428,429,430,431,432,442,443,444,445,446,447,448,449,450,451,452,453,463,464,465,466,467,468,469,470,471,472]
cert_kindSupport 3 473 474 484 485 486 487 488 489 490 491 492 493 494 495
cert_kindSupport_code 3
cert_kindSupport_rest_2 3 000 0
cert_kindSupport_rest_2 3 001 288
cert_kindSupport_rest_2 3 002 576
cert_kindSupport_rest_2 3 003 864
cert_kindSupport_rest_2 3 004 1152
cert_kindSupport_rest_2 3 005 1440
cert_kindSupport_rest_2 3 006 1728
cert_kindSupport_rest_2 3 007 2016
cert_kindSupport_rest_2 3 008 2304
cert_kindSupport_rest_2 3 009 2430
cert_kindSupport_suffix_2 3 009
cert_kindSupport_suffix_3 3 008 009
cert_kindSupport_suffix_3 3 007 008
cert_kindSupport_suffix_3 3 006 007
cert_kindSupport_suffix_3 3 005 006
cert_kindSupport_suffix_3 3 004 005
cert_kindSupport_suffix_3 3 003 004
cert_kindSupport_suffix_3 3 002 003
cert_kindSupport_suffix_3 3 001 002
cert_kindSupport_suffix_3 3 000 001
cert_kindSupport_source 3 9 270
end Papers.RationalityTen.RootedCaches.RootedSevenPure025
