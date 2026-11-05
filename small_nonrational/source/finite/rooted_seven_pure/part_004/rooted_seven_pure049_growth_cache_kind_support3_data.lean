module
prelude
public import RootedSevenPure049GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure049
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,136,137,138,145,146,147,148,149,150,157,158,159,160,161,162,169,170,171,172,173,174,184,185,186]
def kindSupport3_003 : List Nat := [187,188,189,190,191,192,193,194,195,205,206,207,208,209,210,211,212,213,214,215,216,223,224,225,226,227,228,235,236,237,238,239]
def kindSupport3_004 : List Nat := [240,247,248,249,250,251,252,262,263,264,265,266,267,268,269,270,271,272,273,280,281,282,283,284,285,292,293,294,295,296,297,304]
def kindSupport3_005 : List Nat := [305,306,307,308,309,319,320,321,322,323,324,325,326,327,328,329,330,337,338,339,340,341,342,349,350,351,352,353,354,361,362,363]
def kindSupport3_006 : List Nat := [364,365,366,376,377,378,379,380,381,382,383,384,385,386,387,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,421,422]
def kindSupport3_007 : List Nat := [423,424,425,426,427,428,429,430,431,432,442,443,444,445,446,447,448,449,450,451,452,453,463,464,465,466,467,468,469,470,471,472]
def kindSupport3_008 : List Nat := [473,474,484,485,486,487,488,489,490,491,492,493,494,495]
def kindSupport3_code : Nat := 0x3dfeef6fb3d7eaf4fa3cfe6f2f93b5d9ec75fadd5ea74fa5d1e873f8bc4e1f0b83c0dfefb7bbcddeeb61afd76b759abd56a751a7d3697379acce632f96cae532792c8e431f8ec6e0f0581c05fefd7dbe5eef579bc5badb6cb5daad362b0d82bf5eaed5aab54a9d4aa34aa4d228f46a2d128742a0d027f359a4ce6531984a6512793496491d8e46e35198c446210f87436190b854261107833f1f6fa7cbe1eef077bb9daec75b91c6e270b81bed86bb59aad469b49a2d067b399ac36130580bf5f2f578bb5d2e570ae56ab156aa54a8942a04fa793a964aa51269248a29128843a190a8441a0902803f9d4e873391c4e06f371b4d86b35180be5e2e970b65429948a250279208e4622910863c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b050241007
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 288 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 576 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 864 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1152 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1440 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 1728 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2016 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 2304 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 2430 kindSupport3_code
def kindSupport3_suffix_009 : List Nat := []
def kindSupport3_suffix_008 : List Nat := kindSupport3_008 ++ kindSupport3_suffix_009
def kindSupport3_suffix_007 : List Nat := kindSupport3_007 ++ kindSupport3_suffix_008
def kindSupport3_suffix_006 : List Nat := kindSupport3_006 ++ kindSupport3_suffix_007
def kindSupport3_suffix_005 : List Nat := kindSupport3_005 ++ kindSupport3_suffix_006
def kindSupport3_suffix_004 : List Nat := kindSupport3_004 ++ kindSupport3_suffix_005
def kindSupport3_suffix_003 : List Nat := kindSupport3_003 ++ kindSupport3_suffix_004
def kindSupport3_suffix_002 : List Nat := kindSupport3_002 ++ kindSupport3_suffix_003
def kindSupport3_suffix_001 : List Nat := kindSupport3_001 ++ kindSupport3_suffix_002
def kindSupport3_suffix_000 : List Nat := kindSupport3_000 ++ kindSupport3_suffix_001
theorem kindSupport3_source : kindRows 3 =
    (PackedRawNatGrowth.readList 9 270 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure049
