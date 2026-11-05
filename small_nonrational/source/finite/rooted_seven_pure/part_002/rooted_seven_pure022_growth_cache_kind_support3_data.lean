module
prelude
public import RootedSevenPure022GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure022
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,136,137,138,139,140,141,151,152,153,154,155,156,157,158,159,160,161,162,172,173,174,175,176,177]
def kindSupport3_003 : List Nat := [178,179,180,181,182,183,190,191,192,193,194,195,202,203,204,205,206,207,214,215,216,217,218,219,229,230,231,232,233,234,235,236]
def kindSupport3_004 : List Nat := [237,238,239,240,247,248,249,250,251,252,259,260,261,262,263,264,271,272,273,274,275,276,286,287,288,289,290,291,292,293,294,295]
def kindSupport3_005 : List Nat := [296,297,307,308,309,310,311,312,313,314,315,316,317,318,325,326,327,328,329,330,337,338,339,340,341,342,349,350,351,352,353,354]
def kindSupport3_006 : List Nat := [364,365,366,367,368,369,370,371,372,373,374,375,385,386,387,388,389,390,391,392,393,394,395,396,403,404,405,406,407,408,415,416]
def kindSupport3_007 : List Nat := [417,418,419,420,427,428,429,430,431,432,442,443,444,445,446,447,448,449,450,451,452,453,463,464,465,466,467,468,469,470,471,472]
def kindSupport3_008 : List Nat := [473,474,484,485,486,487,488,489,490,491,492,493,494,495]
def kindSupport3_code : Nat := 0x3dfeef6fb3d7eaf4fa3cfe6f2f93b5d9ec75fadd5ea74fa5d1e873f8bc4e1f0b83c0dfefb7bbcddeeb61afd76b759abd268f45a1d067f3197cb6572993c662f1589c461f0d85c260f0581bbddaeb74b9dcae370b7dbadb6cb1586c15faf576ad55aa54ea551a55269147a35167d3d9e4ee75399c4de6d359a4ce532893c9a4b2491c8a43208fc7a291389446210f8441e0d058240df8fb7d3e5f0f7783bddced763add4e97439dcce56db69b2d86bb599ece66b3196ca61b0982c05faf96eb65aad166b258ac15eae56ab144a15027d3c9d4e26d34994c25d1a8c45a29128843a190a8441a0902803f9d4e873391c4e06f371b4d86b35180be5e2e970b65429948a250279208e4622910863c1d8e872381b8d86a34198c8622713094482311084401f0c05c2c150a04c180b050241007
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure022
