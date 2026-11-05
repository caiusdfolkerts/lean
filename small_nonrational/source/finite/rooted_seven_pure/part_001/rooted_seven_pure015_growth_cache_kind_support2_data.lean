module
prelude
public import RootedSevenPure015GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure015
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [74,75,76,77,78,79,86,87,88,89,90,91,98,99,100,101,102,103,113,114,115,116,117,118,119,120,121,134,135,136,137,138]
def kindSupport2_001 : List Nat := [139,146,147,148,149,150,151,158,159,160,161,162,163,170,171,172,173,174,175,176,177,178,191,192,193,194,195,196,197,198,199,212]
def kindSupport2_002 : List Nat := [213,214,215,216,217,224,225,226,227,228,229,236,237,238,239,240,241,248,249,250,251,252,253,254,255,256,269,270,271,272,273,274]
def kindSupport2_003 : List Nat := [281,282,283,284,285,286,293,294,295,296,297,298,305,306,307,308,309,310,311,312,313,326,327,328,329,330,331,332,333,334,347,348]
def kindSupport2_004 : List Nat := [349,350,351,352,359,360,361,362,363,364,371,372,373,374,375,376,383,384,385,386,387,388,389,390,391,404,405,406,407,408,409,410]
def kindSupport2_005 : List Nat := [411,412,425,426,427,428,429,430,437,438,439,440,441,442,449,450,451,452,453,454,461,462,463,464,465,466,467,468,469,482,483,484]
def kindSupport2_006 : List Nat := [485,486,487,494,495,496,497,498,499,506,507,508,509,510,511,518,519,520,521,522,523,524,525,526,539,540,541,542,543,544,545,546]
def kindSupport2_007 : List Nat := [547,560,561,562,563,564,565,572,573,574,575,576,577,584,585,586,587,588,589,596,597,598,599,600,601,602,603,604,617,618,619,620]
def kindSupport2_008 : List Nat := [621,622,623,624,625,638,639,640,641,642,643,644,645,646]
def kindSupport2_code : Nat := 0xa1a85a1283a0a81a027f9fa719c26f9ba6d9b26b9aa699725b96a599625795a559524d9324b92a49922419023f8fa3d8f2358d2338ca318c22388a218821f87a1d8721b83a0d8320b82a0982207819ff7f9fd7f1fb7e9f37c9f17c1ef7b9e7799e5791e3789d5751d3749d1741cf739cd719c5711c3709c16e9b96e1b76d9b56b9ad6b1ab6a9a96719b669996619765995651876198561183609816017f5e1775d9755d1735b16b5a9695a1675815f5795d5715b5394d5314b5294952147519394e1374d9354d1334c9314a9294a127499254791d4711b46919449114410f4390d400ff3f8fd3f0fb3e8f93e0f13c0ef3b8ed3b0e5390e3388e1380d9360d7358d5350c7318c5310c3308c1300bf2c8b12c0af2b8ad2b0ab2a8a3288a12809f2789725895250932488b2288922087218791e0771d8751d0731c87119c661946418c6216c5a1645815c5613c4e1344c12c4a
def kindSupport2_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport2_code
def kindSupport2_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport2_code
def kindSupport2_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport2_code
def kindSupport2_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport2_code
def kindSupport2_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport2_code
def kindSupport2_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport2_code
def kindSupport2_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport2_code
def kindSupport2_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport2_code
def kindSupport2_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport2_code
def kindSupport2_rest_009 : Nat := PackedRawNatGrowth.drop 2700 kindSupport2_code
def kindSupport2_suffix_009 : List Nat := []
def kindSupport2_suffix_008 : List Nat := kindSupport2_008 ++ kindSupport2_suffix_009
def kindSupport2_suffix_007 : List Nat := kindSupport2_007 ++ kindSupport2_suffix_008
def kindSupport2_suffix_006 : List Nat := kindSupport2_006 ++ kindSupport2_suffix_007
def kindSupport2_suffix_005 : List Nat := kindSupport2_005 ++ kindSupport2_suffix_006
def kindSupport2_suffix_004 : List Nat := kindSupport2_004 ++ kindSupport2_suffix_005
def kindSupport2_suffix_003 : List Nat := kindSupport2_003 ++ kindSupport2_suffix_004
def kindSupport2_suffix_002 : List Nat := kindSupport2_002 ++ kindSupport2_suffix_003
def kindSupport2_suffix_001 : List Nat := kindSupport2_001 ++ kindSupport2_suffix_002
def kindSupport2_suffix_000 : List Nat := kindSupport2_000 ++ kindSupport2_suffix_001
theorem kindSupport2_source : kindRows 2 =
    (PackedRawNatGrowth.readList 10 270 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure015
