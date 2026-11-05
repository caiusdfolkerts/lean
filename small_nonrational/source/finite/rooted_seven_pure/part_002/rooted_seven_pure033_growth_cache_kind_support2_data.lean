module
prelude
public import RootedSevenPure033GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure033
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [83,84,85,86,87,88,95,96,97,98,99,100,107,108,109,110,111,112,119,120,121,122,123,124,131,132,133,134,135,136,143,144]
def kindSupport2_001 : List Nat := [145,146,147,148,155,156,157,158,159,160,161,162,163,176,177,178,179,180,181,188,189,190,191,192,193,200,201,202,203,204,205,212]
def kindSupport2_002 : List Nat := [213,214,215,216,217,218,219,220,233,234,235,236,237,238,245,246,247,248,249,250,257,258,259,260,261,262,269,270,271,272,273,274]
def kindSupport2_003 : List Nat := [275,276,277,290,291,292,293,294,295,296,297,298,311,312,313,314,315,316,323,324,325,326,327,328,335,336,337,338,339,340,347,348]
def kindSupport2_004 : List Nat := [349,350,351,352,353,354,355,368,369,370,371,372,373,380,381,382,383,384,385,392,393,394,395,396,397,404,405,406,407,408,409,410]
def kindSupport2_005 : List Nat := [411,412,425,426,427,428,429,430,431,432,433,446,447,448,449,450,451,458,459,460,461,462,463,470,471,472,473,474,475,482,483,484]
def kindSupport2_006 : List Nat := [485,486,487,488,489,490,503,504,505,506,507,508,515,516,517,518,519,520,527,528,529,530,531,532,539,540,541,542,543,544,545,546]
def kindSupport2_007 : List Nat := [547,560,561,562,563,564,565,566,567,568,581,582,583,584,585,586,593,594,595,596,597,598,605,606,607,608,609,610,617,618,619,620]
def kindSupport2_008 : List Nat := [621,622,623,624,625,638,639,640,641,642,643,650,651,652,653,654,655,662,663,664,665,666,667,674,675,676,677,678,679,680,681,682]
def kindSupport2_009 : List Nat := [695,696,697,698,699,700,701,702,703,716,717,718,719,720,721,722,723,724,737,738,739,740,741,742,743,744,745]
def kindSupport2_code : Nat := 0x2e9ba2e7b9ae5b92e3b8ae1b52d3b4ad1b42cfb3acdb32bfafabdaf2bbaeab9ae2b7aaaa9aa2a7a9aa5a92a3a8a9ba6a99a6297a5a8fa3a8da328ba2a83a0a81a027f9fa719c26f9ba6d9b26b9aa6998a619825f97a5d95a559525394a5192a499224791a458e2378da358d2338ca318c22388a218821f87a1d8721b8521384a118420f8220781a05812037f1fb7e9f97e1f77a9e97a1e7799e5791e3789db769d9761d7759cf739cd731cb729c3709c1701bf6f9b16c1af6b9ad6b1ab6a9a96719b6699966197659956518d6318b62989621816017f5f97d5f1755d1735c9715c163589615815f5795d5715b55153549515414f5214751945511434f13b4e9394e1374a9294a12749925491234891545113449114410f4390d4190541103409013e8f93e0f73d8f53b8ed3b0eb3a8e9370db368d9360d7358d5350cd330cb328c9320c1300bf2f8bd2f0b52d0b32c8b12c0a3288a12809f2789d2709b25093248912408f2208721885210831f07b1e8791e0771c06f1b86d1b06b19063188611805f160571585515053
def kindSupport2_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport2_code
def kindSupport2_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport2_code
def kindSupport2_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport2_code
def kindSupport2_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport2_code
def kindSupport2_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport2_code
def kindSupport2_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport2_code
def kindSupport2_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport2_code
def kindSupport2_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport2_code
def kindSupport2_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport2_code
def kindSupport2_rest_009 : Nat := PackedRawNatGrowth.drop 2880 kindSupport2_code
def kindSupport2_rest_010 : Nat := PackedRawNatGrowth.drop 3150 kindSupport2_code
def kindSupport2_suffix_010 : List Nat := []
def kindSupport2_suffix_009 : List Nat := kindSupport2_009 ++ kindSupport2_suffix_010
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
    (PackedRawNatGrowth.readList 10 315 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure033
