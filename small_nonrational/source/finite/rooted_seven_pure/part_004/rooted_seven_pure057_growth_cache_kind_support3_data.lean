module
prelude
public import RootedSevenPure057GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure057
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [71,72,73,74,75,76,83,84,85,86,87,88,95,96,97,98,99,100,101,102,103,113,114,115,116,117,118,119,120,121,122,123]
def kindSupport3_001 : List Nat := [124,131,132,133,134,135,136,143,144,145,146,147,148,155,156,157,158,159,160,170,171,172,173,174,175,176,177,178,179,180,181,191]
def kindSupport3_002 : List Nat := [192,193,194,195,196,197,198,199,200,201,202,203,204,205,215,216,217,218,219,220,221,222,223,224,225,226,233,234,235,236,237,238]
def kindSupport3_003 : List Nat := [245,246,247,248,249,250,257,258,259,260,261,262,272,273,274,275,276,277,278,279,280,281,282,283,293,294,295,296,297,298,299,300]
def kindSupport3_004 : List Nat := [301,302,303,304,311,312,313,314,315,316,323,324,325,326,327,328,335,336,337,338,339,340,350,351,352,353,354,355,356,357,358,359]
def kindSupport3_005 : List Nat := [360,361,371,372,373,374,375,376,377,378,379,380,381,382,389,390,391,392,393,394,401,402,403,404,405,406,413,414,415,416,417,418]
def kindSupport3_006 : List Nat := [428,429,430,431,432,433,434,435,436,437,438,439,449,450,451,452,453,454,455,456,457,458,459,460,467,468,469,470,471,472,479,480]
def kindSupport3_007 : List Nat := [481,482,483,484,491,492,493,494,495,496,506,507,508,509,510,511,512,513,514,515,516,517,527,528,529,530,531,532,533,534,535,536]
def kindSupport3_008 : List Nat := [537,538,548,549,550,551,552,553,554,555,556,557,558,559]
def kindSupport3_code : Nat := 0x8be2e8b62c8ae2a8a62889e268962486a198621785a158521384a118420f8160480e02806007fdfe7f5fc7edfa7c1ef7b9ed7b1eb791e3789e1781df761d7759d5751d3731cb729c9721c7719c5711c3709c16ddb66d5b46cdb26c5b06bdae6b5ac689a16819f6799d6599565193649916298962187619855f97d5f17b5e9795e1775d9755d1735a56859d665956458d625856057d5e55153549515414f5214751945511434f13b4e9394e1374c12f4b92d4b12b4a9294a1274992546d1a4651845d164551444d12445104190541103409013e8f93e0f73d8f53b8ed3b0eb3a8e9388e1380df378dd370db368d9360d7334cc32cca324c831cc6314c430cc2304c02fcb52d0b32c8b12c0af2b8ad2b0ab2a8a027c9e2749c26c9424c922449023c8821c862148420c7c1ec7a1e4781dc761d4741cc721c4671986519063188611805f1605715855150531304b1284912047
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 2700 kindSupport3_code
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
    (PackedRawNatGrowth.readList 10 270 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure057
