module
prelude
public import RootedSevenPure048GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure048
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [71,72,73,74,75,76,83,84,85,86,87,88,95,96,97,98,99,100,101,102,103,113,114,115,116,117,118,119,120,121,122,123]
def kindSupport3_001 : List Nat := [124,131,132,133,134,135,136,143,144,145,146,147,148,155,156,157,158,159,160,170,171,172,173,174,175,176,177,178,179,180,181,191]
def kindSupport3_002 : List Nat := [192,193,194,195,196,197,198,199,200,201,202,209,210,211,212,213,214,221,222,223,224,225,226,233,234,235,236,237,238,248,249,250]
def kindSupport3_003 : List Nat := [251,252,253,254,255,256,257,258,259,266,267,268,269,270,271,278,279,280,281,282,283,290,291,292,293,294,295,305,306,307,308,309]
def kindSupport3_004 : List Nat := [310,311,312,313,314,315,316,326,327,328,329,330,331,332,333,334,335,336,337,344,345,346,347,348,349,356,357,358,359,360,361,368]
def kindSupport3_005 : List Nat := [369,370,371,372,373,383,384,385,386,387,388,389,390,391,392,393,394,401,402,403,404,405,406,413,414,415,416,417,418,425,426,427]
def kindSupport3_006 : List Nat := [428,429,430,440,441,442,443,444,445,446,447,448,449,450,451,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,485,486]
def kindSupport3_007 : List Nat := [487,488,489,490,491,492,493,494,495,496,506,507,508,509,510,511,512,513,514,515,516,517,527,528,529,530,531,532,533,534,535,536]
def kindSupport3_008 : List Nat := [537,538,548,549,550,551,552,553,554,555,556,557,558,559]
def kindSupport3_code : Nat := 0x8be2e8b62c8ae2a8a62889e268962486a198621785a158521384a118420f8160480e02806007fdfe7f5fc7edfa7c1ef7b9ed7b1eb7a9e97a1e7799e576dda765d875dd6755d474dd2745d073dce735c3709c1701bf6f9bd6f1bb6e9b96e1ae6b5ac6adaa6a5a2685a067d9e675966559464d926458a6258861d866158460d82605805fd755d1735c9715c1695a167599655915d5715b56959561515414f5394d5314b52949521475193c4ed3a4e5384dd364d5344cd324c52749925491234891b46919461174590f4390d4310b4290340901400ff3f8fd3f0fb3e8f93e0ee3b4ec3acea3a4e2384e037cde374d6354d434cd2344ca324c831cc6314c430cc2304c02fcb52d0b32c8b12c0af2b8ad2b0ab2a8a027c9e2749c26c9424c922449023c8821c862148420c7c1ec7a1e4781dc761d4741cc721c4671986519063188611805f1605715855150531304b1284912047
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure048
