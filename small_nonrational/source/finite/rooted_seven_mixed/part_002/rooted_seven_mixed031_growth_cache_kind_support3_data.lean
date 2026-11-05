module
prelude
public import RootedSevenMixed031GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed031
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,46,47,48,49,50,51,52,53,54,55,56,57,64,65]
def kindSupport3_001 : List Nat := [66,67,68,69,76,77,78,79,80,81,88,89,90,91,92,93,103,104,105,106,107,108,109,110,111,112,113,114,124,125,126,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,142,143,144,145,146,147,154,155,156,157,158,159,166,167,168,169,170,171,181,182,183,184,185,186]
def kindSupport3_003 : List Nat := [187,188,189,190,191,192,202,203,204,205,206,207,208,209,210,211,212,213,220,221,222,223,224,225,232,233,234,235,236,237,244,245]
def kindSupport3_004 : List Nat := [246,247,248,249,259,260,261,262,263,264,265,266,267,268,269,270,277,278,279,280,281,282,289,290,291,292,293,294,301,302,303,304]
def kindSupport3_005 : List Nat := [305,306,316,317,318,319,320,321,322,323,324,325,326,327,337,338,339,340,341,342,343,344,345,346,347,348,355,356,357,358,359,360]
def kindSupport3_006 : List Nat := [367,368,369,370,371,372,379,380,381,382,383,384,394,395,396,397,398,399,400,401,402,403,404,405,415,416,417,418,419,420,421,422]
def kindSupport3_007 : List Nat := [423,424,425,426,433,434,435,436,437,438,445,446,447,448,449,450,457,458,459,460,461,462,472,473,474,475,476,477,478,479,480,481]
def kindSupport3_008 : List Nat := [482,483,493,494,495,496,497,498,499,500,501,502,503,504,514,515,516,517,518,519,520,521,522,523,524,525]
def kindSupport3_code : Nat := 0x8360c82e0a8260881e068160480e027e1f77d9f57d1f37c9f17c1ef7b9ed78de2785e077dde775dc76dda765d8739cd731cb729c9709c1701bf6f9bd6d9b56d1b36c9b16a9a96a1a7699a5691a3689a16819f6559464d926459063d8e6358c62d8a6017f5f97d5f17b5d1735c9715c16f5a16759965591635715b569595615755955551535495151d465154450d42505404fd3e4f53c4c9314c12f4b92d4992549123489214691946117459154390d4310b429094210741905411033e4f83dcf63d4f43b4ec3acea3a4e8384e037cde374dc354d434cd2344d033cce334cc32cca300bf2f8bd2f0bb2e8b92e0b72d8b52acaa2a4a829ca627c9e2749c26c9a24c922449023c8e21c862148420c82204801fc7e1f47c1c8711c06f1b86d1b06b1a8691a0671745c16c5a164581445013c4e1344c1144410c42104400e4380dc360d4340cc320c4300bc2e09023088210801f0601705815050130300b0280902007
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 2820 kindSupport3_code
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
    (PackedRawNatGrowth.readList 10 282 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
