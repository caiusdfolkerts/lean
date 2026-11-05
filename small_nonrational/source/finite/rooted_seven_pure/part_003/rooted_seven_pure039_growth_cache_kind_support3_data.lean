module
prelude
public import RootedSevenPure039GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure039
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [80,81,82,83,84,85,92,93,94,95,96,97,104,105,106,107,108,109,110,111,112,122,123,124,125,126,127,128,129,130,131,132]
def kindSupport3_001 : List Nat := [133,140,141,142,143,144,145,152,153,154,155,156,157,164,165,166,167,168,169,179,180,181,182,183,184,185,186,187,188,189,190,200]
def kindSupport3_002 : List Nat := [201,202,203,204,205,206,207,208,209,210,211,218,219,220,221,222,223,230,231,232,233,234,235,242,243,244,245,246,247,257,258,259]
def kindSupport3_003 : List Nat := [260,261,262,263,264,265,266,267,268,275,276,277,278,279,280,287,288,289,290,291,292,299,300,301,302,303,304,314,315,316,317,318]
def kindSupport3_004 : List Nat := [319,320,321,322,323,324,325,332,333,334,335,336,337,344,345,346,347,348,349,356,357,358,359,360,361,371,372,373,374,375,376,377]
def kindSupport3_005 : List Nat := [378,379,380,381,382,392,393,394,395,396,397,398,399,400,401,402,403,410,411,412,413,414,415,422,423,424,425,426,427,434,435,436]
def kindSupport3_006 : List Nat := [437,438,439,449,450,451,452,453,454,455,456,457,458,459,460,470,471,472,473,474,475,476,477,478,479,480,481,488,489,490,491,492]
def kindSupport3_007 : List Nat := [493,500,501,502,503,504,505,512,513,514,515,516,517,527,528,529,530,531,532,533,534,535,536,537,538,548,549,550,551,552,553,554]
def kindSupport3_008 : List Nat := [555,556,557,558,559,566,567,568,569,570,571,578,579,580,581,582,583,590,591,592,593,594,595,605,606,607,608,609,610,611,612,613]
def kindSupport3_009 : List Nat := [614,615,616,626,627,628,629,630,631,632,633,634,635,636,637,647,648,649,650,651,652,653,654,655,656,657,658]
def kindSupport3_code : Nat := 0x292a4690a3e8ea368ca2e8aa2688a1e7d9f27b9ea799e2779da759d2739ca6899e669966498e629866097e5e9765394a519424f93a4791a459124390a3b8ea398e2378da2f8ba2d8b22b8aa298a22789a258921a8661885e168561484e128461083e058120380a01801f97e1f77d9f57d1ed7b1eb7a9e97a1e1781df779dd771db769d9761d7759cc72dca725c871dc6715c470dc2705b76d9b56d1b36c9ab6a9a96a1a76999f6799d6719b66993649916418f6398d6318b629896217e5f57c5ed7a5e5785dd765d5745cd695a167599655915d5715b56959561515414f5394d5314551143509415013f4f93d4f13b4e9304bd2e4b52c4ad2448d224852047d1845d164551444d0c42d0a4250841d064150440d02404f73d8f53d0f33c8eb3a8e93a0e7398df378dd370db368d3348d1340cf338cd330cb328c9320be2f4bc2ecba2e4b82dcb62d4b42cca92a0a7298a52909d2709b26899260912408f2388d2308521083208812007f1f87d1f07b1e8701bc6e1b46c1ac6a1a4681846017c5e1745c1545414c5214450
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 2880 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 3150 kindSupport3_code
def kindSupport3_suffix_010 : List Nat := []
def kindSupport3_suffix_009 : List Nat := kindSupport3_009 ++ kindSupport3_suffix_010
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
    (PackedRawNatGrowth.readList 10 315 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure039
