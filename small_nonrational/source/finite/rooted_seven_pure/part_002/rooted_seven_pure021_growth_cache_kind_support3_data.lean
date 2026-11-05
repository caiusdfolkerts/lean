module
prelude
public import RootedSevenPure021GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure021
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [80,81,82,83,84,85,92,93,94,95,96,97,104,105,106,107,108,109,110,111,112,122,123,124,125,126,127,128,129,130,131,132]
def kindSupport3_001 : List Nat := [133,140,141,142,143,144,145,152,153,154,155,156,157,164,165,166,167,168,169,179,180,181,182,183,184,185,186,187,188,189,190,200]
def kindSupport3_002 : List Nat := [201,202,203,204,205,206,207,208,209,210,211,218,219,220,221,222,223,230,231,232,233,234,235,242,243,244,245,246,247,257,258,259]
def kindSupport3_003 : List Nat := [260,261,262,263,264,265,266,267,268,275,276,277,278,279,280,287,288,289,290,291,292,299,300,301,302,303,304,314,315,316,317,318]
def kindSupport3_004 : List Nat := [319,320,321,322,323,324,325,335,336,337,338,339,340,341,342,343,344,345,346,353,354,355,356,357,358,365,366,367,368,369,370,377]
def kindSupport3_005 : List Nat := [378,379,380,381,382,389,390,391,392,393,394,401,402,403,404,405,406,413,414,415,416,417,418,428,429,430,431,432,433,434,435,436]
def kindSupport3_006 : List Nat := [437,438,439,446,447,448,449,450,451,458,459,460,461,462,463,470,471,472,473,474,475,485,486,487,488,489,490,491,492,493,494,495]
def kindSupport3_007 : List Nat := [496,506,507,508,509,510,511,512,513,514,515,516,517,527,528,529,530,531,532,533,534,535,536,537,538,545,546,547,548,549,550,557]
def kindSupport3_008 : List Nat := [558,559,560,561,562,569,570,571,572,573,574,584,585,586,587,588,589,590,591,592,593,594,595,605,606,607,608,609,610,611,612,613]
def kindSupport3_009 : List Nat := [614,615,616,626,627,628,629,630,631,632,633,634,635,636,637,647,648,649,650,651,652,653,654,655,656,657,658]
def kindSupport3_code : Nat := 0x292a4690a3e8ea368ca2e8aa2688a1e7d9f27b9ea799e2779da759d2739ca6899e669966498e629866097e5e9765394a519424f93a4d9324b92a499223e8f63c8ee3a8e6328c6308be2e8b6268962488e228861a8661885e168561484e128461083e058120380a01801ff7f9fd7f1fb7e9f07bdee7b5ec7adea7a5e879de6795db769d9761d7759cf739cd731cb729c3709c1701bf6f9b76d9b56d1b36c9b16c1af6b9ad6b1a2685a067d9e675966559464d926458a6258861d866157e5f57c5ed7a5e5725c5705bd6e5b5665956458d625855a5655855d565555454d525455053d4551143509415013f4f93d4f13b4e9304bd2e4b52c4ad2448d224852047d1845d164551444d0c42d0a4250841d064150440d02404f73d8f53d0f33c8eb3a8e93a0e7398df378dd370db368d3348d1340cf338cd330cb328c9320be2f4bc2ecba2e4b82dcb62d4b42cca92a0a7298a52909d2709b26899260912408f2388d2308521083208812007f1f87d1f07b1e8701bc6e1b46c1ac6a1a4681846017c5e1745c1545414c5214450
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure021
