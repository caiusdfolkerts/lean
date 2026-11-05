module
prelude
public import RootedSevenPure001GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure001
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [89,90,91,92,93,94,101,102,103,104,105,106,113,114,115,116,117,118,125,126,127,128,129,130,137,138,139,140,141,142,149,150]
def kindSupport3_001 : List Nat := [151,152,153,154,164,165,166,167,168,169,170,171,172,173,174,175,182,183,184,185,186,187,194,195,196,197,198,199,206,207,208,209]
def kindSupport3_002 : List Nat := [210,211,221,222,223,224,225,226,227,228,229,230,231,232,242,243,244,245,246,247,248,249,250,251,252,253,260,261,262,263,264,265]
def kindSupport3_003 : List Nat := [272,273,274,275,276,277,284,285,286,287,288,289,299,300,301,302,303,304,305,306,307,308,309,310,317,318,319,320,321,322,329,330]
def kindSupport3_004 : List Nat := [331,332,333,334,341,342,343,344,345,346,356,357,358,359,360,361,362,363,364,365,366,367,377,378,379,380,381,382,383,384,385,386]
def kindSupport3_005 : List Nat := [387,388,395,396,397,398,399,400,407,408,409,410,411,412,419,420,421,422,423,424,434,435,436,437,438,439,440,441,442,443,444,445]
def kindSupport3_006 : List Nat := [452,453,454,455,456,457,464,465,466,467,468,469,476,477,478,479,480,481,491,492,493,494,495,496,497,498,499,500,501,502,509,510]
def kindSupport3_007 : List Nat := [511,512,513,514,521,522,523,524,525,526,533,534,535,536,537,538,548,549,550,551,552,553,554,555,556,557,558,559,569,570,571,572]
def kindSupport3_008 : List Nat := [573,574,575,576,577,578,579,580,587,588,589,590,591,592,599,600,601,602,603,604,611,612,613,614,615,616,626,627,628,629,630,631]
def kindSupport3_009 : List Nat := [632,633,634,635,636,637,644,645,646,647,648,649,656,657,658,659,660,661,668,669,670,671,672,673,683,684,685,686,687,688,689,690]
def kindSupport3_010 : List Nat := [691,692,693,694,704,705,706,707,708,709,710,711,712,713,714,715,725,726,727,728,729,730,731,732,733,734,735,736,746,747,748,749]
def kindSupport3_011 : List Nat := [750,751,752,753,754,755,756,757]
def kindSupport3_code : Nat := 0xbd6f4bcef2bc6f0bbeeebb6ecbaeeab82dfb7addb72dbb6ad9b62d7b5ad5b2ecab26c8b1ec6b16c4b0ec2b06c0adab5ad2b3acab1ac2afabaadab2aba86a0a7e9ea769ca5694a4e92a4690a2688a1e86a16849f67c9ee7a9e6789de769d6749ce729a26799a65992639725b96a59962579424f93a4d9324b9124390a419023f8fa3d8f23b8ea398be2e8b62c8ae2a8a62889e268962486a198621785a1583a0d8320b82a0980a01801ff7f9fd7d9f57d1f37c9f17c1ef7b9ed7b1eb785e077dde775dc755d474dd2745d0725c871dc6715c46f5bc6edba6e5b86ddb66d5b46cdb26a1a7699a5691a36719b66999661976418f6398d6318b61183609816017f5f97d5f17b5e9795bd6e5b56c5ad6a5a56859d66595645695956157559555394d5314b52949509415013f4f93d4d9354d1334c9314c12f4b92d4b12b4852047d1e4751c4551444d12445104250841d06415043f4fc3ecfa3e4f83dcf63d4f43ccf23a0e7398e5390e3388e1380df378dd34cd2344d033cce31cc6314c430cc22ecba2e4b82dcb62bcae2b4ac2acaa2a4a829ca6294a42689926097258952388d2308b22889208812007f1f87d1d8751d0731c8711a8691a067198651785d1705b16859
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
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 3200 kindSupport3_code
def kindSupport3_rest_011 : Nat := PackedRawNatGrowth.drop 3520 kindSupport3_code
def kindSupport3_rest_012 : Nat := PackedRawNatGrowth.drop 3600 kindSupport3_code
def kindSupport3_suffix_012 : List Nat := []
def kindSupport3_suffix_011 : List Nat := kindSupport3_011 ++ kindSupport3_suffix_012
def kindSupport3_suffix_010 : List Nat := kindSupport3_010 ++ kindSupport3_suffix_011
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
    (PackedRawNatGrowth.readList 10 360 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure001
