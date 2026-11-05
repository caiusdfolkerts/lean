module
prelude
public import RootedSevenPure010GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure010
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [1,2,3,4,5,6,13,14,15,16,17,18,25,26,27,28,29,30,40,41,42,43,44,45,46,47,48,61,62,63,64,65]
def kindSupport2_001 : List Nat := [66,73,74,75,76,77,78,85,86,87,88,89,90,97,98,99,100,101,102,103,104,105,118,119,120,121,122,123,124,125,126,139]
def kindSupport2_002 : List Nat := [140,141,142,143,144,151,152,153,154,155,156,163,164,165,166,167,168,175,176,177,178,179,180,181,182,183,196,197,198,199,200,201]
def kindSupport2_003 : List Nat := [208,209,210,211,212,213,220,221,222,223,224,225,232,233,234,235,236,237,238,239,240,253,254,255,256,257,258,259,260,261,274,275]
def kindSupport2_004 : List Nat := [276,277,278,279,286,287,288,289,290,291,298,299,300,301,302,303,310,311,312,313,314,315,316,317,318,331,332,333,334,335,336,343]
def kindSupport2_005 : List Nat := [344,345,346,347,348,355,356,357,358,359,360,367,368,369,370,371,372,373,374,375,388,389,390,391,392,393,394,395,396,409,410,411]
def kindSupport2_006 : List Nat := [412,413,414,421,422,423,424,425,426,433,434,435,436,437,438,445,446,447,448,449,450,451,452,453,466,467,468,469,470,471,472,473]
def kindSupport2_007 : List Nat := [474,487,488,489,490,491,492,499,500,501,502,503,504,511,512,513,514,515,516,523,524,525,526,527,528,529,530,531,544,545,546,547]
def kindSupport2_008 : List Nat := [548,549,550,551,552,565,566,567,568,569,570,571,572,573]
def kindSupport2_code : Nat := 0x8f63c8ee3a8e6388de368d62889e268962488e228862084e128461083e0e8360c82e0480e02806007fdf87ddf67d5f47cdec7adea7a5e879dda765d875dd6755d474dd2715c470dc2705c06fdbe6f5b66d5b46cdb26c5aa6a5a869da66959e6759c66d9a6658c62d8a6258861d86615845dd765d5745cd725c5705bd6859d665956458d5c56d5a5655855d5053d4e5354c52d3e4f53c4ed3a4e5384dd364bd2e4b52c4ad2a48d224852047d1e45d164551444d124150440d02405003fcfe3f4f03bcee3b4ec3acea3a4e8384e037cde374dc354d434cd2344d0324c831cc6314c42dcb62d4b42ccb22c4b02bca829ca6294a428c9c26c9a2649825c9023c8e2348c22c7e1f47c1ec7a1e4781dc761a46819c661946418c621845a1645815c561544e1344c12c4a12442104400fc3e0f4300bc2e0b42c0ac2a0a4280781d0701b06819048110400f0380d018050100300801
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure010
