module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport776_000 : List Nat := [26,50,90,96,99,100,248,249,250,251,258,259,475,476,477,480,481,486,487,492,494,496,497,498,501,502,507,508,513,515,757,758]
def ridgeSupport776_001 : List Nat := [761,762,765,766,812,813,814,817,818,823,824,829,831,833,834,835,838,839,844,845,850,852,1289,1290,1291,1292,1293,1294,1341,1345,1346,1347]
def ridgeSupport776_002 : List Nat := [1348,1350,1351,1358,1360,1362,1366,1367,1368,1369,1371,1372,1379,1381,1425,1429,1430,1431,1432,1434,1435,1442,1444,1446,1450,1451,1452,1453,1455,1456,1463,1465]
def ridgeSupport776_003 : List Nat := [1467,1468,1472,1473,1474,1475,1477,1478,1486,1488,1489,1491,2240,2242,2244,2246,2262,2263,2268,2269,2274,2276,2280,2282,2302,2303,2308,2309,2310,2311,2316,2317]
def ridgeSupport776_004 : List Nat := [2336,2338,2342,2344,2350,2351,2356,2357,2358,2359,2361,2362,2372,2374,2376,2378,2394,2395,2400,2401,2406,2408,2412,2414,2434,2435,2440,2441,2442,2443,2448,2449]
def ridgeSupport776_005 : List Nat := [2468,2470,2474,2476,2482,2483,2488,2489,2490,2491,2493,2494,2610,2611,2618,2620,2622,2623,2630,2632,2646,2647,2658,2659,2664,2665,2672,2674,2676,2677,2684,2686]
def ridgeSupport776_006 : List Nat := [2700,2701,2712,2713,2864,2866,2868,2870,2890,2891,2896,2897,2898,2899,2904,2905,2910,2912,2916,2918,2924,2926,2930,2932,2938,2939,2944,2945,2946,2947,2952,2953]
def ridgeSupport776_007 : List Nat := [2977,2978,2980,2981,3002,3003,3500,3502,3504,3506,3526,3527,3532,3533,3534,3535,3540,3541,3546,3548,3552,3554,3560,3562,3566,3568,3574,3575,3580,3581,3582,3583]
def ridgeSupport776_008 : List Nat := [3588,3589,3613,3614,3616,3617,3728,3730,3732,3733,3750,3751,3758,3760,3768,3769,3777,3779,3782,3784,3786,3787,3804,3805,3812,3814,3822,3823,3831,3833,4304,4306]
def ridgeSupport776_009 : List Nat := [4308,4309,4316,4318,4320,4321,4329,4331,4335,4337,4358,4360,4362,4363,4370,4372,4374,4375,4383,4385,4389,4391,4460,4462,4464,4466,4472,4474,4476,4478,4494,4495]
def ridgeSupport776_010 : List Nat := [4500,4501,4521,4523,4525,4527,4581,4583,4585,4587,4604,4606,4610,4612,4665,4667,4671,4673,4830,4831,4866,4867,4972,4973,5128,5129]
def ridgeSupport776_code : Nat := 0x28134089b6cdb260730296fcb7a48323f91dc8e64092028ff47f23d71e98f3c79635f1ad8d5c6a632b1948c7c63a2fd17c8bd45e22e51708b745b224f125890c47e22f11688a444a21710a884441a1e30ef875c3a61c30e086f43721ab0d48694341df2ef7777bbb9dccee476ebb71d96eca7643b19d86ec175cbae1d60eae753ba99d2ae947493a41c42e2070f3875c0ae046ffb7f9bfadfc6fbb7d9be0dee6f537a1bc4de06ee3769baadd46e7b739b9adcc6e3b719b64db06d736b1776bba5d2ae91744ba15c4ae21706b825c0ae016f6b7a5ba2dc96dcb6c5b32d916c0b5e5acad616a6b525a8ad41696b4a59b2cd1664b3054caa6151aa8c53f29f14eaa7453929c14d2a68531a9894aea56524291947ea3e51e28e9466a324df26f53769ba4dca6e13669b24d626a934c9a44c8a64131698a4c4a6213069824b725b12d09664b0a5812b695a4a5252128c94449d24e526e93649aa4d125e92e4942499244920486a43120e906482a4111fe8fe47523a11c88e246ea3711ae8d646323111848c02e99744ba05ce2e31714b865c22e09700b785bb2dc96dcb605af2d696b0b565aa2d31690b4459b2cd1660b2e5962ca9644aca5632ae156cab25582ab9558aa45502a7151ca8c5442a19508a8253d2871434a1850b28514246a83521a68d3068e3461a18d0868233f19e8ce066e3321988cb865a32c17f0bf45f42f917b0bd44062010fe07ec3ec1f50f907c43e01ee0f6079c3cc1e10f007743b81db08184081f60fa07c83e00c8063030016806401a
def ridgeSupport776_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport776_code
def ridgeSupport776_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport776_code
def ridgeSupport776_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport776_code
def ridgeSupport776_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport776_code
def ridgeSupport776_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport776_code
def ridgeSupport776_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport776_code
def ridgeSupport776_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport776_code
def ridgeSupport776_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport776_code
def ridgeSupport776_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport776_code
def ridgeSupport776_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport776_code
def ridgeSupport776_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport776_code
def ridgeSupport776_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport776_code
def ridgeSupport776_suffix_011 : List Nat := []
def ridgeSupport776_suffix_010 : List Nat := ridgeSupport776_010 ++ ridgeSupport776_suffix_011
def ridgeSupport776_suffix_009 : List Nat := ridgeSupport776_009 ++ ridgeSupport776_suffix_010
def ridgeSupport776_suffix_008 : List Nat := ridgeSupport776_008 ++ ridgeSupport776_suffix_009
def ridgeSupport776_suffix_007 : List Nat := ridgeSupport776_007 ++ ridgeSupport776_suffix_008
def ridgeSupport776_suffix_006 : List Nat := ridgeSupport776_006 ++ ridgeSupport776_suffix_007
def ridgeSupport776_suffix_005 : List Nat := ridgeSupport776_005 ++ ridgeSupport776_suffix_006
def ridgeSupport776_suffix_004 : List Nat := ridgeSupport776_004 ++ ridgeSupport776_suffix_005
def ridgeSupport776_suffix_003 : List Nat := ridgeSupport776_003 ++ ridgeSupport776_suffix_004
def ridgeSupport776_suffix_002 : List Nat := ridgeSupport776_002 ++ ridgeSupport776_suffix_003
def ridgeSupport776_suffix_001 : List Nat := ridgeSupport776_001 ++ ridgeSupport776_suffix_002
def ridgeSupport776_suffix_000 : List Nat := ridgeSupport776_000 ++ ridgeSupport776_suffix_001
theorem ridgeSupport776_source : candidateSupports 776 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport776_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
