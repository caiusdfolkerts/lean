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
def ridgeSupport328_000 : List Nat := [22,46,86,92,97,99,200,201,202,203,210,211,432,434,436,438,440,445,446,448,451,474,475,479,481,482,486,488,489,491,709,710]
def ridgeSupport328_001 : List Nat := [713,714,717,718,769,771,773,775,777,782,783,785,788,811,812,816,818,819,823,825,826,828,1241,1242,1243,1244,1245,1246,1300,1302,1304,1305]
def ridgeSupport328_002 : List Nat := [1307,1309,1310,1314,1319,1343,1344,1345,1348,1349,1350,1352,1357,1359,1384,1386,1388,1389,1391,1393,1394,1398,1403,1427,1428,1429,1432,1433,1434,1436,1441,1443]
def ridgeSupport328_003 : List Nat := [1468,1470,1471,1473,1474,1476,1478,1479,1481,1482,1486,1487,2239,2242,2245,2249,2263,2266,2272,2273,2277,2279,2282,2283,2288,2289,2298,2299,2320,2321,2330,2331]
def ridgeSupport328_004 : List Nat := [2336,2337,2341,2343,2346,2347,2352,2357,2362,2363,2367,2369,2371,2374,2377,2381,2395,2398,2404,2405,2409,2411,2414,2415,2420,2421,2430,2431,2452,2453,2462,2463]
def ridgeSupport328_005 : List Nat := [2468,2469,2473,2475,2478,2479,2484,2489,2494,2495,2499,2501,2504,2505,2508,2513,2516,2517,2520,2525,2540,2541,2552,2553,2614,2615,2617,2619,2626,2627,2629,2631]
def ridgeSupport328_006 : List Nat := [2650,2651,2662,2663,2863,2866,2869,2873,2876,2877,2886,2887,2899,2902,2908,2909,2913,2915,2918,2919,2924,2925,2929,2931,2934,2935,2940,2945,2956,2957,2966,2967]
def ridgeSupport328_007 : List Nat := [2970,2972,2976,2977,2986,2987,3499,3502,3505,3509,3512,3513,3522,3523,3535,3538,3544,3545,3549,3551,3554,3555,3560,3561,3565,3567,3570,3571,3576,3581,3592,3593]
def ridgeSupport328_008 : List Nat := [3602,3603,3606,3608,3612,3613,3618,3623,3626,3627,3644,3645,3648,3653,3662,3663,3667,3670,3727,3729,3736,3737,3754,3755,3757,3759,3772,3773,3774,3776,4194,4199]
def ridgeSupport328_009 : List Nat := [4202,4203,4206,4211,4214,4215,4219,4222,4225,4228,4303,4305,4312,4313,4315,4317,4324,4325,4326,4328,4332,4334,4459,4462,4465,4469,4471,4474,4477,4481,4484,4485]
def ridgeSupport328_010 : List Nat := [4498,4499,4518,4523,4524,4528,4578,4583,4584,4588,4590,4595,4603,4605,4651,4654,4662,4664,4838,4839,4874,4875,4964,4965,5120,5121]
def ridgeSupport328_code : Nat := 0x28034009b2cd9261730a973cb9a47123691748ae3fb1fb8f9c7ba3d91e88f3c78a3611ac8d5c69a3271928c2c61230317d8bd45de2eb1718b745ae1dd0ec874439a1cb0e486ec36e1b30d8868c33e10908183f41ee0ef076839c1ba0d706a833c189d80ebe75ebaf1d5eead755baa9d32e98748ba3dcace53727b939c8ae4071eb8f1c56e2a713b889c3ae1c70c3859c26e12704b821bfadf86f9b7c9bdeded6f4b7a1bc6de26efb775bb2dd86e9373db86dc26dcb6e1b6adb16d736ad756baa5d0ae81738b9a5cbae5971ab8c5c0adf16eeb765b9adc56dab6c5b3ad996c6b615aead716acb535a3ad1967ab3c59cacd5664b2f533a9994b6a5a523a915486a4251da8e546ea364fca7e13da9ec4eea7613aa9d44e8a7313929c84e2a70d37e9be4dca6d135e9ae4d5a6a534a9a44cfa67932a9944bfa5f92ea9744b7a5b92d69694b2a5912bc95b4a6a52528c9434a0a4fd27693a49aa4c125692a493a49524292048da46922291047da3e91e28f0475a3a91ce8e5470a3811b48d7464a3151848bf2e79738b945c92e39718b885c22e096fcb7c5bc2d19684b3859a2cc9660b2a5942c995ecaec5722b895bcada56c2b515a0a9e54d2a41518a8a5442a09500a7e5272911478a3a51b28c9460a2c51426f13749b84db26d136467833a19c8cdc6663321980cb06563141888c3c61c3091838c146063011670b345942c91630b143d61e90f407983c41e10ef876c3b41c30e006f837a1b80db06d03641b006983481960ca06483200c606102e015805c016
def ridgeSupport328_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport328_code
def ridgeSupport328_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport328_code
def ridgeSupport328_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport328_code
def ridgeSupport328_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport328_code
def ridgeSupport328_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport328_code
def ridgeSupport328_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport328_code
def ridgeSupport328_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport328_code
def ridgeSupport328_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport328_code
def ridgeSupport328_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport328_code
def ridgeSupport328_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport328_code
def ridgeSupport328_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport328_code
def ridgeSupport328_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport328_code
def ridgeSupport328_suffix_011 : List Nat := []
def ridgeSupport328_suffix_010 : List Nat := ridgeSupport328_010 ++ ridgeSupport328_suffix_011
def ridgeSupport328_suffix_009 : List Nat := ridgeSupport328_009 ++ ridgeSupport328_suffix_010
def ridgeSupport328_suffix_008 : List Nat := ridgeSupport328_008 ++ ridgeSupport328_suffix_009
def ridgeSupport328_suffix_007 : List Nat := ridgeSupport328_007 ++ ridgeSupport328_suffix_008
def ridgeSupport328_suffix_006 : List Nat := ridgeSupport328_006 ++ ridgeSupport328_suffix_007
def ridgeSupport328_suffix_005 : List Nat := ridgeSupport328_005 ++ ridgeSupport328_suffix_006
def ridgeSupport328_suffix_004 : List Nat := ridgeSupport328_004 ++ ridgeSupport328_suffix_005
def ridgeSupport328_suffix_003 : List Nat := ridgeSupport328_003 ++ ridgeSupport328_suffix_004
def ridgeSupport328_suffix_002 : List Nat := ridgeSupport328_002 ++ ridgeSupport328_suffix_003
def ridgeSupport328_suffix_001 : List Nat := ridgeSupport328_001 ++ ridgeSupport328_suffix_002
def ridgeSupport328_suffix_000 : List Nat := ridgeSupport328_000 ++ ridgeSupport328_suffix_001
theorem ridgeSupport328_source : candidateSupports 328 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport328_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
