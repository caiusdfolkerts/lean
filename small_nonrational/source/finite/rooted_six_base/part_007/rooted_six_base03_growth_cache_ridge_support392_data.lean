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
def ridgeSupport392_000 : List Nat := [24,48,88,94,97,100,224,225,226,227,234,235,433,434,435,438,439,444,445,450,452,495,496,500,502,503,507,509,510,512,733,734]
def ridgeSupport392_001 : List Nat := [737,738,741,742,770,771,772,775,776,781,782,787,789,832,833,837,839,840,844,846,847,849,1265,1266,1267,1268,1269,1270,1299,1303,1304,1305]
def ridgeSupport392_002 : List Nat := [1306,1308,1309,1316,1318,1364,1365,1366,1369,1370,1371,1373,1378,1380,1383,1387,1388,1389,1390,1392,1393,1400,1402,1448,1449,1450,1453,1454,1455,1457,1462,1464]
def ridgeSupport392_003 : List Nat := [1467,1470,1471,1472,1475,1476,1477,1479,1484,1485,1487,1488,2239,2241,2246,2248,2266,2267,2269,2272,2275,2278,2280,2281,2294,2295,2300,2301,2314,2315,2328,2329]
def ridgeSupport392_004 : List Nat := [2335,2337,2342,2343,2348,2349,2354,2356,2359,2360,2367,2368,2371,2373,2378,2380,2398,2399,2401,2404,2407,2410,2412,2413,2426,2427,2432,2433,2446,2447,2460,2461]
def ridgeSupport392_005 : List Nat := [2467,2469,2474,2475,2480,2481,2486,2488,2491,2492,2499,2500,2502,2503,2510,2512,2514,2515,2522,2524,2538,2539,2550,2551,2668,2669,2671,2673,2680,2681,2683,2685]
def ridgeSupport392_006 : List Nat := [2704,2705,2716,2717,2863,2865,2870,2872,2882,2883,2888,2889,2902,2903,2905,2908,2911,2914,2916,2917,2923,2925,2930,2931,2936,2937,2942,2944,2950,2951,2964,2965]
def ridgeSupport392_007 : List Nat := [2973,2975,2976,2978,2994,2995,3499,3501,3506,3508,3518,3519,3524,3525,3538,3539,3541,3544,3547,3550,3552,3553,3559,3561,3566,3567,3572,3573,3578,3580,3586,3587]
def ridgeSupport392_008 : List Nat := [3600,3601,3609,3611,3612,3614,3620,3622,3624,3625,3642,3643,3650,3652,3660,3661,3669,3671,3781,3783,3790,3791,3808,3809,3811,3813,3826,3827,3828,3830,4196,4198]
def ridgeSupport392_009 : List Nat := [4200,4201,4208,4210,4212,4213,4221,4223,4227,4229,4357,4359,4366,4367,4369,4371,4378,4379,4380,4382,4386,4388,4459,4461,4466,4468,4471,4473,4478,4480,4482,4483]
def ridgeSupport392_010 : List Nat := [4504,4505,4518,4520,4527,4529,4578,4580,4587,4589,4592,4594,4609,4611,4653,4655,4668,4670,4834,4835,4870,4871,4968,4969,5124,5125]
def ridgeSupport392_code : Nat := 0x280b4049b4cda260f306971cb8a47d23c917c8b64072018f947c23db1eb8f2478a3631af8d4469a3331988c1c60a30117e8bcc5de2e91728b6c5ae24912288f447223711a889c44621f10e883c41610b08383fc1f60eb07483941c20d30688334191decef4779bbc9dcaee3770bb81d9eece763bb15caee55726b931c88e4271db8e9c52e287133891c3ce1c70db865c22e10701b809bf8dfa6fab7d1bdedee6f4b79dbc2de06ef376dbb0dd56e9b749b8adc46dfb6f9b68db26d6b6ad766bb25d12e8173eb9d5caae5170eb865c02df96f2b785b9adc96dab6b5b2ad916c4b5f5ae2d656aeb565a4ad21686b4259c2cd9662b2f54eaa71522a9053ea9ed4f2a78538a9bd4daa6c4fba7d93d69ea4ee27693a69d24e8273938e9c64e2270d3789bb4dc26d93629b04d5a6a934a9a34cea67131e98e4c0a6012f697a4b6a5b12d49674b225852be95e4a6252928a9434a024fd27093749a24c925a92c493a49924291f48ca46121690a47ea3f11ee8f6474a3a11cc8e347023751b68da46423191828bf2e8173cb9a5cc2e39714b885c32e016fcb7c5bb2dc16d8b625af2d716b4b545a92d415e8af05712b815b8ada56c2b5959cac85622ae956cab45592ab1554aa85262921474a3851a28c9460a2e51327b13d49e84f327913c46a234f1a70d306903471a28d046803151898c3861a3081838c106063021730b945c42e116f0b744001fe0fe87ec3ee1f60fa07c03de1c40e106f43781b70db06cc3641b107583a81c60e207083800c806102f0160060018
def ridgeSupport392_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport392_code
def ridgeSupport392_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport392_code
def ridgeSupport392_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport392_code
def ridgeSupport392_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport392_code
def ridgeSupport392_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport392_code
def ridgeSupport392_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport392_code
def ridgeSupport392_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport392_code
def ridgeSupport392_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport392_code
def ridgeSupport392_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport392_code
def ridgeSupport392_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport392_code
def ridgeSupport392_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport392_code
def ridgeSupport392_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport392_code
def ridgeSupport392_suffix_011 : List Nat := []
def ridgeSupport392_suffix_010 : List Nat := ridgeSupport392_010 ++ ridgeSupport392_suffix_011
def ridgeSupport392_suffix_009 : List Nat := ridgeSupport392_009 ++ ridgeSupport392_suffix_010
def ridgeSupport392_suffix_008 : List Nat := ridgeSupport392_008 ++ ridgeSupport392_suffix_009
def ridgeSupport392_suffix_007 : List Nat := ridgeSupport392_007 ++ ridgeSupport392_suffix_008
def ridgeSupport392_suffix_006 : List Nat := ridgeSupport392_006 ++ ridgeSupport392_suffix_007
def ridgeSupport392_suffix_005 : List Nat := ridgeSupport392_005 ++ ridgeSupport392_suffix_006
def ridgeSupport392_suffix_004 : List Nat := ridgeSupport392_004 ++ ridgeSupport392_suffix_005
def ridgeSupport392_suffix_003 : List Nat := ridgeSupport392_003 ++ ridgeSupport392_suffix_004
def ridgeSupport392_suffix_002 : List Nat := ridgeSupport392_002 ++ ridgeSupport392_suffix_003
def ridgeSupport392_suffix_001 : List Nat := ridgeSupport392_001 ++ ridgeSupport392_suffix_002
def ridgeSupport392_suffix_000 : List Nat := ridgeSupport392_000 ++ ridgeSupport392_suffix_001
theorem ridgeSupport392_source : candidateSupports 392 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport392_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
