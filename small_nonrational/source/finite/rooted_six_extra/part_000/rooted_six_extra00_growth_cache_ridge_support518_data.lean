module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport518_000 : List Nat := [4,38,41,43,44,155,156,158,163,165,179,180,182,187,189,191,192,194,199,201,647,649,652,653,655,671,673,676,677,679,683,685]
def ridgeSupport518_001 : List Nat := [688,689,691,716,717,719,720,723,724,725,727,728,730,735,736,737,738,740,741,744,745,746,748,749,751,756,757,758,759,761,762,765]
def ridgeSupport518_002 : List Nat := [766,767,769,770,772,777,778,2348,2349,2354,2355,2360,2361,2362,2363,2364,2365,2366,2367,2372,2373,2378,2379,2384,2385,2386,2387,2388,2389,2390,2391,2410]
def ridgeSupport518_003 : List Nat := [2411,2412,2413,2414,2415,2434,2435,2436,2437,2438,2439,2458,2459,2460,2461,2462,2463,2482,2483,2484,2485,2486,2487,2506,2507,2508,2509,2510,2511,2530,2531,2532]
def ridgeSupport518_004 : List Nat := [2533,2534,2535,2536,2538,2542,2544,2548,2550,2554,2555,2556,2557,2558,2559,2678,2679,2690,2691,2692,2694,2698,2700,2714,2715,2726,2727,2750,2751,2762,2763,2764]
def ridgeSupport518_005 : List Nat := [2766,2770,2772,2786,2787,2798,2799,2822,2823,2834,2835,2836,2838,2842,2844,2858,2859,2870,2871,4724,4725,4736,4737,4760,4761,4772,4773,4780,4782,4786,4788,4796]
def ridgeSupport518_006 : List Nat := [4797,4808,4809,4832,4833,4844,4845,4852,4854,4858,4860,4868,4869,4880,4881,4904,4905,4916,4917,4924,4926,4930,4932,7138,7139,7140,7141,7142,7143,7786,7787,7788]
def ridgeSupport518_007 : List Nat := [7789,7790,7791,7792,7794,7798,7800,7802,7803,7804,7806,7810,7812,7814,7815,7838,7839,7844,7845,7856,7857,7862,7863,7874,7875,7880,7881,8296,8298,8302,8304,8314]
def ridgeSupport518_008 : List Nat := [8316,8320,8322,8332,8334,8338,8340]
def ridgeSupport518_code : Nat := 0x2094824a08e8232082820207c81ea07081ba06a81a1ec97b21ec37b09eb77ad9eb17ac1ea57a91e9f7a79e877a19e847a09e7e79f1e7b79e9e7879d9e7279c1e6f79b9e6d79b1e6b79a9be76f99be56f91be36f893444d0933e4cf13354cd13294ca13114c413054c112fc4be92f64bd12ed4bb12e14b812c94b212bd4af12b44ac92ae4ab12a54a912994a612814a0127549d0b372cd8b2b2ca8b1c2c68b162c50b132c48b072c18aef2bb8ae32b88ad42b48ace2b30acb2b28abf2af8aa72a98a9b2a68a8c2a28a862a10a832a08a7729d89ff27f89fd27f09fb27e89f627d09f027b89ea27a09e727989e527909e327889cf27389cd27309cb27289b726d89b526d09b326c899f267899d267099b266898726189852610983260896f25b896d25b096b25a8957255895525509532548951254094b2528945251093f24f893d24f093b24e893924e093324c892d24b030a0c243040c083010bfc2fe0bf42fa0be42f70bd82f50bd02ef0bb42ec0ba82e90ba02e50b902e20b842e00b7c2da0b602d70b542d40b4c2d00b3c2cd0b302b30ac42b00ab42ab0a9c2a50a902a10a7c28f0a3428c0a2428703240c703080c002fc0bd02ec0b602d00b302940a3027809c026c02c00ac0290098004
def ridgeSupport518_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport518_code
def ridgeSupport518_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport518_code
def ridgeSupport518_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport518_code
def ridgeSupport518_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport518_code
def ridgeSupport518_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport518_code
def ridgeSupport518_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport518_code
def ridgeSupport518_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport518_code
def ridgeSupport518_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport518_code
def ridgeSupport518_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport518_code
def ridgeSupport518_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport518_code
def ridgeSupport518_suffix_009 : List Nat := []
def ridgeSupport518_suffix_008 : List Nat := ridgeSupport518_008 ++ ridgeSupport518_suffix_009
def ridgeSupport518_suffix_007 : List Nat := ridgeSupport518_007 ++ ridgeSupport518_suffix_008
def ridgeSupport518_suffix_006 : List Nat := ridgeSupport518_006 ++ ridgeSupport518_suffix_007
def ridgeSupport518_suffix_005 : List Nat := ridgeSupport518_005 ++ ridgeSupport518_suffix_006
def ridgeSupport518_suffix_004 : List Nat := ridgeSupport518_004 ++ ridgeSupport518_suffix_005
def ridgeSupport518_suffix_003 : List Nat := ridgeSupport518_003 ++ ridgeSupport518_suffix_004
def ridgeSupport518_suffix_002 : List Nat := ridgeSupport518_002 ++ ridgeSupport518_suffix_003
def ridgeSupport518_suffix_001 : List Nat := ridgeSupport518_001 ++ ridgeSupport518_suffix_002
def ridgeSupport518_suffix_000 : List Nat := ridgeSupport518_000 ++ ridgeSupport518_suffix_001
theorem ridgeSupport518_source : candidateSupports 518 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport518_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
