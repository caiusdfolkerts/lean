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
def ridgeSupport708_000 : List Nat := [460,461,462,725,726,727,1149,1150,1151,1305,1306,1307,1389,1390,1391,1459,1460,1461,2106,2107,2112,2113,2126,2127,2129,2132,2135,2138,2146,2148,2154,2155]
def ridgeSupport708_001 : List Nat := [2160,2161,2174,2175,2249,2252,2255,2258,2266,2268,2297,2300,2303,2306,2314,2316,2346,2347,2352,2353,2366,2367,2369,2372,2375,2378,2386,2388,2394,2395,2400,2401]
def ridgeSupport708_002 : List Nat := [2414,2415,2489,2492,2495,2498,2506,2508,2537,2540,2543,2546,2554,2556,2698,2699,2700,2701,2702,2703,2710,2711,2712,2713,2714,2715,3641,3644,3647,3650,3658,3660]
def ridgeSupport708_003 : List Nat := [3666,3667,3672,3673,3686,3687,3714,3715,3720,3721,3734,3735,3809,3812,3815,3818,3826,3828,3844,3845,3846,3847,3848,3849,3988,3989,3990,3991,3992,3993,4018,4019]
def ridgeSupport708_004 : List Nat := [4020,4021,4022,4023,4409,4412,4415,4418,4426,4428,4434,4435,4440,4441,4454,4455,4482,4483,4488,4489,4502,4503,4577,4580,4583,4586,4594,4596,4612,4613,4614,4615]
def ridgeSupport708_005 : List Nat := [4616,4617,4756,4757,4758,4759,4760,4761,4786,4787,4788,4789,4790,4791,5465,5468,5471,5474,5482,5484,5490,5491,5496,5497,5510,5511,5538,5539,5544,5545,5558,5559]
def ridgeSupport708_006 : List Nat := [5633,5636,5639,5642,5650,5652,5668,5669,5670,5671,5672,5673,6064,6065,6066,6067,6068,6069,6076,6077,6078,6079,6080,6081,6592,6593,6594,6595,6596,6597,6604,6605]
def ridgeSupport708_007 : List Nat := [6606,6607,6608,6609,7086,7087,7092,7093,7106,7107,7122,7123,7128,7129,7142,7143,7276,7281,7282,7287,7295,7297,7372,7377,7378,7383,7391,7393,7492,7497,7498,7503]
def ridgeSupport708_008 : List Nat := [7511,7513]
def ridgeSupport708_code : Nat := 0x7565d57753dd4a7525d447385cdf735dcd27345ccc7205c7f71ddc7271c5c6c6f9dbe66f65bd86f4dbd26f0dbc26ed5bb46ebdbae67459d0673d9ce67359cc67159c4670d9c267059c05f057c05efd7be5ef57bc5ed57b45ecd7b25ec57b058a5628589d626589562458516125829607581160156dd5b656a55a8568d5a2561d58655e557855cd57255b156a558955f55715594add2b64ad52b44acd2b24a652984a5d2964a552944825208481d206481520447d11f247a91e747911e1465d1964625188460d182459d1664565158454d152453114a450913f44f11393edcfb63ed4fb43eccfb23e64f983e5cf963e54f943c24f083c1cf063c14f043bd0ef23ba8ee73b90ee13a5ce963a24e883a0ce82399ce663964e58394ce523930e4a3908e3f38f0e392a6ca9a2a64a982a5ca962a3ca8e2a34a8c2a2ca8a27f09fa27c89ef27b09e927309ca27089bf26f09b925bc96e2584960256c95a25509522528947251094124fc93e24c493024ac92a243090a24088ff23f08f923708da23488cf23308c921fc87e21c487021ac86a219086221688572150851213c84e210484020ec83a16d45b416cc56f15b856d146c51a146447f11f847d0b5c2d60b541ce07341cc
def ridgeSupport708_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport708_code
def ridgeSupport708_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport708_code
def ridgeSupport708_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport708_code
def ridgeSupport708_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport708_code
def ridgeSupport708_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport708_code
def ridgeSupport708_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport708_code
def ridgeSupport708_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport708_code
def ridgeSupport708_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport708_code
def ridgeSupport708_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport708_code
def ridgeSupport708_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport708_code
def ridgeSupport708_suffix_009 : List Nat := []
def ridgeSupport708_suffix_008 : List Nat := ridgeSupport708_008 ++ ridgeSupport708_suffix_009
def ridgeSupport708_suffix_007 : List Nat := ridgeSupport708_007 ++ ridgeSupport708_suffix_008
def ridgeSupport708_suffix_006 : List Nat := ridgeSupport708_006 ++ ridgeSupport708_suffix_007
def ridgeSupport708_suffix_005 : List Nat := ridgeSupport708_005 ++ ridgeSupport708_suffix_006
def ridgeSupport708_suffix_004 : List Nat := ridgeSupport708_004 ++ ridgeSupport708_suffix_005
def ridgeSupport708_suffix_003 : List Nat := ridgeSupport708_003 ++ ridgeSupport708_suffix_004
def ridgeSupport708_suffix_002 : List Nat := ridgeSupport708_002 ++ ridgeSupport708_suffix_003
def ridgeSupport708_suffix_001 : List Nat := ridgeSupport708_001 ++ ridgeSupport708_suffix_002
def ridgeSupport708_suffix_000 : List Nat := ridgeSupport708_000 ++ ridgeSupport708_suffix_001
theorem ridgeSupport708_source : candidateSupports 708 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport708_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
