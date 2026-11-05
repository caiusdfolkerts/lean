module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport73_000 : List Nat := [5,21,22,23,175,176,179,180,185,187,188,191,192,197,199,200,203,204,209,330,419,420,422,423,424,425,427,428,430,431,433,434]
def ridgeSupport73_001 : List Nat := [440,441,443,444,445,446,448,449,451,452,454,455,461,462,464,465,466,467,469,470,472,473,475,476,2396,2397,2398,2399,2400,2401,2402,2403]
def ridgeSupport73_002 : List Nat := [2408,2409,2414,2415,2420,2421,2422,2423,2424,2425,2426,2427,2432,2433,2438,2439,2444,2445,2446,2447,2448,2449,2468,2469,2470,2471,2472,2473,2492,2493,2494,2495]
def ridgeSupport73_003 : List Nat := [2496,2497,2516,2517,2518,2519,2520,2521,2540,2541,2542,2543,2544,2545,2564,2565,2566,2567,2568,2569,2588,2589,2590,2591,2592,2593,2597,2599,2603,2605,2609,2611]
def ridgeSupport73_004 : List Nat := [2882,2883,2900,2901,2918,2919,2927,2929,2933,2935,2936,2937,2954,2955,2972,2973,2990,2991,2999,3001,3005,3007,3008,3009,3026,3027,3044,3045,3062,3063,3071,3073]
def ridgeSupport73_005 : List Nat := [3077,3079,3080,3081,3644,3646,3651,3652,3654,3657,3660,3662,3667,3668,3670,3673,3676,3678,3683,3684,3686,3689,5744,5745,5746,5747,5748,5749,5756,5757,5758,5759]
def ridgeSupport73_006 : List Nat := [5760,5761,5768,5769,5770,5771,5772,5773,5792,5793,5794,5795,5796,5797,5816,5817,5818,5819,5820,5821,5825,5827,5831,5833,5837,5839,5840,5841,5842,5843,5844,5845]
def ridgeSupport73_007 : List Nat := [5849,5851,5855,5857,5861,5863,5867,5868,5870,5871,5873,5874,6014,6015,6023,6025,6029,6031,6032,6033,6046,6048,6050,6051,6059,6061,6068,6069,6077,6079,6083,6085]
def ridgeSupport73_008 : List Nat := [6086,6087,6100,6102,6104,6105,6113,6115,6122,6123,6131,6133,6137,6139,6140,6141,6154,6156,6158,6159,6167,6169,6488,6491,6492,6495,6496,6499,7424,7425,7426,7427]
def ridgeSupport73_009 : List Nat := [7428,7429,7450,7452,7456,7458,7462,7464,7712,7713,7714,7715,7716,7717,7882,7886,7890]
def ridgeSupport73_code : Nat := 0x1ed2f677b2bc4be24f11f88bc43e20e94749ba45d20e8e746ba0bd04e81f40ba03d00cb1e5832bf95ccade563033817c07e03b01980abfedff2ff77f9bfadfcefd77eabf1df86fb37d8beb5f52f8f7c6be2df0ef7f7bdbdaded2f5b7abbd1de8af4179ebc8de42f1f78dbc4de1eeff77eb795bc6ddf6eeb765baedcf6e5b70db7edb76d9b6adb52da76d2b68db42d9f6cdb64db1ed876c1b5edaf2d776bab5cdae2d4b6a4b51da8ad436a0b46da32d1768ab44da22d03680b3fd9facfb67cb3ad9d2ce7672b38d9c1cd2e66732398dcbce5c72cb959ca8e537273931c92e46722390dc7ce3c604b02180ec05600affd7eebf65f2af917a6bd25e0af0177ebbd5dcaedd75ebae5ceae71716b8a5bcade16eeb755b8adbd6ceb665aaad51686b42519a8c545aa2b513a895442a2050fa87943aa1c504a82140ea06502a8113e29f04f7a7b93da9ec4eca7613ae9d64eaa7513829c04dfa6f937a9bc4d4a6a134e9a64d2a6913229904c7a63931a98c4c3a6193029804bda5e92f29784bba5d92ea9744b7a5b92d29684b1a5892c29604afa5792ba95c0ee076c3b21d80eb07543a61d20e8874039c1cd0e387183881c30e0870037c1bd0de06ec3721b80d906c435e1ae0d606ac3521a80d386983481a30a503441980cb064031c18a0c005f82f01760b905a02cc1600af00b805802a005
def ridgeSupport73_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport73_code
def ridgeSupport73_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport73_code
def ridgeSupport73_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport73_code
def ridgeSupport73_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport73_code
def ridgeSupport73_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport73_code
def ridgeSupport73_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport73_code
def ridgeSupport73_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport73_code
def ridgeSupport73_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport73_code
def ridgeSupport73_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport73_code
def ridgeSupport73_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport73_code
def ridgeSupport73_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport73_code
def ridgeSupport73_suffix_010 : List Nat := []
def ridgeSupport73_suffix_009 : List Nat := ridgeSupport73_009 ++ ridgeSupport73_suffix_010
def ridgeSupport73_suffix_008 : List Nat := ridgeSupport73_008 ++ ridgeSupport73_suffix_009
def ridgeSupport73_suffix_007 : List Nat := ridgeSupport73_007 ++ ridgeSupport73_suffix_008
def ridgeSupport73_suffix_006 : List Nat := ridgeSupport73_006 ++ ridgeSupport73_suffix_007
def ridgeSupport73_suffix_005 : List Nat := ridgeSupport73_005 ++ ridgeSupport73_suffix_006
def ridgeSupport73_suffix_004 : List Nat := ridgeSupport73_004 ++ ridgeSupport73_suffix_005
def ridgeSupport73_suffix_003 : List Nat := ridgeSupport73_003 ++ ridgeSupport73_suffix_004
def ridgeSupport73_suffix_002 : List Nat := ridgeSupport73_002 ++ ridgeSupport73_suffix_003
def ridgeSupport73_suffix_001 : List Nat := ridgeSupport73_001 ++ ridgeSupport73_suffix_002
def ridgeSupport73_suffix_000 : List Nat := ridgeSupport73_000 ++ ridgeSupport73_suffix_001
theorem ridgeSupport73_source : candidateSupports 73 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport73_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
