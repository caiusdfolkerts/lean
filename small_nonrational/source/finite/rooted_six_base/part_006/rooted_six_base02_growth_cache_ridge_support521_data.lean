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
def ridgeSupport521_000 : List Nat := [8,23,25,26,198,201,202,205,208,222,225,226,229,232,234,237,238,241,244,333,439,440,442,443,446,447,448,450,451,453,458,459]
def ridgeSupport521_001 : List Nat := [460,461,463,464,467,468,469,471,472,474,479,480,481,482,484,485,488,489,490,492,493,495,500,501,2400,2401,2406,2407,2412,2413,2414,2415]
def ridgeSupport521_002 : List Nat := [2416,2417,2418,2419,2424,2425,2430,2431,2436,2437,2438,2439,2440,2441,2442,2443,2462,2463,2464,2465,2466,2467,2486,2487,2488,2489,2490,2491,2510,2511,2512,2513]
def ridgeSupport521_003 : List Nat := [2514,2515,2534,2535,2536,2537,2538,2539,2558,2559,2560,2561,2562,2563,2582,2583,2584,2585,2586,2587,2588,2590,2594,2596,2600,2602,2606,2607,2608,2609,2610,2611]
def ridgeSupport521_004 : List Nat := [2958,2959,2976,2977,2994,2995,2996,2998,3002,3004,3012,3013,3030,3031,3048,3049,3066,3067,3068,3070,3074,3076,3084,3085,3102,3103,3120,3121,3138,3139,3140,3142]
def ridgeSupport521_005 : List Nat := [3146,3148,3156,3157,3677,3679,3682,3685,3687,3688,3709,3711,3714,3717,3719,3720,3725,3727,3730,3733,3735,3736,5748,5749,5752,5753,5754,5755,5760,5761,5764,5765]
def ridgeSupport521_006 : List Nat := [5766,5767,5786,5787,5788,5789,5790,5791,5810,5811,5812,5813,5814,5815,5816,5818,5822,5824,5828,5830,5834,5835,5836,5837,5838,5839,5840,5842,5846,5848,5852,5854]
def ridgeSupport521_007 : List Nat := [5858,5859,5860,5861,5862,5863,5865,5866,5868,5869,5871,5872,6072,6073,6074,6076,6080,6082,6090,6091,6099,6101,6108,6109,6110,6112,6126,6127,6128,6130,6134,6136]
def ridgeSupport521_008 : List Nat := [6144,6145,6153,6155,6162,6163,6164,6166,6180,6181,6182,6184,6188,6190,6198,6199,6207,6209,6216,6217,6218,6220,6497,6498,6505,6506,6509,6510,7428,7429,7432,7433]
def ridgeSupport521_009 : List Nat := [7434,7435,7455,7457,7461,7463,7467,7469,7730,7731,7732,7733,7734,7735,7891,7899,7903]
def ridgeSupport521_code : Nat := 0x1edff6dfb4fc6fe36f1af8d3c67e32e96f4afa4fd25e90f47fa17d0ae84f423a0bd04cb765b72d5969cb1658709984ac24e12308383fc1be0db05d82cc14609b04b824c0b6053027812c05e027003800bfc5fdafe57f0bf7dfbafc17debeedf72fab7d3be5df2af857c0bde5eeaf737b8b785bbeddb6ecb755ba6dcf6e6b72db92dc76e2b6f5b72db16d6b695b42d9f6ceb66db32d976cab635b12d816beb5d5ae2d6f6b6b5adad2d676b2b4fda7ad3b69cb4dda6ad0f686b42da12d03680b3dd9eacf3678b3ad9d1d30e9774aba49d1ee8d7443a1dd0ae8273fb9f5cd0e67732b989cbee5d62ab151898c4a6233111886c42618b0c183ec1e606b031808c025ff2ff17f6bfa5f4afa17aebd65e2af11778bba5db2ed1766bb25d0ae8171eb8e519a8c9462a30517a8b9454a28512288943ca1c50da869432a1850ba859406a02500a8013fe9fe4f5a7a93d29e84f3a7993a69d24e8a74139e9ce4dda6e93729b84dba6d93469a24d0a68133e99e4c5a6293129884c3a61930a9844bfa5f92f29784b9a5c92e29704b7a5b92da96c4b3a5992c29600fa87d03de1ed0f607a83d21e80f287903c41e10f0077c3b41d80eb87543a81d30e8073c39a1cc0e5872838a1c30e1070037e1be0dd86e83701b70a683d01e20ee07683a81d00e507103841bc0d006683281920c600d006402e008
def ridgeSupport521_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport521_code
def ridgeSupport521_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport521_code
def ridgeSupport521_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport521_code
def ridgeSupport521_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport521_code
def ridgeSupport521_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport521_code
def ridgeSupport521_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport521_code
def ridgeSupport521_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport521_code
def ridgeSupport521_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport521_code
def ridgeSupport521_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport521_code
def ridgeSupport521_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport521_code
def ridgeSupport521_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport521_code
def ridgeSupport521_suffix_010 : List Nat := []
def ridgeSupport521_suffix_009 : List Nat := ridgeSupport521_009 ++ ridgeSupport521_suffix_010
def ridgeSupport521_suffix_008 : List Nat := ridgeSupport521_008 ++ ridgeSupport521_suffix_009
def ridgeSupport521_suffix_007 : List Nat := ridgeSupport521_007 ++ ridgeSupport521_suffix_008
def ridgeSupport521_suffix_006 : List Nat := ridgeSupport521_006 ++ ridgeSupport521_suffix_007
def ridgeSupport521_suffix_005 : List Nat := ridgeSupport521_005 ++ ridgeSupport521_suffix_006
def ridgeSupport521_suffix_004 : List Nat := ridgeSupport521_004 ++ ridgeSupport521_suffix_005
def ridgeSupport521_suffix_003 : List Nat := ridgeSupport521_003 ++ ridgeSupport521_suffix_004
def ridgeSupport521_suffix_002 : List Nat := ridgeSupport521_002 ++ ridgeSupport521_suffix_003
def ridgeSupport521_suffix_001 : List Nat := ridgeSupport521_001 ++ ridgeSupport521_suffix_002
def ridgeSupport521_suffix_000 : List Nat := ridgeSupport521_000 ++ ridgeSupport521_suffix_001
theorem ridgeSupport521_source : candidateSupports 521 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport521_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
