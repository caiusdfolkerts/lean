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
def ridgeSupport74_000 : List Nat := [5,37,41,42,43,174,177,179,182,184,186,189,191,194,196,198,201,203,206,208,616,618,619,622,624,628,630,631,634,636,640,642]
def ridgeSupport74_001 : List Nat := [643,646,648,688,689,691,692,693,694,696,697,699,700,702,703,709,710,712,713,714,715,717,718,720,721,723,724,730,731,733,734,735]
def ridgeSupport74_002 : List Nat := [736,738,739,741,742,744,745,2636,2637,2638,2639,2640,2641,2642,2643,2648,2649,2654,2655,2660,2661,2662,2663,2664,2665,2666,2667,2672,2673,2678,2679,2684]
def ridgeSupport74_003 : List Nat := [2685,2686,2687,2688,2689,2708,2709,2710,2711,2712,2713,2732,2733,2734,2735,2736,2737,2756,2757,2758,2759,2760,2761,2780,2781,2782,2783,2784,2785,2804,2805,2806]
def ridgeSupport74_004 : List Nat := [2807,2808,2809,2828,2829,2830,2831,2832,2833,2837,2839,2843,2845,2849,2851,2894,2895,2906,2907,2915,2917,2921,2923,2930,2931,2942,2943,2966,2967,2978,2979,2987]
def ridgeSupport74_005 : List Nat := [2989,2993,2995,3002,3003,3014,3015,3038,3039,3050,3051,3059,3061,3065,3067,3074,3075,3086,3087,4220,4221,4232,4233,4256,4257,4268,4269,4283,4285,4289,4291,4292]
def ridgeSupport74_006 : List Nat := [4293,4304,4305,4328,4329,4340,4341,4355,4357,4361,4363,4364,4365,4376,4377,4400,4401,4412,4413,4427,4429,4433,4435,5876,5877,5878,5879,5880,5881,5888,5889,5890]
def ridgeSupport74_007 : List Nat := [5891,5892,5893,5900,5901,5902,5903,5904,5905,5924,5925,5926,5927,5928,5929,5948,5949,5950,5951,5952,5953,5957,5959,5963,5965,5969,5971,5972,5973,5974,5975,5976]
def ridgeSupport74_008 : List Nat := [5977,5981,5983,5987,5989,5993,5995,5999,6000,6002,6003,6005,6006,6011,6013,6017,6019,6026,6027,6038,6039,6047,6049,6053,6055,6058,6060,6065,6067,6071,6073,6080]
def ridgeSupport74_009 : List Nat := [6081,6092,6093,6101,6103,6107,6109,6112,6114,6119,6121,6125,6127,6134,6135,6146,6147,6155,6157,6161,6163,6166,6168,6776,6777,6788,6789,6803,6805,6809,6811,6812]
def ridgeSupport74_010 : List Nat := [6813,6820,6822,6824,6825,6830,6831,6842,6843,6857,6859,6863,6865,6866,6867,6874,6876,6878,6879,6884,6885,6896,6897,6911,6913,6917,6919,6920,6921,6928,6930,6932]
def ridgeSupport74_011 : List Nat := [6933,7436,7437,7438,7439,7440,7441,7451,7453,7457,7459,7463,7465,7520,7521,7526,7527,7532,7533,7748,7749,7750,7751,7752,7753]
def ridgeSupport74_code : Nat := 0x1e49f24791fc8de45f2275b7ad9d67eb37587ac1d29e93f48fa43d1de8df447a21d0fe877437a19b15d8a6c4b621b09d846c1f60bb01d7febc75e1ae5d726b7f5bdadcd6d6b4f5a5ad1d67eb2f593abbd5d6abf55daa9d546a9b549a9dd4e6a6f533a95d49ea17509a79d3c606302d813c08e037017803c015fdefed7efbf6dfa6fcf7e2bf05f76fb77d7beadf36f997c1be05ee6f6f7b3bd8deb2f557a7bd2de86f3f797bcb5e2ef15783bc0ddf6ef7776bbaddceee5770bb7ddaeed3765bb1dd7eebb759bac5d5eead755baa5d4eea374dba5dd1ee8b741ba05cfee7d73db9e5ca6e51727b935c96e49711b885c3ee1d70db865c16e09703b815c06e016f9b7c5bdeded6f5b7a454e2a314d8a5c4f6279131898446623110d886442e213105881c3d61e90e987443461a10c5862430e1830bd85dc2b61590a1850422611107d83e303d81cc036012fed7f2bf55f9afad7d4bdf5ef2f1d78cbbb5dd2ecd762bad5d5ae8d744b975cb2dfd6fcb735b92dad6d2b655b1ad6d6b4b4f5a72c8d642b1d58dac5d62ab115882c3d61cb0d5862be55f0af757b2bd55e8ae15702b7d5bcadd56e2b25590ac75632b15588ab15582abd55caad5562a65530a9754b2a55528a8154029fd4fca7d53e29dd4eca7153829ad4d4a69534299d4cca65532297d4bca5952c294d4a4a51528293d49ca4d5260ba45d02e61728b8c5c42e016f8b785ba2db16d0b505a62d11680b3859a2cb1650b245902c61628afc57c2bc15d8ae45702b615a8ad05662b11580a2050c2831410a004f827a13b89d84e827013709ac4d426806803381960c906303101840bf05e82e81700b605982c415c02b01500a404a005
def ridgeSupport74_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport74_code
def ridgeSupport74_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport74_code
def ridgeSupport74_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport74_code
def ridgeSupport74_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport74_code
def ridgeSupport74_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport74_code
def ridgeSupport74_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport74_code
def ridgeSupport74_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport74_code
def ridgeSupport74_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport74_code
def ridgeSupport74_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport74_code
def ridgeSupport74_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport74_code
def ridgeSupport74_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport74_code
def ridgeSupport74_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport74_code
def ridgeSupport74_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport74_code
def ridgeSupport74_suffix_012 : List Nat := []
def ridgeSupport74_suffix_011 : List Nat := ridgeSupport74_011 ++ ridgeSupport74_suffix_012
def ridgeSupport74_suffix_010 : List Nat := ridgeSupport74_010 ++ ridgeSupport74_suffix_011
def ridgeSupport74_suffix_009 : List Nat := ridgeSupport74_009 ++ ridgeSupport74_suffix_010
def ridgeSupport74_suffix_008 : List Nat := ridgeSupport74_008 ++ ridgeSupport74_suffix_009
def ridgeSupport74_suffix_007 : List Nat := ridgeSupport74_007 ++ ridgeSupport74_suffix_008
def ridgeSupport74_suffix_006 : List Nat := ridgeSupport74_006 ++ ridgeSupport74_suffix_007
def ridgeSupport74_suffix_005 : List Nat := ridgeSupport74_005 ++ ridgeSupport74_suffix_006
def ridgeSupport74_suffix_004 : List Nat := ridgeSupport74_004 ++ ridgeSupport74_suffix_005
def ridgeSupport74_suffix_003 : List Nat := ridgeSupport74_003 ++ ridgeSupport74_suffix_004
def ridgeSupport74_suffix_002 : List Nat := ridgeSupport74_002 ++ ridgeSupport74_suffix_003
def ridgeSupport74_suffix_001 : List Nat := ridgeSupport74_001 ++ ridgeSupport74_suffix_002
def ridgeSupport74_suffix_000 : List Nat := ridgeSupport74_000 ++ ridgeSupport74_suffix_001
theorem ridgeSupport74_source : candidateSupports 74 =
    (PackedRawNatGrowth.readList 13 377 ridgeSupport74_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
