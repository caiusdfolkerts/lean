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
def ridgeSupport522_000 : List Nat := [8,40,43,45,46,199,200,202,207,209,223,224,226,231,233,235,236,238,243,245,639,641,644,645,647,663,665,668,669,671,675,677]
def ridgeSupport522_001 : List Nat := [680,681,683,708,709,711,712,715,716,717,719,720,722,727,728,729,730,732,733,736,737,738,740,741,743,748,749,750,751,753,754,757]
def ridgeSupport522_002 : List Nat := [758,759,761,762,764,769,770,2640,2641,2646,2647,2652,2653,2654,2655,2656,2657,2658,2659,2664,2665,2670,2671,2676,2677,2678,2679,2680,2681,2682,2683,2702]
def ridgeSupport522_003 : List Nat := [2703,2704,2705,2706,2707,2726,2727,2728,2729,2730,2731,2750,2751,2752,2753,2754,2755,2774,2775,2776,2777,2778,2779,2798,2799,2800,2801,2802,2803,2822,2823,2824]
def ridgeSupport522_004 : List Nat := [2825,2826,2827,2828,2830,2834,2836,2840,2842,2846,2847,2848,2849,2850,2851,2970,2971,2982,2983,2984,2986,2990,2992,3006,3007,3018,3019,3042,3043,3054,3055,3056]
def ridgeSupport522_005 : List Nat := [3058,3062,3064,3078,3079,3090,3091,3114,3115,3126,3127,3128,3130,3134,3136,3150,3151,3162,3163,4296,4297,4308,4309,4332,4333,4344,4345,4352,4354,4358,4360,4368]
def ridgeSupport522_006 : List Nat := [4369,4380,4381,4404,4405,4416,4417,4424,4426,4430,4432,4440,4441,4452,4453,4476,4477,4488,4489,4496,4498,4502,4504,5880,5881,5884,5885,5886,5887,5892,5893,5896]
def ridgeSupport522_007 : List Nat := [5897,5898,5899,5918,5919,5920,5921,5922,5923,5942,5943,5944,5945,5946,5947,5948,5950,5954,5956,5960,5962,5966,5967,5968,5969,5970,5971,5972,5974,5978,5980,5984]
def ridgeSupport522_008 : List Nat := [5986,5990,5991,5992,5993,5994,5995,5997,5998,6000,6001,6003,6004,6062,6064,6068,6070,6084,6085,6096,6097,6098,6100,6104,6106,6111,6113,6116,6118,6122,6124,6138]
def ridgeSupport522_009 : List Nat := [6139,6150,6151,6152,6154,6158,6160,6165,6167,6170,6172,6176,6178,6192,6193,6204,6205,6206,6208,6212,6214,6219,6221,6834,6835,6846,6847,6854,6856,6860,6862,6870]
def ridgeSupport522_010 : List Nat := [6871,6873,6875,6882,6883,6888,6889,6900,6901,6908,6910,6914,6916,6924,6925,6927,6929,6936,6937,6942,6943,6954,6955,6962,6964,6968,6970,6978,6979,6981,6983,6990]
def ridgeSupport522_011 : List Nat := [6991,7440,7441,7444,7445,7446,7447,7454,7456,7460,7462,7466,7468,7530,7531,7536,7537,7542,7543,7766,7767,7768,7769,7770,7771]
def ridgeSupport522_code : Nat := 0x1e5bf2d7967cb1e57f2b75dfaedd71eb875afad5d2ce95749ba49d20e8f745fa2dd15e8a7447a21b4fda76d1f68bb43da16ceb671b34d996caf655b1fd8f6c67631b11d87ec37619b04d816bfb5f9af5d7a6ba75d1ae3d716b6f5b3ad7d6b6b3b599ac8d636aff57dab3d596137097846c22610307d83dc1e60c7061822c106073035817c0ae04301d80ac04601f00d7fbbfd5fb2fd57e6bf25f86fbf7dabec5f52fa57d1be85f16f897b6bda5ec2f5d774bb9ddc6ee176ebb6ddaeed5769bb45d9eecd762bb05d72eb5756baa5d4eea5751ba85d3ee9d74aba45d12e8573eb9e5ceee75739b9c5cdee6d723b915c86e4171fb8f5c2ee15709b845c16e096ffb7f5bf6df96f9b7c466232d1928c8462631117d8be45962c91598ac454229d14a8a4450628113589a4476239111888442220d10288043e61f10ed87643561a90c9864316d8b4c4f627310187cc3a61c30dd86cc2b615304d824c076032fe17ecbf25f82fbd7dcbe35f12f2d794bbf5df2ec175cbaa5d42e9d74cb9b5cd2c8d644b215902c7d63cb1a58c2c51624b0e5862c2d614b095842c1d60caf35792bc55e0aef5772b6d5b4ad956c2b5d5acac35612b05580abf55f2aad554aa95542a9d54ca935492a45520a8f54729ed4f4a7953c29dd4eca7553a29bd4dca69534298d4c4a61530297d4bca5d52e295d4aca515280c086022fc17d0be45ee2f617a8bc85e22ef1770bb45d82e71728b905c42e11700b745b82da16c8b605ae2d21680b3c59a2cc1658b2058e2c51620aac5522a81528a8c53e29d14e0a6452e2871428a1050227f07a83cc1dc0ec07583a41ce0e2070037c1a20cf065032018e02e01680ac050008
def ridgeSupport522_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport522_code
def ridgeSupport522_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport522_code
def ridgeSupport522_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport522_code
def ridgeSupport522_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport522_code
def ridgeSupport522_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport522_code
def ridgeSupport522_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport522_code
def ridgeSupport522_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport522_code
def ridgeSupport522_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport522_code
def ridgeSupport522_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport522_code
def ridgeSupport522_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport522_code
def ridgeSupport522_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport522_code
def ridgeSupport522_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport522_code
def ridgeSupport522_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport522_code
def ridgeSupport522_suffix_012 : List Nat := []
def ridgeSupport522_suffix_011 : List Nat := ridgeSupport522_011 ++ ridgeSupport522_suffix_012
def ridgeSupport522_suffix_010 : List Nat := ridgeSupport522_010 ++ ridgeSupport522_suffix_011
def ridgeSupport522_suffix_009 : List Nat := ridgeSupport522_009 ++ ridgeSupport522_suffix_010
def ridgeSupport522_suffix_008 : List Nat := ridgeSupport522_008 ++ ridgeSupport522_suffix_009
def ridgeSupport522_suffix_007 : List Nat := ridgeSupport522_007 ++ ridgeSupport522_suffix_008
def ridgeSupport522_suffix_006 : List Nat := ridgeSupport522_006 ++ ridgeSupport522_suffix_007
def ridgeSupport522_suffix_005 : List Nat := ridgeSupport522_005 ++ ridgeSupport522_suffix_006
def ridgeSupport522_suffix_004 : List Nat := ridgeSupport522_004 ++ ridgeSupport522_suffix_005
def ridgeSupport522_suffix_003 : List Nat := ridgeSupport522_003 ++ ridgeSupport522_suffix_004
def ridgeSupport522_suffix_002 : List Nat := ridgeSupport522_002 ++ ridgeSupport522_suffix_003
def ridgeSupport522_suffix_001 : List Nat := ridgeSupport522_001 ++ ridgeSupport522_suffix_002
def ridgeSupport522_suffix_000 : List Nat := ridgeSupport522_000 ++ ridgeSupport522_suffix_001
theorem ridgeSupport522_source : candidateSupports 522 =
    (PackedRawNatGrowth.readList 13 377 ridgeSupport522_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
