module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport522_000 : List Nat := [8,40,43,45,46,199,200,202,207,209,223,224,226,231,233,235,236,238,243,245,639,641,644,645,647,663,665,668,669,671,675,677]
def ridgeSupport522_001 : List Nat := [680,681,683,708,709,711,712,715,716,717,719,720,722,727,728,729,730,732,733,736,737,738,740,741,743,748,749,750,751,753,754,757]
def ridgeSupport522_002 : List Nat := [758,759,761,762,764,769,770,2640,2641,2646,2647,2652,2653,2654,2655,2656,2657,2658,2659,2664,2665,2670,2671,2676,2677,2678,2679,2680,2681,2682,2683,2702]
def ridgeSupport522_003 : List Nat := [2703,2704,2705,2706,2707,2726,2727,2728,2729,2730,2731,2750,2751,2752,2753,2754,2755,2774,2775,2776,2777,2778,2779,2798,2799,2800,2801,2802,2803,2822,2823,2824]
def ridgeSupport522_004 : List Nat := [2825,2826,2827,2828,2830,2834,2836,2840,2842,2846,2847,2848,2849,2850,2851,2970,2971,2982,2983,2984,2986,2990,2992,3006,3007,3018,3019,3042,3043,3054,3055,3056]
def ridgeSupport522_005 : List Nat := [3058,3062,3064,3078,3079,3090,3091,3114,3115,3126,3127,3128,3130,3134,3136,3150,3151,3162,3163,4296,4297,4308,4309,4332,4333,4344,4345,4352,4354,4358,4360,4368]
def ridgeSupport522_006 : List Nat := [4369,4380,4381,4404,4405,4416,4417,4424,4426,4430,4432,4440,4441,4452,4453,4476,4477,4488,4489,4496,4498,4502,4504,5208,5209,5212,5213,5214,5215,5222,5224,5228]
def ridgeSupport522_007 : List Nat := [5230,5234,5236,5298,5299,5304,5305,5310,5311,5534,5535,5536,5537,5538,5539,6134,6135,6136,6137,6138,6139,6140,6142,6146,6148,6150,6151,6152,6154,6158,6160,6162]
def ridgeSupport522_008 : List Nat := [6163,6186,6187,6192,6193,6204,6205,6210,6211,6222,6223,6228,6229,6452,6454,6458,6460,6470,6472,6476,6478,6488,6490,6494,6496]
def ridgeSupport522_code : Nat := 0x1960caf656b2b194eca6652328d93cc9d64db269855c2a613f09d843c2160f7079831c1860af055813c09604301d80ac04601f00d804c015ffaff97fbbfd5fe6ff17f7bfb568eb455a1ad0567eb3d4bfa5f52e69714b3a5951d28e546ea3651a28cd45fa2f51768b9459a2c466232d1928c8462631117d8be45962c91598ac454229d14a8a4450628113589a4476239111888442220d10288043e61f10ed87643561a90c9864316d8b4c4f627310187cc3a61c30dd86cc2b615304d824c076032fe17ecbf25f82fbd7dcbe35f12f2d794bbf5df2ec175cbaa5d42e9d74cb9b5cd2c8d644b215902c7d63cb1a58c2c51624b0e5862c2d614b095842c1d60caf35792bc55e0aef5772b6d5b4ad956c2b5d5acac35612b05580abf55f2aad554aa95542a9d54ca935492a45520a8f54729ed4f4a7953c29dd4eca7553a29bd4dca69534298d4c4a61530297d4bca5d52e295d4aca515280c086022fc17d0be45ee2f617a8bc85e22ef1770bb45d82e71728b905c42e11700b745b82da16c8b605ae2d21680b3c59a2cc1658b2058e2c51620aac5522a81528a8c53e29d14e0a6452e2871428a1050227f07a83cc1dc0ec07583a41ce0e2070037c1a20cf065032018e02e01680ac050008
def ridgeSupport522_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport522_code
def ridgeSupport522_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport522_code
def ridgeSupport522_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport522_code
def ridgeSupport522_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport522_code
def ridgeSupport522_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport522_code
def ridgeSupport522_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport522_code
def ridgeSupport522_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport522_code
def ridgeSupport522_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport522_code
def ridgeSupport522_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport522_code
def ridgeSupport522_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport522_code
def ridgeSupport522_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 281 ridgeSupport522_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
