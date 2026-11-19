module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_code_3 522
cert_ridgeSupport_rest_2 522 000 0
cert_ridgeSupport_rest_2 522 001 416
cert_ridgeSupport_rest_2 522 002 832
cert_ridgeSupport_rest_2 522 003 1248
cert_ridgeSupport_rest_2 522 004 1664
cert_ridgeSupport_rest_2 522 005 2080
cert_ridgeSupport_rest_2 522 006 2496
cert_ridgeSupport_rest_2 522 007 2912
cert_ridgeSupport_rest_2 522 008 3328
cert_ridgeSupport_rest_2 522 009 3653
cert_ridgeSupport_suffix_4 522 009
cert_ridgeSupport_suffix_3 522 008 009
cert_ridgeSupport_suffix_3 522 007 008
cert_ridgeSupport_suffix_3 522 006 007
cert_ridgeSupport_suffix_3 522 005 006
cert_ridgeSupport_suffix_3 522 004 005
cert_ridgeSupport_suffix_3 522 003 004
cert_ridgeSupport_suffix_3 522 002 003
cert_ridgeSupport_suffix_3 522 001 002
cert_ridgeSupport_suffix_3 522 000 001
cert_ridgeSupport_source_3 522 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
