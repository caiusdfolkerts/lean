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
def ridgeSupport712_000 : List Nat := [544,545,546,881,882,883,1146,1147,1148,1570,1571,1572,1654,1655,1656,1724,1725,1726,2874,2875,2880,2881,2894,2895,2897,2900,2903,2906,2914,2916,2922,2923]
def ridgeSupport712_001 : List Nat := [2928,2929,2942,2943,3017,3020,3023,3026,3034,3036,3065,3068,3071,3074,3082,3084,3114,3115,3120,3121,3134,3135,3137,3140,3143,3146,3154,3156,3162,3163,3168,3169]
def ridgeSupport712_002 : List Nat := [3182,3183,3257,3260,3263,3266,3274,3276,3305,3308,3311,3314,3322,3324,3466,3467,3468,3469,3470,3471,3478,3479,3480,3481,3482,3483,3642,3643,3648,3649,3662,3663]
def ridgeSupport712_003 : List Nat := [3665,3668,3671,3674,3682,3684,3690,3691,3696,3697,3710,3711,3785,3788,3791,3794,3802,3804,3833,3836,3839,3842,3850,3852,3994,3995,3996,3997,3998,3999,4006,4007]
def ridgeSupport712_004 : List Nat := [4008,4009,4010,4011,4937,4940,4943,4946,4954,4956,4962,4963,4968,4969,4982,4983,5010,5011,5016,5017,5030,5031,5105,5108,5111,5114,5122,5124,5140,5141,5142,5143]
def ridgeSupport712_005 : List Nat := [5144,5145,5284,5285,5286,5287,5288,5289,5314,5315,5316,5317,5318,5319,5705,5708,5711,5714,5722,5724,5730,5731,5736,5737,5750,5751,5778,5779,5784,5785,5798,5799]
def ridgeSupport712_006 : List Nat := [5873,5876,5879,5882,5890,5892,5908,5909,5910,5911,5912,5913,6052,6053,6054,6055,6056,6057,6082,6083,6084,6085,6086,6087,6880,6881,6882,6883,6884,6885,6892,6893]
def ridgeSupport712_007 : List Nat := [6894,6895,6896,6897,7182,7183,7188,7189,7202,7203,7218,7219,7224,7225,7238,7239,7278,7279,7284,7285,7298,7299,7432,7437,7438,7443,7451,7453,7528,7533,7534,7539]
def ridgeSupport712_008 : List Nat := [7547,7549]
def ridgeSupport712_code : Nat := 0x75f5d7b75cdd6e75b5d687475d1b744dd0e7435d08720dc8271d5c7471bdc6e711dc4670e5c3870cdc32708dc227055c14703dc0e6bc5af06bbdaee6bb5aec6b95ae46b8dae26b85ae05f1d7c65f157c45f0d7c25ea57a85e9d7a65e957a45c657185c5d7165c557145c117025be96f75bd16f15a9d6a65a656985a4d69259dd67659a5668598d662597165a594964f5931649531d4c653154c4530d4c252a54a8529d4a652954a45065418505d416505541450114024fe93f74fd13f14e9d3a64e653984e4d3924ddd3764da53684d8d3624d7135a4d4934f4d313493eacfaa3ea4fa83e9cfa63e7cf9e3e74f9c3e6cf9a3c30f0a3c08eff3bf0ef93b70eda3b48ecf3b30ec939fce7e39c4e7039ace6a3990e623968e573950e51393ce4e3904e4038ece3a366cd9a3664d98365cd96363cd8e3634d8c362cd8a33f0cfa33c8cef33b0ce93330cca3308cbf32f0cb931bcc6e3184c60316cc5a3150c523128c473110c4130fcc3e30c4c3030acc2a3030c0a3008bff2ff0bf92f70bda2f48bcf2f30bc92dfcb7e2dc4b702dacb6a2d90b622d68b572d50b512d3cb4e2d04b402cecb3a1af86bd1af067819dc6761890623188847c11ec47a0dcc3720dc42220884220
def ridgeSupport712_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport712_code
def ridgeSupport712_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport712_code
def ridgeSupport712_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport712_code
def ridgeSupport712_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport712_code
def ridgeSupport712_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport712_code
def ridgeSupport712_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport712_code
def ridgeSupport712_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport712_code
def ridgeSupport712_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport712_code
def ridgeSupport712_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport712_code
def ridgeSupport712_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport712_code
def ridgeSupport712_suffix_009 : List Nat := []
def ridgeSupport712_suffix_008 : List Nat := ridgeSupport712_008 ++ ridgeSupport712_suffix_009
def ridgeSupport712_suffix_007 : List Nat := ridgeSupport712_007 ++ ridgeSupport712_suffix_008
def ridgeSupport712_suffix_006 : List Nat := ridgeSupport712_006 ++ ridgeSupport712_suffix_007
def ridgeSupport712_suffix_005 : List Nat := ridgeSupport712_005 ++ ridgeSupport712_suffix_006
def ridgeSupport712_suffix_004 : List Nat := ridgeSupport712_004 ++ ridgeSupport712_suffix_005
def ridgeSupport712_suffix_003 : List Nat := ridgeSupport712_003 ++ ridgeSupport712_suffix_004
def ridgeSupport712_suffix_002 : List Nat := ridgeSupport712_002 ++ ridgeSupport712_suffix_003
def ridgeSupport712_suffix_001 : List Nat := ridgeSupport712_001 ++ ridgeSupport712_suffix_002
def ridgeSupport712_suffix_000 : List Nat := ridgeSupport712_000 ++ ridgeSupport712_suffix_001
theorem ridgeSupport712_source : candidateSupports 712 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport712_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
