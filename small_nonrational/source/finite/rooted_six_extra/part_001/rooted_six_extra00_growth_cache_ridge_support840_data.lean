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
def ridgeSupport840_000 : List Nat := [565,566,567,902,903,904,1167,1168,1169,1591,1592,1593,1675,1676,1677,1721,1722,1723,2872,2873,2886,2887,2892,2893,2899,2901,2909,2912,2915,2918,2920,2921]
def ridgeSupport840_001 : List Nat := [2934,2935,2940,2941,3019,3021,3029,3032,3035,3038,3067,3069,3077,3080,3083,3086,3112,3113,3126,3127,3132,3133,3139,3141,3149,3152,3155,3158,3160,3161,3174,3175]
def ridgeSupport840_002 : List Nat := [3180,3181,3259,3261,3269,3272,3275,3278,3307,3309,3317,3320,3323,3326,3538,3539,3540,3541,3542,3543,3550,3551,3552,3553,3554,3555,3640,3641,3654,3655,3660,3661]
def ridgeSupport840_003 : List Nat := [3667,3669,3677,3680,3683,3686,3688,3689,3702,3703,3708,3709,3787,3789,3797,3800,3803,3806,3835,3837,3845,3848,3851,3854,4066,4067,4068,4069,4070,4071,4078,4079]
def ridgeSupport840_004 : List Nat := [4080,4081,4082,4083,4939,4941,4949,4952,4955,4958,4960,4961,4974,4975,4980,4981,5008,5009,5022,5023,5028,5029,5107,5109,5117,5120,5123,5126,5134,5135,5136,5137]
def ridgeSupport840_005 : List Nat := [5138,5139,5356,5357,5358,5359,5360,5361,5386,5387,5388,5389,5390,5391,5707,5709,5717,5720,5723,5726,5728,5729,5742,5743,5748,5749,5776,5777,5790,5791,5796,5797]
def ridgeSupport840_006 : List Nat := [5875,5877,5885,5888,5891,5894,5902,5903,5904,5905,5906,5907,6124,6125,6126,6127,6128,6129,6154,6155,6156,6157,6158,6159,6952,6953,6954,6955,6956,6957,6964,6965]
def ridgeSupport840_007 : List Nat := [6966,6967,6968,6969,7180,7181,7194,7195,7200,7201,7216,7217,7230,7231,7236,7237,7276,7277,7290,7291,7296,7297,7434,7436,7444,7449,7450,7455,7530,7532,7540,7545]
def ridgeSupport840_008 : List Nat := [7546,7551]
def ridgeSupport840_code : Nat := 0x75fdd7a75e5d7475b1d6a747dd1a7465d147431d0a7205c8071edc7a71b5c6c7115c4470fdc3e70c5c307085c20706dc1a7035c0c6ce5b386cddb366cd5b346cb5b2c6cadb2a6ca5b28603d80e603580c602d80a5fc57f05fbd7ee5fb57ec5c4d7125c457105c3d70e5c197035c016fd5bd56f35a956a45a7d69e5a4569059d567459bd66e5985660597965b5961655593564b543d50e543550c542d50a53c54f053bd4ee53b54ec504d4125045410503d40e501940350013fd4fd53f34e953a44e7d39e4e453904dd53744dbd36e4d853604d7935b4d613554d3534b3fccff23fc4ff03fbcfee3f9cfe63f94fe43f8cfe23c38f0b3c20f053bf4efb3b78edb3b60ed53b34ecb39f4e7c39dce7639a4e683998e633980e5d3954e533934e4c391ce4638e4e38378cde23784de0377cdde375cdd63754dd4374cdd233f8cfb33e0cf533b4ceb3338ccb3320cc532f4cbb31b4c6c319cc663164c583158c533140c4d3114c4330f4c3c30dcc3630a4c283038c0b3020c052ff4bfb2f78bdb2f60bd52f34bcb2df4b7c2ddcb762da4b682d98b632d80b5d2d54b532d34b4c2d1cb462ce4b381aec6ba1ae468d1a3068b18e463818dc491124048f0e203870e1823708d8235
def ridgeSupport840_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport840_code
def ridgeSupport840_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport840_code
def ridgeSupport840_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport840_code
def ridgeSupport840_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport840_code
def ridgeSupport840_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport840_code
def ridgeSupport840_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport840_code
def ridgeSupport840_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport840_code
def ridgeSupport840_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport840_code
def ridgeSupport840_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport840_code
def ridgeSupport840_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport840_code
def ridgeSupport840_suffix_009 : List Nat := []
def ridgeSupport840_suffix_008 : List Nat := ridgeSupport840_008 ++ ridgeSupport840_suffix_009
def ridgeSupport840_suffix_007 : List Nat := ridgeSupport840_007 ++ ridgeSupport840_suffix_008
def ridgeSupport840_suffix_006 : List Nat := ridgeSupport840_006 ++ ridgeSupport840_suffix_007
def ridgeSupport840_suffix_005 : List Nat := ridgeSupport840_005 ++ ridgeSupport840_suffix_006
def ridgeSupport840_suffix_004 : List Nat := ridgeSupport840_004 ++ ridgeSupport840_suffix_005
def ridgeSupport840_suffix_003 : List Nat := ridgeSupport840_003 ++ ridgeSupport840_suffix_004
def ridgeSupport840_suffix_002 : List Nat := ridgeSupport840_002 ++ ridgeSupport840_suffix_003
def ridgeSupport840_suffix_001 : List Nat := ridgeSupport840_001 ++ ridgeSupport840_suffix_002
def ridgeSupport840_suffix_000 : List Nat := ridgeSupport840_000 ++ ridgeSupport840_suffix_001
theorem ridgeSupport840_source : candidateSupports 840 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport840_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
