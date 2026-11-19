module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_code_3 840
cert_ridgeSupport_rest_2 840 000 0
cert_ridgeSupport_rest_2 840 001 448
cert_ridgeSupport_rest_2 840 002 896
cert_ridgeSupport_rest_2 840 003 1344
cert_ridgeSupport_rest_2 840 004 1792
cert_ridgeSupport_rest_2 840 005 2240
cert_ridgeSupport_rest_2 840 006 2688
cert_ridgeSupport_rest_2 840 007 3136
cert_ridgeSupport_rest_2 840 008 3584
cert_ridgeSupport_rest_2 840 009 3612
cert_ridgeSupport_suffix_4 840 009
cert_ridgeSupport_suffix_3 840 008 009
cert_ridgeSupport_suffix_3 840 007 008
cert_ridgeSupport_suffix_3 840 006 007
cert_ridgeSupport_suffix_3 840 005 006
cert_ridgeSupport_suffix_3 840 004 005
cert_ridgeSupport_suffix_3 840 003 004
cert_ridgeSupport_suffix_3 840 002 003
cert_ridgeSupport_suffix_3 840 001 002
cert_ridgeSupport_suffix_3 840 000 001
cert_ridgeSupport_source_3 840 14 258
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
