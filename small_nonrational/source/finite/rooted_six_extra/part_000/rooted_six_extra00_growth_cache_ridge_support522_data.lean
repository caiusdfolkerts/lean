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
def ridgeSupport522_000 : List Nat := [8,48,51,53,54,227,228,230,235,237,251,252,254,259,261,263,264,266,271,273,803,805,808,809,811,827,829,832,833,835,839,841]
def ridgeSupport522_001 : List Nat := [844,845,847,872,873,875,876,879,880,881,883,884,886,891,892,893,894,896,897,900,901,902,904,905,907,912,913,914,915,917,918,921]
def ridgeSupport522_002 : List Nat := [922,923,925,926,928,933,934,3116,3117,3122,3123,3128,3129,3130,3131,3132,3133,3134,3135,3140,3141,3146,3147,3152,3153,3154,3155,3156,3157,3158,3159,3178]
def ridgeSupport522_003 : List Nat := [3179,3180,3181,3182,3183,3202,3203,3204,3205,3206,3207,3226,3227,3228,3229,3230,3231,3250,3251,3252,3253,3254,3255,3274,3275,3276,3277,3278,3279,3298,3299,3300]
def ridgeSupport522_004 : List Nat := [3301,3302,3303,3304,3306,3310,3312,3316,3318,3322,3323,3324,3325,3326,3327,3446,3447,3458,3459,3460,3462,3466,3468,3482,3483,3494,3495,3518,3519,3530,3531,3532]
def ridgeSupport522_005 : List Nat := [3534,3538,3540,3554,3555,3566,3567,3590,3591,3602,3603,3604,3606,3610,3612,3626,3627,3638,3639,5252,5253,5264,5265,5288,5289,5300,5301,5308,5310,5314,5316,5324]
def ridgeSupport522_006 : List Nat := [5325,5336,5337,5360,5361,5372,5373,5380,5382,5386,5388,5396,5397,5408,5409,5432,5433,5444,5445,5452,5454,5458,5460,7234,7235,7236,7237,7238,7239,7954,7955,7956]
def ridgeSupport522_007 : List Nat := [7957,7958,7959,7960,7962,7966,7968,7970,7971,7972,7974,7978,7980,7982,7983,8006,8007,8012,8013,8024,8025,8030,8031,8042,8043,8048,8049,8416,8418,8422,8424,8434]
def ridgeSupport522_008 : List Nat := [8436,8440,8442,8452,8454,8458,8460]
def ridgeSupport522_code : Nat := 0x210c842a10684120fa83e20f483ca0e8839a0e28381f717dc1f6b7da9f5f7d79f597d61f4d7d31f477d19f2f7cb9f2c7ca9f267c91f237c89f207c79f1a7c61f177c59f157c51f137c49c477119c457111c437109554554954e5531545551153954e15215481515545150c542950654114fd53f14f153c14d953614cd53314c453094be52f14b552d14a952a149152414855210e3738d8e2b38a8e1c3868e163850e133848e073818def37b8de33788dd43748dce3730dcb3728dbf36f8da73698d9b3668d8c3628d863610d833608d7735d8cff33f8cfd33f0cfb33e8cf633d0cf033b8cea33a0ce73398ce53390ce33388ccf3338ccd3330ccb3328cb732d8cb532d0cb332c8c9f3278c9d3270c9b3268c873218c853210c833208c6f31b8c6d31b0c6b31a8c573158c553150c533148c513140c4b3128c453110c3f30f8c3d30f0c3b30e8c3930e0c3330c8c2d30b03a60e943a00e7839d0e6c39a0e643960e543930e483910e4038b0e243880e183850e103810e0037e0df437c0dec3760dd03730dc43700dbc36c0dac3690da034f0d3434c0d243470d0c3410d0033d0cec32b0ca43280c94323044410f0428108041c105040c0fe03f00fb03b40eb03980e4038c03600d403300c0008
def ridgeSupport522_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport522_code
def ridgeSupport522_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport522_code
def ridgeSupport522_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport522_code
def ridgeSupport522_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport522_code
def ridgeSupport522_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport522_code
def ridgeSupport522_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport522_code
def ridgeSupport522_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport522_code
def ridgeSupport522_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport522_code
def ridgeSupport522_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport522_code
def ridgeSupport522_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport522_code
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
    (PackedRawNatGrowth.readList 14 263 ridgeSupport522_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
