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
def ridgeSupport456_000 : List Nat := [523,524,525,860,861,862,1125,1126,1127,1549,1550,1551,1633,1634,1635,1727,1728,1729,2876,2877,2882,2883,2888,2889,2896,2898,2902,2904,2908,2910,2924,2925]
def ridgeSupport456_001 : List Nat := [2930,2931,2936,2937,3016,3018,3022,3024,3028,3030,3064,3066,3070,3072,3076,3078,3116,3117,3122,3123,3128,3129,3136,3138,3142,3144,3148,3150,3164,3165,3170,3171]
def ridgeSupport456_002 : List Nat := [3176,3177,3256,3258,3262,3264,3268,3270,3304,3306,3310,3312,3316,3318,3394,3395,3396,3397,3398,3399,3406,3407,3408,3409,3410,3411,3644,3645,3650,3651,3656,3657]
def ridgeSupport456_003 : List Nat := [3664,3666,3670,3672,3676,3678,3692,3693,3698,3699,3704,3705,3784,3786,3790,3792,3796,3798,3832,3834,3838,3840,3844,3846,3922,3923,3924,3925,3926,3927,3934,3935]
def ridgeSupport456_004 : List Nat := [3936,3937,3938,3939,4936,4938,4942,4944,4948,4950,4964,4965,4970,4971,4976,4977,5012,5013,5018,5019,5024,5025,5104,5106,5110,5112,5116,5118,5146,5147,5148,5149]
def ridgeSupport456_005 : List Nat := [5150,5151,5212,5213,5214,5215,5216,5217,5242,5243,5244,5245,5246,5247,5704,5706,5710,5712,5716,5718,5732,5733,5738,5739,5744,5745,5780,5781,5786,5787,5792,5793]
def ridgeSupport456_006 : List Nat := [5872,5874,5878,5880,5884,5886,5914,5915,5916,5917,5918,5919,5980,5981,5982,5983,5984,5985,6010,6011,6012,6013,6014,6015,6808,6809,6810,6811,6812,6813,6820,6821]
def ridgeSupport456_007 : List Nat := [6822,6823,6824,6825,7184,7185,7190,7191,7196,7197,7220,7221,7226,7227,7232,7233,7280,7281,7286,7287,7292,7293,7433,7435,7439,7441,7445,7447,7529,7531,7535,7537]
def ridgeSupport456_008 : List Nat := [7541,7543]
def ridgeSupport456_code : Nat := 0x75ddd7575c5d6f75add69745dd157445d0f742dd0971f5c7c71ddc7671c5c707105c4070edc3a70d5c347075c1c705dc167045c106aa5aa86a9daa66a95aa46a75a9c6a6da9a6a65a985dfd77e5df577c5ded77a5d857605d7d75e5d7575c5c7d71e5c7571c5c6d71a5bf96fc5be16f65bc96f05a856a05a6d69a5a5569459c567059ad66a59956645959654594164e592964851fd47e51f547c51ed47a5185460517d45e517545c507d41e507541c506d41a4ff93fc4fe13f64fc93f04e853a04e6d39a4e553944dc53704dad36a4d953644d593544d4134e4d293483d8cf623d84f603d7cf5e3d5cf563d54f543d4cf523c18f043c00efe3be8ef83b58ed43b40ece3b28ec839e4e7839cce7239b4e6c3978e5c3960e563948e503924e48390ce4238f4e3c354cd523544d50353cd4e351cd463514d44350cd4233d8cf433c0cee33a8ce83318cc43300cbe32e8cb831a4c68318cc623174c5c3138c4c3120c463108c4030e4c3830ccc3230b4c2c3018c043000bfe2fe8bf82f58bd42f40bce2f28bc82de4b782dccb722db4b6c2d78b5c2d60b562d48b502d24b482d0cb422cf4b3c1b046c01afc6631988661183c60e183446711984650d7835d0d7020d083020b
def ridgeSupport456_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport456_code
def ridgeSupport456_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport456_code
def ridgeSupport456_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport456_code
def ridgeSupport456_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport456_code
def ridgeSupport456_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport456_code
def ridgeSupport456_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport456_code
def ridgeSupport456_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport456_code
def ridgeSupport456_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport456_code
def ridgeSupport456_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport456_code
def ridgeSupport456_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport456_code
def ridgeSupport456_suffix_009 : List Nat := []
def ridgeSupport456_suffix_008 : List Nat := ridgeSupport456_008 ++ ridgeSupport456_suffix_009
def ridgeSupport456_suffix_007 : List Nat := ridgeSupport456_007 ++ ridgeSupport456_suffix_008
def ridgeSupport456_suffix_006 : List Nat := ridgeSupport456_006 ++ ridgeSupport456_suffix_007
def ridgeSupport456_suffix_005 : List Nat := ridgeSupport456_005 ++ ridgeSupport456_suffix_006
def ridgeSupport456_suffix_004 : List Nat := ridgeSupport456_004 ++ ridgeSupport456_suffix_005
def ridgeSupport456_suffix_003 : List Nat := ridgeSupport456_003 ++ ridgeSupport456_suffix_004
def ridgeSupport456_suffix_002 : List Nat := ridgeSupport456_002 ++ ridgeSupport456_suffix_003
def ridgeSupport456_suffix_001 : List Nat := ridgeSupport456_001 ++ ridgeSupport456_suffix_002
def ridgeSupport456_suffix_000 : List Nat := ridgeSupport456_000 ++ ridgeSupport456_suffix_001
theorem ridgeSupport456_source : candidateSupports 456 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport456_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
