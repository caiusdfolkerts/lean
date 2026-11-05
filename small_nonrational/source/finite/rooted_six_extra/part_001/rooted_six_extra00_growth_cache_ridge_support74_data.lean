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
def ridgeSupport74_000 : List Nat := [5,45,49,50,51,202,205,207,210,212,214,217,219,222,224,226,229,231,234,236,780,782,783,786,788,792,794,795,798,800,804,806]
def ridgeSupport74_001 : List Nat := [807,810,812,852,853,855,856,857,858,860,861,863,864,866,867,873,874,876,877,878,879,881,882,884,885,887,888,894,895,897,898,899]
def ridgeSupport74_002 : List Nat := [900,902,903,905,906,908,909,3112,3113,3114,3115,3116,3117,3118,3119,3124,3125,3130,3131,3136,3137,3138,3139,3140,3141,3142,3143,3148,3149,3154,3155,3160]
def ridgeSupport74_003 : List Nat := [3161,3162,3163,3164,3165,3184,3185,3186,3187,3188,3189,3208,3209,3210,3211,3212,3213,3232,3233,3234,3235,3236,3237,3256,3257,3258,3259,3260,3261,3280,3281,3282]
def ridgeSupport74_004 : List Nat := [3283,3284,3285,3304,3305,3306,3307,3308,3309,3313,3315,3319,3321,3325,3327,3370,3371,3382,3383,3391,3393,3397,3399,3406,3407,3418,3419,3442,3443,3454,3455,3463]
def ridgeSupport74_005 : List Nat := [3465,3469,3471,3478,3479,3490,3491,3514,3515,3526,3527,3535,3537,3541,3543,3550,3551,3562,3563,5176,5177,5188,5189,5212,5213,5224,5225,5239,5241,5245,5247,5248]
def ridgeSupport74_006 : List Nat := [5249,5260,5261,5284,5285,5296,5297,5311,5313,5317,5319,5320,5321,5332,5333,5356,5357,5368,5369,5383,5385,5389,5391,7216,7217,7218,7219,7220,7221,7936,7937,7938]
def ridgeSupport74_007 : List Nat := [7939,7940,7941,7960,7961,7962,7963,7964,7965,7972,7973,7974,7975,7976,7977,7984,7985,7990,7991,8002,8003,8008,8009,8020,8021,8026,8027,8401,8403,8407,8409,8419]
def ridgeSupport74_008 : List Nat := [8421,8425,8427,8437,8439,8443,8445]
def ridgeSupport74_code : Nat := 0x20fd83ee0f783d60eb83a60e5838e0d9835e0d38345f5b7d69f557d51f497d21f437d09f377cd9f317cc1f297ca1f277c99f257c91f1d7c71f1b7c69f197c61f057c11f037c09f017c01c3570d1c3370c9c3170c150f5435509541d4f953e14ed53b14d553514c953214c753154c152fd4b152c14a5529148d5231481520147f51f547951dd46951a145d5171445511143950e0deb37a8ddf3778dd73754dd1373cdc73718dbb36e8da33688d973658d8f3634d89361cd7f35f8d7335c8d5b3568d4f3538d473514d4134fcd3734d8d2b34a8cff33f4cf933dccf333c4ced33b0ceb33a8ce933a0cd53350cd33348cd13340cbd32f0cbb32e8cb932e0ca53290ca33288ca13280c8d3230c8b3228c893220c7531d0c7331c8c7131c0c5d3170c5b3168c593160c533148c4d3130c473118c453110c433108c413100c3b30e8c3530d0c2f30b8c2d30b0c2b30a8c2930a038d0e3038a0e243870e183840e0c3820e0437f0df83780ddc3750dd03720dc436f0db836d0db036a0da43630d883600d7c35d0d7035a0d643580d5c3550d5032c0ca83270c983240c8031e0c6c31a0c603140c4830f0c3830c03b00ea039c0e503880e003780db03640d603500d2033c0cd032803300c803100b4005
def ridgeSupport74_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport74_code
def ridgeSupport74_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport74_code
def ridgeSupport74_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport74_code
def ridgeSupport74_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport74_code
def ridgeSupport74_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport74_code
def ridgeSupport74_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport74_code
def ridgeSupport74_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport74_code
def ridgeSupport74_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport74_code
def ridgeSupport74_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport74_code
def ridgeSupport74_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport74_code
def ridgeSupport74_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 14 263 ridgeSupport74_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
