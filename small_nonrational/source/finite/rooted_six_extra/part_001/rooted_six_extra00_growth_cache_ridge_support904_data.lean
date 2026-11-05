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
def ridgeSupport904_000 : List Nat := [586,587,588,923,924,925,1188,1189,1190,1612,1613,1614,1696,1697,1698,1718,1719,1720,2878,2879,2884,2885,2890,2891,2905,2907,2911,2913,2917,2919,2926,2927]
def ridgeSupport904_001 : List Nat := [2932,2933,2938,2939,3025,3027,3031,3033,3037,3039,3073,3075,3079,3081,3085,3087,3118,3119,3124,3125,3130,3131,3145,3147,3151,3153,3157,3159,3166,3167,3172,3173]
def ridgeSupport904_002 : List Nat := [3178,3179,3265,3267,3271,3273,3277,3279,3313,3315,3319,3321,3325,3327,3610,3611,3612,3613,3614,3615,3622,3623,3624,3625,3626,3627,3646,3647,3652,3653,3658,3659]
def ridgeSupport904_003 : List Nat := [3673,3675,3679,3681,3685,3687,3694,3695,3700,3701,3706,3707,3793,3795,3799,3801,3805,3807,3841,3843,3847,3849,3853,3855,4138,4139,4140,4141,4142,4143,4150,4151]
def ridgeSupport904_004 : List Nat := [4152,4153,4154,4155,4945,4947,4951,4953,4957,4959,4966,4967,4972,4973,4978,4979,5014,5015,5020,5021,5026,5027,5113,5115,5119,5121,5125,5127,5128,5129,5130,5131]
def ridgeSupport904_005 : List Nat := [5132,5133,5428,5429,5430,5431,5432,5433,5458,5459,5460,5461,5462,5463,5713,5715,5719,5721,5725,5727,5734,5735,5740,5741,5746,5747,5782,5783,5788,5789,5794,5795]
def ridgeSupport904_006 : List Nat := [5881,5883,5887,5889,5893,5895,5896,5897,5898,5899,5900,5901,6196,6197,6198,6199,6200,6201,6226,6227,6228,6229,6230,6231,7024,7025,7026,7027,7028,7029,7036,7037]
def ridgeSupport904_007 : List Nat := [7038,7039,7040,7041,7186,7187,7192,7193,7198,7199,7222,7223,7228,7229,7234,7235,7282,7283,7288,7289,7294,7295,7440,7442,7446,7448,7452,7454,7536,7538,7542,7544]
def ridgeSupport904_008 : List Nat := [7548,7550]
def ridgeSupport904_code : Nat := 0x75f9d7c75e1d7675c9d707479d1c7461d167449d1071fdc7e71e5c7871cdc72710dc4270f5c3c70ddc36707dc1e7065c18704dc126e05b806dfdb7e6df5b7c6dd5b746dcdb726dc5b70615d8566155854614d85260e583860dd83660d58345c3570c5c2d70a5c257085c1d7055c056ff5bed6f95a8d6a25a7569c5a5d69659cd67259b566c599d666597d65d5965657594d651555d5565555554554d55254e553854dd53654d5534503540c502d40a5025408501d40550053ff4fed3f94e8d3a24e7539c4e5d3964dcd3724db536c4d9d3664d7d35d4d653574d4d35140ed03a40e503840dd03640bd02e40b502c40ad02a3c3cf0d3c24f073c0cf013b7cedd3b64ed73b4ced139ece7a39d4e7439bce6e399ce653984e5f396ce59392ce4a3914e4438fce3e38ace2a38a4e28389ce26387ce1e3874e1c386ce1a33fccfd33e4cf733cccf1333cccd3324cc7330ccc131acc6a3194c64317cc5e315cc553144c4f312cc4930ecc3a30d4c3430bcc2e303cc0d3024c07300cc012f7cbdd2f64bd72f4cbd12decb7a2dd4b742dbcb6e2d9cb652d84b5f2d6cb592d2cb4a2d14b442cfcb3e1ae06b71ad86a21a846a0193864d19304a612944a40e7439c0e6c24c092c24a
def ridgeSupport904_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport904_code
def ridgeSupport904_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport904_code
def ridgeSupport904_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport904_code
def ridgeSupport904_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport904_code
def ridgeSupport904_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport904_code
def ridgeSupport904_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport904_code
def ridgeSupport904_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport904_code
def ridgeSupport904_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport904_code
def ridgeSupport904_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport904_code
def ridgeSupport904_rest_009 : Nat := PackedRawNatGrowth.drop 3612 ridgeSupport904_code
def ridgeSupport904_suffix_009 : List Nat := []
def ridgeSupport904_suffix_008 : List Nat := ridgeSupport904_008 ++ ridgeSupport904_suffix_009
def ridgeSupport904_suffix_007 : List Nat := ridgeSupport904_007 ++ ridgeSupport904_suffix_008
def ridgeSupport904_suffix_006 : List Nat := ridgeSupport904_006 ++ ridgeSupport904_suffix_007
def ridgeSupport904_suffix_005 : List Nat := ridgeSupport904_005 ++ ridgeSupport904_suffix_006
def ridgeSupport904_suffix_004 : List Nat := ridgeSupport904_004 ++ ridgeSupport904_suffix_005
def ridgeSupport904_suffix_003 : List Nat := ridgeSupport904_003 ++ ridgeSupport904_suffix_004
def ridgeSupport904_suffix_002 : List Nat := ridgeSupport904_002 ++ ridgeSupport904_suffix_003
def ridgeSupport904_suffix_001 : List Nat := ridgeSupport904_001 ++ ridgeSupport904_suffix_002
def ridgeSupport904_suffix_000 : List Nat := ridgeSupport904_000 ++ ridgeSupport904_suffix_001
theorem ridgeSupport904_source : candidateSupports 904 =
    (PackedRawNatGrowth.readList 14 258 ridgeSupport904_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
