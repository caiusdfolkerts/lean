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
def ridgeSupport168_000 : List Nat := [38,68,77,80,81,616,617,619,624,626,651,654,656,659,661,663,666,668,671,673,989,992,993,996,999,1026,1027,1030,1031,1036,1038,1039]
def ridgeSupport168_001 : List Nat := [1042,1043,1048,1145,1147,1148,1150,1151,1153,1155,1156,1158,1159,1162,1163,1166,1168,1169,1171,1172,1174,1176,1177,1179,1180,1183,1184,1209,1210,1212,1213,1214]
def ridgeSupport168_002 : List Nat := [1215,1217,1218,1220,1221,1223,1224,3980,3981,3986,3987,3988,3989,3990,3991,3994,3995,4000,4001,4004,4005,4010,4011,4012,4013,4014,4015,4018,4019,4024,4025,4034]
def ridgeSupport168_003 : List Nat := [4035,4036,4037,4038,4039,4058,4059,4060,4061,4062,4063,4082,4083,4084,4085,4086,4087,4106,4107,4108,4109,4110,4111,4130,4131,4132,4133,4134,4135,4154,4155,4156]
def ridgeSupport168_004 : List Nat := [4157,4158,4159,4175,4177,4178,4179,4180,4181,4182,4183,4185,4188,4191,4194,4240,4241,4252,4253,4257,4260,4263,4266,4276,4277,4288,4289,4312,4313,4324,4325,4329]
def ridgeSupport168_005 : List Nat := [4332,4335,4338,4348,4349,4360,4361,4454,4455,4466,4467,4475,4477,4481,4483,4490,4491,4502,4503,4852,4853,4870,4871,4888,4889,4893,4896,4899,4902,4906,4907,4924]
def ridgeSupport168_006 : List Nat := [4925,4942,4943,4960,4961,4965,4968,4971,4974,4978,4979,5066,5067,5084,5085,5102,5103,5111,5113,5117,5119,5120,5121,6644,6645,6650,6651,6652,6653,6656,6657,6662]
def ridgeSupport168_007 : List Nat := [6663,6664,6665,6674,6675,6676,6677,6678,6679,6698,6699,6700,6701,6702,6703,6719,6721,6722,6723,6724,6725,6726,6727,6729,6732,6735,6738,6743,6745,6746,6747,6748]
def ridgeSupport168_008 : List Nat := [6749,6750,6751,6753,6756,6759,6762,6764,6765,6770,6772,6773,6775,6777,6780,6783,6786,6796,6797,6808,6809,6813,6816,6819,6822,6824,6829,6831,6834,6837,6840,6850]
def ridgeSupport168_009 : List Nat := [6851,6862,6863,6867,6870,6873,6876,6878,6883,6941,6943,6947,6949,6956,6957,6968,6969,6977,6979,6983,6985,6988,6990,7156,7157,7161,7164,7167,7170,7174,7175,7184]
def ridgeSupport168_010 : List Nat := [7189,7192,7193,7197,7200,7210,7211,7215,7218,7221,7224,7228,7229,7238,7243,7246,7247,7251,7254,7316,7317,7325,7327,7331,7333,7334,7335,7348,7350,7352,7353,7361]
def ridgeSupport168_011 : List Nat := [7363,7508,7509,7514,7515,7516,7517,7521,7524,7527,7530,7541,7543,7556,7561,7562,7567,7576,7578,7946,7947,7948,7949,7950,7951]
def ridgeSupport168_code : Nat := 0x1f0ff877c37e19f0bf85766bb31d8fec57627b09d77ebaf5abacfd64eb0f577ab9d5bead7557aa9cc3e60f2e7971cb6e5a729f94dca5e51f27f93bc95e4a715b8a7c4fe27712f88dc3de1e70e386bc32e17f0af855c20e0ef067831c15e08701f80dc02dffeff37f3bf5dfa6d3b699b49da3ed0f683b39d9c6cb7659b25d91ec7f63bae3d6f6b735b3ad6d69eb3f59dac3d616ae356bab2d57eab7551aa6d51ea8353ba99d4c6a37519a82d3fe9f34f3a77d3ae9d34e5a6dd3669ab4cfa64d30e97f4bda5dd2e696f4b5a59d2be94b49fa4cd24e91f48da45d22690f485a41d1fe8bf45da2dd1668af455a17d0b6857429a13d096827411a07d0368074019fdcfe67ef3f59f5cfa50068013ff9fecfe67ef3ef9f74f767b93cb9e54dce6e536e9b5cda26cb3619b04d3e69d33d99e4cae655326991cc8263b31998c4c1e60d2f597a465e32d18b8c5460e30317d8bdc5ce2e51678b344262110fd87e43ca1df0ec874c3961c90d986c43061810b585a42aa14f0a4850c276139091848418a0bf05c82cc15e0ad05582a414e0a5051827c0fe07d03d81e40ee0750278134096049023811403e01d00d806402e014ff77fb3fd5fe8ff37f93f7dfbcfdd7ee3f6dfb4fc77e33f15f88fc37e13ee5f70fb37d93ebdf5cfad7d63eadf54fa57d23e85f40f9b7cd3e5df2cf957ca3e4df24f8d7c6132098e4c526213089824bf25f12f49784ba25c928093e49c24d926493049624a124c922490247122c914487243121090648123f91f88f847b23c90608264122079038818407203100c8043e71f20f847c03dd1508a7c53829a14b8a545262901470a2c4e427013589a44d00510280134088026
def ridgeSupport168_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport168_code
def ridgeSupport168_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport168_code
def ridgeSupport168_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport168_code
def ridgeSupport168_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport168_code
def ridgeSupport168_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport168_code
def ridgeSupport168_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport168_code
def ridgeSupport168_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport168_code
def ridgeSupport168_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport168_code
def ridgeSupport168_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport168_code
def ridgeSupport168_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport168_code
def ridgeSupport168_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport168_code
def ridgeSupport168_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport168_code
def ridgeSupport168_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport168_code
def ridgeSupport168_suffix_012 : List Nat := []
def ridgeSupport168_suffix_011 : List Nat := ridgeSupport168_011 ++ ridgeSupport168_suffix_012
def ridgeSupport168_suffix_010 : List Nat := ridgeSupport168_010 ++ ridgeSupport168_suffix_011
def ridgeSupport168_suffix_009 : List Nat := ridgeSupport168_009 ++ ridgeSupport168_suffix_010
def ridgeSupport168_suffix_008 : List Nat := ridgeSupport168_008 ++ ridgeSupport168_suffix_009
def ridgeSupport168_suffix_007 : List Nat := ridgeSupport168_007 ++ ridgeSupport168_suffix_008
def ridgeSupport168_suffix_006 : List Nat := ridgeSupport168_006 ++ ridgeSupport168_suffix_007
def ridgeSupport168_suffix_005 : List Nat := ridgeSupport168_005 ++ ridgeSupport168_suffix_006
def ridgeSupport168_suffix_004 : List Nat := ridgeSupport168_004 ++ ridgeSupport168_suffix_005
def ridgeSupport168_suffix_003 : List Nat := ridgeSupport168_003 ++ ridgeSupport168_suffix_004
def ridgeSupport168_suffix_002 : List Nat := ridgeSupport168_002 ++ ridgeSupport168_suffix_003
def ridgeSupport168_suffix_001 : List Nat := ridgeSupport168_001 ++ ridgeSupport168_suffix_002
def ridgeSupport168_suffix_000 : List Nat := ridgeSupport168_000 ++ ridgeSupport168_suffix_001
theorem ridgeSupport168_source : candidateSupports 168 =
    (PackedRawNatGrowth.readList 13 377 ridgeSupport168_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
