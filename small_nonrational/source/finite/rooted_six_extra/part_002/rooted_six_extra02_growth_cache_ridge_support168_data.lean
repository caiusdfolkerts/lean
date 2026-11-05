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
def ridgeSupport168_000 : List Nat := [38,68,77,80,81,616,617,619,624,626,651,654,656,659,661,663,666,668,671,673,989,992,993,996,999,1026,1027,1030,1031,1036,1038,1039]
def ridgeSupport168_001 : List Nat := [1042,1043,1048,1145,1147,1148,1150,1151,1153,1155,1156,1158,1159,1162,1163,1166,1168,1169,1171,1172,1174,1176,1177,1179,1180,1183,1184,1209,1210,1212,1213,1214]
def ridgeSupport168_002 : List Nat := [1215,1217,1218,1220,1221,1223,1224,3980,3981,3986,3987,3988,3989,3990,3991,3994,3995,4000,4001,4004,4005,4010,4011,4012,4013,4014,4015,4018,4019,4024,4025,4034]
def ridgeSupport168_003 : List Nat := [4035,4036,4037,4038,4039,4058,4059,4060,4061,4062,4063,4082,4083,4084,4085,4086,4087,4106,4107,4108,4109,4110,4111,4130,4131,4132,4133,4134,4135,4154,4155,4156]
def ridgeSupport168_004 : List Nat := [4157,4158,4159,4175,4177,4178,4179,4180,4181,4182,4183,4185,4188,4191,4194,4240,4241,4252,4253,4257,4260,4263,4266,4276,4277,4288,4289,4312,4313,4324,4325,4329]
def ridgeSupport168_005 : List Nat := [4332,4335,4338,4348,4349,4360,4361,4454,4455,4466,4467,4475,4477,4481,4483,4490,4491,4502,4503,4852,4853,4870,4871,4888,4889,4893,4896,4899,4902,4906,4907,4924]
def ridgeSupport168_006 : List Nat := [4925,4942,4943,4960,4961,4965,4968,4971,4974,4978,4979,5066,5067,5084,5085,5102,5103,5111,5113,5117,5119,5120,5121,5276,5277,5282,5283,5284,5285,5289,5292,5295]
def ridgeSupport168_007 : List Nat := [5298,5309,5311,5324,5329,5330,5335,5344,5346,5714,5715,5716,5717,5718,5719,6386,6387,6388,6389,6390,6391,6407,6409,6410,6411,6412,6413,6419,6421,6422,6423,6424]
def ridgeSupport168_008 : List Nat := [6425,6430,6431,6436,6437,6448,6449,6454,6455,6482,6483,6488,6489,6549,6552,6562,6563,6567,6570,6580,6581,6605,6607,6614,6615]
def ridgeSupport168_code : Nat := 0x19d7ceb673f39b9b5cda66ab34f9a3cd1666332b959cac654f2a5937c9b64c7261925c92647f23d919c8c645f22d915c89e43721990bc85642720f8f7c7b63d71e98f3c79595ecad655b2a594eca54e2a70535e9a54d1a6652fe97b4b2a57d2b29534a5a52528e94549da4e50068013ff9fecfe67ef3ef9f74f767b93cb9e54dce6e536e9b5cda26cb3619b04d3e69d33d99e4cae655326991cc8263b31998c4c1e60d2f597a465e32d18b8c5460e30317d8bdc5ce2e51678b344262110fd87e43ca1df0ec874c3961c90d986c43061810b585a42aa14f0a4850c276139091848418a0bf05c82cc15e0ad05582a414e0a5051827c0fe07d03d81e40ee0750278134096049023811403e01d00d806402e014ff77fb3fd5fe8ff37f93f7dfbcfdd7ee3f6dfb4fc77e33f15f88fc37e13ee5f70fb37d93ebdf5cfad7d63eadf54fa57d23e85f40f9b7cd3e5df2cf957ca3e4df24f8d7c6132098e4c526213089824bf25f12f49784ba25c928093e49c24d926493049624a124c922490247122c914487243121090648123f91f88f847b23c90608264122079038818407203100c8043e71f20f847c03dd1508a7c53829a14b8a545262901470a2c4e427013589a44d00510280134088026
def ridgeSupport168_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport168_code
def ridgeSupport168_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport168_code
def ridgeSupport168_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport168_code
def ridgeSupport168_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport168_code
def ridgeSupport168_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport168_code
def ridgeSupport168_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport168_code
def ridgeSupport168_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport168_code
def ridgeSupport168_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport168_code
def ridgeSupport168_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport168_code
def ridgeSupport168_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport168_code
def ridgeSupport168_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 281 ridgeSupport168_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
