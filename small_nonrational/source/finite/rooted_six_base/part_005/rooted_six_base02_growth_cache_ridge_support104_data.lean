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
def ridgeSupport104_000 : List Nat := [37,67,77,78,79,615,618,620,623,625,627,630,632,635,637,639,642,644,647,649,990,991,994,995,1000,1002,1003,1006,1007,1012,1014,1015]
def ridgeSupport104_001 : List Nat := [1018,1019,1024,1146,1147,1149,1150,1151,1152,1154,1155,1157,1158,1160,1161,1167,1168,1170,1171,1172,1173,1175,1176,1178,1179,1181,1182,1188,1189,1191,1192,1193]
def ridgeSupport104_002 : List Nat := [1194,1196,1197,1199,1200,1202,1203,3980,3981,3982,3983,3984,3985,3986,3987,3992,3993,3998,3999,4004,4005,4006,4007,4008,4009,4010,4011,4016,4017,4022,4023,4028]
def ridgeSupport104_003 : List Nat := [4029,4030,4031,4032,4033,4052,4053,4054,4055,4056,4057,4076,4077,4078,4079,4080,4081,4100,4101,4102,4103,4104,4105,4124,4125,4126,4127,4128,4129,4148,4149,4150]
def ridgeSupport104_004 : List Nat := [4151,4152,4153,4172,4173,4174,4175,4176,4177,4181,4183,4187,4189,4193,4195,4238,4239,4250,4251,4259,4261,4265,4267,4274,4275,4286,4287,4310,4311,4322,4323,4331]
def ridgeSupport104_005 : List Nat := [4333,4337,4339,4346,4347,4358,4359,4382,4383,4394,4395,4403,4405,4409,4411,4418,4419,4430,4431,4850,4851,4868,4869,4886,4887,4895,4897,4901,4903,4904,4905,4922]
def ridgeSupport104_006 : List Nat := [4923,4940,4941,4958,4959,4967,4969,4973,4975,4976,4977,4994,4995,5012,5013,5030,5031,5039,5041,5045,5047,5048,5049,6644,6645,6646,6647,6648,6649,6656,6657,6658]
def ridgeSupport104_007 : List Nat := [6659,6660,6661,6668,6669,6670,6671,6672,6673,6692,6693,6694,6695,6696,6697,6716,6717,6718,6719,6720,6721,6725,6727,6731,6733,6737,6739,6740,6741,6742,6743,6744]
def ridgeSupport104_008 : List Nat := [6745,6749,6751,6755,6757,6761,6763,6767,6768,6770,6771,6773,6774,6779,6781,6785,6787,6794,6795,6806,6807,6815,6817,6821,6823,6826,6828,6833,6835,6839,6841,6848]
def ridgeSupport104_009 : List Nat := [6849,6860,6861,6869,6871,6875,6877,6880,6882,6887,6889,6893,6895,6902,6903,6914,6915,6923,6925,6929,6931,6934,6936,7154,7155,7163,7165,7169,7171,7172,7173,7186]
def ridgeSupport104_010 : List Nat := [7188,7190,7191,7199,7201,7208,7209,7217,7219,7223,7225,7226,7227,7240,7242,7244,7245,7253,7255,7262,7263,7271,7273,7277,7279,7280,7281,7294,7296,7298,7299,7307]
def ridgeSupport104_011 : List Nat := [7309,7508,7509,7510,7511,7512,7513,7523,7525,7529,7531,7535,7537,7558,7560,7564,7566,7570,7572,7940,7941,7942,7943,7944,7945]
def ridgeSupport104_code : Nat := 0x1f09f847c1fe0df05f827653b25d8eec67623b0dd71eb7f5afad3d65eb1f567ab1d57eab7557aa9c8de45f20f905c80e3f71c78e1c6fe36f1a78cfc5fe2f715f8abc4de26712b891c3be1d70e786fc33e18f0a7851c21e0ff05f82dc14e097017809c03e00eff77f7bf3df96c6362db13d88ec37617b03d816bdf5edaefd76eba75cfae2d706b775b7ad7d6aeb37599ac1d606ae756fab3d58eab3555aa7d52ea8753fa97d4b6a2f515a83d40e9f74f7a76d3ae9cf4e5a70d37e9af4d3a65d31e97f4bba59d2c695f4ada55d2a694f4a3a4dd25e91f48ba41d2068ff47da3dd1e68a7451a27d136897449a11d08683f41da0dd066817409a03d0168074019f9cfc67df3ed9f5cfa4ee67713b79dacec675f3a79d34e567293839c14dc66e136f9b6cda66cf35f9af4d3669933b99d4ca6651327992cc8663f31798b4c166092f3979453e29d1438a144ee273135899c4ae25511f88f441e20d0fb87d43ce1e30ed875c38e1c50d786b42fe17d0b385942ae1530a5851c26e13508f847418e0c305d82dc15e0ab051828413e09d04d82640e607103781b40d6069021810407e03d01d80e40260110078034016008ff17f83fbdfdcfed7f63f65fb0fd77eb3f55fa8fc17e03efdf7cfbd7de3eddf6cfb17d83eadf54fa97d43e9df4cfa57d23e7df3cf997cc3e4df24f917c83e3df1cf8d7c612cc9644b025792b49584aa25492a094e4a5252127893a49b24d126092e49524a124c9244902479224910486242920c90448023f91f88fa47b23d10007f63fa1fb8fd87e83ef1f70fac7d43e81f18f887be3de1448a1c50828213f89f44f627813b09cc4e226f13609a84ce04f0270134086025
def ridgeSupport104_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport104_code
def ridgeSupport104_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport104_code
def ridgeSupport104_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport104_code
def ridgeSupport104_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport104_code
def ridgeSupport104_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport104_code
def ridgeSupport104_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport104_code
def ridgeSupport104_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport104_code
def ridgeSupport104_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport104_code
def ridgeSupport104_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport104_code
def ridgeSupport104_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport104_code
def ridgeSupport104_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport104_code
def ridgeSupport104_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport104_code
def ridgeSupport104_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport104_code
def ridgeSupport104_suffix_012 : List Nat := []
def ridgeSupport104_suffix_011 : List Nat := ridgeSupport104_011 ++ ridgeSupport104_suffix_012
def ridgeSupport104_suffix_010 : List Nat := ridgeSupport104_010 ++ ridgeSupport104_suffix_011
def ridgeSupport104_suffix_009 : List Nat := ridgeSupport104_009 ++ ridgeSupport104_suffix_010
def ridgeSupport104_suffix_008 : List Nat := ridgeSupport104_008 ++ ridgeSupport104_suffix_009
def ridgeSupport104_suffix_007 : List Nat := ridgeSupport104_007 ++ ridgeSupport104_suffix_008
def ridgeSupport104_suffix_006 : List Nat := ridgeSupport104_006 ++ ridgeSupport104_suffix_007
def ridgeSupport104_suffix_005 : List Nat := ridgeSupport104_005 ++ ridgeSupport104_suffix_006
def ridgeSupport104_suffix_004 : List Nat := ridgeSupport104_004 ++ ridgeSupport104_suffix_005
def ridgeSupport104_suffix_003 : List Nat := ridgeSupport104_003 ++ ridgeSupport104_suffix_004
def ridgeSupport104_suffix_002 : List Nat := ridgeSupport104_002 ++ ridgeSupport104_suffix_003
def ridgeSupport104_suffix_001 : List Nat := ridgeSupport104_001 ++ ridgeSupport104_suffix_002
def ridgeSupport104_suffix_000 : List Nat := ridgeSupport104_000 ++ ridgeSupport104_suffix_001
theorem ridgeSupport104_source : candidateSupports 104 =
    (PackedRawNatGrowth.readList 13 377 ridgeSupport104_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
