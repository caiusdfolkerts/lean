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
def ridgeSupport104_000 : List Nat := [37,67,77,78,79,615,618,620,623,625,627,630,632,635,637,639,642,644,647,649,990,991,994,995,1000,1002,1003,1006,1007,1012,1014,1015]
def ridgeSupport104_001 : List Nat := [1018,1019,1024,1146,1147,1149,1150,1151,1152,1154,1155,1157,1158,1160,1161,1167,1168,1170,1171,1172,1173,1175,1176,1178,1179,1181,1182,1188,1189,1191,1192,1193]
def ridgeSupport104_002 : List Nat := [1194,1196,1197,1199,1200,1202,1203,3980,3981,3982,3983,3984,3985,3986,3987,3992,3993,3998,3999,4004,4005,4006,4007,4008,4009,4010,4011,4016,4017,4022,4023,4028]
def ridgeSupport104_003 : List Nat := [4029,4030,4031,4032,4033,4052,4053,4054,4055,4056,4057,4076,4077,4078,4079,4080,4081,4100,4101,4102,4103,4104,4105,4124,4125,4126,4127,4128,4129,4148,4149,4150]
def ridgeSupport104_004 : List Nat := [4151,4152,4153,4172,4173,4174,4175,4176,4177,4181,4183,4187,4189,4193,4195,4238,4239,4250,4251,4259,4261,4265,4267,4274,4275,4286,4287,4310,4311,4322,4323,4331]
def ridgeSupport104_005 : List Nat := [4333,4337,4339,4346,4347,4358,4359,4382,4383,4394,4395,4403,4405,4409,4411,4418,4419,4430,4431,4850,4851,4868,4869,4886,4887,4895,4897,4901,4903,4904,4905,4922]
def ridgeSupport104_006 : List Nat := [4923,4940,4941,4958,4959,4967,4969,4973,4975,4976,4977,4994,4995,5012,5013,5030,5031,5039,5041,5045,5047,5048,5049,5276,5277,5278,5279,5280,5281,5291,5293,5297]
def ridgeSupport104_007 : List Nat := [5299,5303,5305,5326,5328,5332,5334,5338,5340,5708,5709,5710,5711,5712,5713,6380,6381,6382,6383,6384,6385,6404,6405,6406,6407,6408,6409,6416,6417,6418,6419,6420]
def ridgeSupport104_008 : List Nat := [6421,6428,6429,6434,6435,6446,6447,6452,6453,6464,6465,6470,6471,6551,6553,6560,6561,6569,6571,6578,6579,6587,6589,6596,6597]
def ridgeSupport104_code : Nat := 0x19c5ce266f73779b3cd966af3539a1cd0666732f947ca36507281935c9a64bf25d923c916477239915c8a644f225911c886427211907c8364172098f1c7863bf1dd8edc765946ca164fb275936c994dca6d535a9a94d0a6752e696f4b3a58d2b69574a1a50527e93d49da4e4ee67713b79dacec675f3a79d34e567293839c14dc66e136f9b6cda66cf35f9af4d3669933b99d4ca6651327992cc8663f31798b4c166092f3979453e29d1438a144ee273135899c4ae25511f88f441e20d0fb87d43ce1e30ed875c38e1c50d786b42fe17d0b385942ae1530a5851c26e13508f847418e0c305d82dc15e0ab051828413e09d04d82640e607103781b40d6069021810407e03d01d80e40260110078034016008ff17f83fbdfdcfed7f63f65fb0fd77eb3f55fa8fc17e03efdf7cfbd7de3eddf6cfb17d83eadf54fa97d43e9df4cfa57d23e7df3cf997cc3e4df24f917c83e3df1cf8d7c612cc9644b025792b49584aa25492a094e4a5252127893a49b24d126092e49524a124c9244902479224910486242920c90448023f91f88fa47b23d10007f63fa1fb8fd87e83ef1f70fac7d43e81f18f887be3de1448a1c50828213f89f44f627813b09cc4e226f13609a84ce04f0270134086025
def ridgeSupport104_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport104_code
def ridgeSupport104_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport104_code
def ridgeSupport104_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport104_code
def ridgeSupport104_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport104_code
def ridgeSupport104_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport104_code
def ridgeSupport104_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport104_code
def ridgeSupport104_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport104_code
def ridgeSupport104_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport104_code
def ridgeSupport104_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport104_code
def ridgeSupport104_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport104_code
def ridgeSupport104_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 281 ridgeSupport104_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
