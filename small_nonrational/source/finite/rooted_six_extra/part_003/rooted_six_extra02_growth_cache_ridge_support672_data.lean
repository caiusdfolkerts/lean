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
def ridgeSupport672_000 : List Nat := [51,81,91,98,100,663,664,665,666,673,674,793,794,795,798,799,804,805,810,812,834,836,838,840,842,847,848,850,853,1037,1038,1039]
def ridgeSupport672_001 : List Nat := [1040,1047,1048,1167,1168,1169,1172,1173,1178,1179,1184,1186,1208,1210,1212,1214,1216,1221,1222,1224,1227,1276,1277,1278,1281,1282,1287,1288,1293,1295,1317,1319]
def ridgeSupport672_002 : List Nat := [1321,1323,1325,1330,1331,1333,1336,1363,1365,1367,1369,1370,1372,1374,1375,1379,1381,1386,1387,3740,3745,3754,3756,3822,3823,3832,3833,3838,3839,3842,3844,3848]
def ridgeSupport672_003 : List Nat := [3849,3855,3858,3870,3871,3880,3881,3908,3913,3918,3919,3922,3924,3928,3929,3934,3935,3944,3945,3958,3959,3968,3969,3980,3985,3994,3996,4062,4063,4072,4073,4078]
def ridgeSupport672_004 : List Nat := [4079,4082,4084,4088,4089,4095,4098,4110,4111,4120,4121,4148,4153,4158,4159,4162,4164,4168,4169,4174,4175,4184,4185,4198,4199,4208,4209,4300,4302,4312,4314,4328]
def ridgeSupport672_005 : List Nat := [4329,4340,4341,4442,4447,4454,4459,4474,4475,4486,4487,4508,4513,4522,4524,4590,4591,4600,4601,4606,4607,4610,4612,4616,4617,4623,4626,4638,4639,4648,4649,4676]
def ridgeSupport672_006 : List Nat := [4681,4686,4687,4690,4692,4696,4697,4702,4703,4712,4713,4726,4727,4736,4737,4812,4813,4820,4821,4924,4926,4936,4938,4952,4953,4964,4965,5066,5071,5078,5083,5098]
def ridgeSupport672_007 : List Nat := [5099,5110,5111,5264,5269,5270,5274,5276,5281,5282,5286,5294,5295,5308,5309,5312,5317,5318,5322,5330,5331,5344,5345,5698,5699,5734,5735,5794,5795,6342,6343,6352]
def ridgeSupport672_008 : List Nat := [6353,6357,6358,6359,6360,6365,6366,6390,6391,6400,6401,6405,6406,6407,6408,6413,6414,6446,6447,6449,6451,6483,6484,6485,6486,6510,6511,6520,6521,6525,6526,6527]
def ridgeSupport672_009 : List Nat := [6528,6533,6534,6566,6567,6569,6571,6603,6604,6605,6606]
def ridgeSupport672_code : Nat := 0x673b39b9ccce5e6af3539a7cd3661b30b980cbfe5fb2fb979cbc65bf2dd956caae5532a7933c98e4bf25d90ec86e42320f906c82e4072018f7c7b637b1bb8d8c6be35b1ab8d1c68631f18d6a3b51599eccd643b2153869c14d3a69532a98d4c5a6052f69794afa57529a9454a1a4e526a92d495a484fde7ed3eb9f54f6e7ad3cf9e54d966c93599ac4d2a69133e99e4b565a92cd9664a0650127793b49a64d125f92f49664b1254929493e49d24992248a645121f90f484a41f20990448124051ff8ff47e63f11ef8f746b23551a18ce461e30d17b8bd45ae2cd15f8ad43d61e90e9874436a1b10ce86641c60e106783341660b104f827412609104482140fe07d03981a406603100f8074009ffeff97fc3fd1fe4fef7f73fa5fd0fdf7ef3e71f34f917c63e05f00f777bb3da5ed0f5f7af3d65eb0f547a93d3de9cf497a23ca5e50f1f78f3c49e1ef097843c11e04eff77f3be5df0eef7773ab1d54ea174e15acad45652b1957cabc55c2ad1564aae5552a994e0a6a53329914b4a565292939494a1e50d284141ca0450127f13f49f84cb264131898a4c025f12f09744b8251128093649a24a9250922490247906082e410207903881a3551a90d4069e34a1a40d186883421960ca864a32418f8c7863631a18c8a8854229a14c8a6052e064031016c0a2033
def ridgeSupport672_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport672_code
def ridgeSupport672_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport672_code
def ridgeSupport672_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport672_code
def ridgeSupport672_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport672_code
def ridgeSupport672_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport672_code
def ridgeSupport672_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport672_code
def ridgeSupport672_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport672_code
def ridgeSupport672_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport672_code
def ridgeSupport672_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport672_code
def ridgeSupport672_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport672_code
def ridgeSupport672_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport672_code
def ridgeSupport672_suffix_010 : List Nat := []
def ridgeSupport672_suffix_009 : List Nat := ridgeSupport672_009 ++ ridgeSupport672_suffix_010
def ridgeSupport672_suffix_008 : List Nat := ridgeSupport672_008 ++ ridgeSupport672_suffix_009
def ridgeSupport672_suffix_007 : List Nat := ridgeSupport672_007 ++ ridgeSupport672_suffix_008
def ridgeSupport672_suffix_006 : List Nat := ridgeSupport672_006 ++ ridgeSupport672_suffix_007
def ridgeSupport672_suffix_005 : List Nat := ridgeSupport672_005 ++ ridgeSupport672_suffix_006
def ridgeSupport672_suffix_004 : List Nat := ridgeSupport672_004 ++ ridgeSupport672_suffix_005
def ridgeSupport672_suffix_003 : List Nat := ridgeSupport672_003 ++ ridgeSupport672_suffix_004
def ridgeSupport672_suffix_002 : List Nat := ridgeSupport672_002 ++ ridgeSupport672_suffix_003
def ridgeSupport672_suffix_001 : List Nat := ridgeSupport672_001 ++ ridgeSupport672_suffix_002
def ridgeSupport672_suffix_000 : List Nat := ridgeSupport672_000 ++ ridgeSupport672_suffix_001
theorem ridgeSupport672_source : candidateSupports 672 =
    (PackedRawNatGrowth.readList 13 299 ridgeSupport672_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
