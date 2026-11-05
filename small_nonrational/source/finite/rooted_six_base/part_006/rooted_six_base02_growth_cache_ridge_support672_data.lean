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
def ridgeSupport672_000 : List Nat := [51,81,91,98,100,663,664,665,666,673,674,793,794,795,798,799,804,805,810,812,834,836,838,840,842,847,848,850,853,1037,1038,1039]
def ridgeSupport672_001 : List Nat := [1040,1047,1048,1167,1168,1169,1172,1173,1178,1179,1184,1186,1208,1210,1212,1214,1216,1221,1222,1224,1227,1276,1277,1278,1281,1282,1287,1288,1293,1295,1317,1319]
def ridgeSupport672_002 : List Nat := [1321,1323,1325,1330,1331,1333,1336,1363,1365,1367,1369,1370,1372,1374,1375,1379,1381,1386,1387,3740,3745,3754,3756,3822,3823,3832,3833,3838,3839,3842,3844,3848]
def ridgeSupport672_003 : List Nat := [3849,3855,3858,3870,3871,3880,3881,3908,3913,3918,3919,3922,3924,3928,3929,3934,3935,3944,3945,3958,3959,3968,3969,3980,3985,3994,3996,4062,4063,4072,4073,4078]
def ridgeSupport672_004 : List Nat := [4079,4082,4084,4088,4089,4095,4098,4110,4111,4120,4121,4148,4153,4158,4159,4162,4164,4168,4169,4174,4175,4184,4185,4198,4199,4208,4209,4300,4302,4312,4314,4328]
def ridgeSupport672_005 : List Nat := [4329,4340,4341,4442,4447,4454,4459,4474,4475,4486,4487,4508,4513,4522,4524,4590,4591,4600,4601,4606,4607,4610,4612,4616,4617,4623,4626,4638,4639,4648,4649,4676]
def ridgeSupport672_006 : List Nat := [4681,4686,4687,4690,4692,4696,4697,4702,4703,4712,4713,4726,4727,4736,4737,4812,4813,4820,4821,4924,4926,4936,4938,4952,4953,4964,4965,5066,5071,5078,5083,5098]
def ridgeSupport672_007 : List Nat := [5099,5110,5111,6512,6517,6518,6522,6538,6539,6542,6544,6548,6549,6555,6558,6570,6571,6580,6581,6586,6587,6596,6597,6608,6613,6618,6619,6622,6624,6628,6629,6632]
def ridgeSupport672_008 : List Nat := [6634,6638,6639,6644,6649,6650,6654,6670,6671,6674,6676,6680,6681,6687,6690,6702,6703,6712,6713,6718,6719,6728,6729,6740,6745,6750,6751,6754,6756,6760,6761,6764]
def ridgeSupport672_009 : List Nat := [6766,6770,6771,6830,6831,6838,6840,6842,6843,6850,6852,6866,6867,6878,6879,6940,6941,6944,6949,6952,6953,6956,6961,6976,6977,6988,6989,6992,6997,6998,7002,7018]
def ridgeSupport672_010 : List Nat := [7019,7022,7024,7028,7029,7035,7038,7050,7051,7060,7061,7066,7067,7076,7077,7088,7093,7098,7099,7102,7104,7108,7109,7112,7114,7118,7119,7140,7141,7202,7203,7210]
def ridgeSupport672_011 : List Nat := [7212,7214,7215,7222,7224,7238,7239,7250,7251,7312,7313,7316,7321,7324,7325,7328,7333,7348,7349,7360,7361,7496,7501,7502,7506,7508,7513,7514,7518,7526,7527,7540]
def ridgeSupport672_012 : List Nat := [7541,7544,7549,7550,7554,7562,7563,7576,7577,7930,7931,7966,7967,8026,8027]
def ridgeSupport672_code : Nat := 0x7d6feb5f1ff8f7befdf5d99ecc762fb15d82ebf75f7af1d75eba759facdd5eead7567aa9d52ea77537a91cc1e6072d7969ca5e507277939c99e4a7247921c53e29711f88dc38e1b70bf85dc2ce15708f845be5df26f3f79dbcade46f17789bc0ddf6eef775bb5dd86e97749b9bdcd6e57729b8bdc56dfb6f7b75dba6dc36ddb6bdb56d6b6adb55da86d37699b41da06cc7659b29d946c97641b1dd8e6b7f5bdad3d696b13585abbd5d6ae356daafd5769cf4e5a6ed3669a74d1a64d31697f4bda59d2a6927491a3fd1f68e7471a2fd17688b43fa19d0c6853425a0fd0767fb3f59f9cfa67bf3dd9eacf467973c99e0cef676f3b59d5ce867173899bbcdd66d73699abcd5667b337995cca664331d98bcc565eb2ed975cb84fde7ed3eb9f54f6e7ad3cf9e54d966c93599ac4d2a69133e99e4b565a92cd9664a0650127793b49a64d125f92f49664b1254929493e49d24992248a645121f90f484a41f20990448124051ff8ff47e63f11ef8f746b23551a18ce461e30d17b8bd45ae2cd15f8ad43d61e90e9874436a1b10ce86641c60e106783341660b104f827412609104482140fe07d03981a406603100f8074009ffeff97fc3fd1fe4fef7f73fa5fd0fdf7ef3e71f34f917c63e05f00f777bb3da5ed0f5f7af3d65eb0f547a93d3de9cf497a23ca5e50f1f78f3c49e1ef097843c11e04eff77f3be5df0eef7773ab1d54ea174e15acad45652b1957cabc55c2ad1564aae5552a994e0a6a53329914b4a565292939494a1e50d284141ca0450127f13f49f84cb264131898a4c025f12f09744b8251128093649a24a9250922490247906082e410207903881a3551a90d4069e34a1a40d186883421960ca864a32418f8c7863631a18c8a8854229a14c8a6052e064031016c0a2033
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
def ridgeSupport672_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport672_code
def ridgeSupport672_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport672_code
def ridgeSupport672_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport672_code
def ridgeSupport672_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport672_code
def ridgeSupport672_suffix_013 : List Nat := []
def ridgeSupport672_suffix_012 : List Nat := ridgeSupport672_012 ++ ridgeSupport672_suffix_013
def ridgeSupport672_suffix_011 : List Nat := ridgeSupport672_011 ++ ridgeSupport672_suffix_012
def ridgeSupport672_suffix_010 : List Nat := ridgeSupport672_010 ++ ridgeSupport672_suffix_011
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
    (PackedRawNatGrowth.readList 13 399 ridgeSupport672_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
