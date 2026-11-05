module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport56_000 : List Nat := [0,81,82,83,84,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253]
def ridgeSupport56_001 : List Nat := [1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285]
def ridgeSupport56_002 : List Nat := [1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,4182,4183,4184,4185,4186,4187,4188,4189,4190,4191,4192,4193,4194,4195,4196,4197,4198,4199,4200]
def ridgeSupport56_003 : List Nat := [4201,4202,4203,4204,4205,4206,4207,4208,4209,4210,4211,4212,4213,4214,4215,4216,4217,4218,4219,4220,4221,4222,4223,4224,4225,4226,4227,4228,4229,4230,4231,4232]
def ridgeSupport56_004 : List Nat := [4233,4234,4235,4236,4237,4238,4239,4240,4241,4242,4243,4244,4245,4246,4247,4248,4249,4250,4251,4252,4253,4254,4255,4256,4257,4258,4259,4260,4261,4262,4263,4264]
def ridgeSupport56_005 : List Nat := [4265,4266,4267,4268,4269,4270,4271,4272,4273,4274,4275,4276,4277,4278,4279,4280,4281,4282,4283,4284,4285,4286,4287,4288,4289,4290,4291,4292,4293,4294,4295,4296]
def ridgeSupport56_006 : List Nat := [4297,4298,4299,4300,4301,4302,4303,4304,4305,4306,4307,4308,4309,4310,4311,4312,4313,4314,4315,4316,4317,4318,4319,4320,4321,4322,4323,4324,4325,4326,4327,4328]
def ridgeSupport56_007 : List Nat := [4329,4330,4331,4332,4333,4334,4335,4336,4337,4338,4339,4340,4341,4342,4343,4344,4345,4346,4347,4348,4349,4350,4351,4352,4353,4354,4355,4356,4357,4358,4359,4360]
def ridgeSupport56_008 : List Nat := [4361,4362,4363,4364,4365,4366,4367,4368,4369,4370,4371,4372,4373,4374,4375,4376,4377,4378,4379,4380,4381,4382,4383,4384,4385,4386,4387,4388,4389,4390,4391,4392]
def ridgeSupport56_009 : List Nat := [4393,4394,4395,4396,4397,4650,4651,4652,4653,4654,4655,4656,4657,4658,4659,4660,4661,4662,4663,4664,4665,4666,4667,4668,4669,4670,4671,4672,4673,5214,5215,5216]
def ridgeSupport56_010 : List Nat := [5217,5218,5219,5220,5221,5222,5223,5224,5225,5226,5227,5228,5229,5230,5231,5232,5233,5234,5235,5236,5237]
def ridgeSupport56_code : Nat := 0x1475a3a51ce8e5471a3851be8dd46da3651ae8d5469a34519e8cd465a32518e8c5461a30517e8bd24192048fe47d23d91e48ee47523991c48de46d23591a48ce46523191848be45d22d91648ae45512d89644ae255129894449e24d125892448e245121890447e23d11d88e446e23511988c445e22d11588a444e225111888443e21d10d886442e215109884441e20d105882440e20510188043fe1fd0fd87e43ee1f50f987c43de1ed0f587a43ce1e50f187843be1dd0ed87643ae1d50e9874439e1cd0e5872438e1c50e1870437e1bd0dd86e436e1b50d986c435e1ad0d586a434e1a50d1868433e19d0cd866432e1950c9864431e18d0c5862430e1850c186042fe17d0bd85e42ee1750b985c42de16d0b585a42ce1650b185842be15d0ad85642ae1550a9854429e14d0a5852428e1450a1850427e13d09d84e426e13509984c425e12d09584a424e125091848423e11d08d846422e115089844421e10d085842420e10508184041fe0fd07d83e41ee0f507983c41de0ed07583a41ce0e507183841be0dd06d83641ae0d5069834419e0cd065832418e0c5061830417e0bd05d82e416e0b505982c415e0ac5122889440a1e50e2869430a1650a2849420a0e5062829410a0650228094009fe4fe27e93f09f64fa27c93e09ee4f627a93d09e64f227893c09de4ee27693b09d64ea27493a09ce4e627293909c64e227093809be4de26e93709b64da26c93609ae4d626a93509a64d2268934099e4ce266933099605402981480a2000
def ridgeSupport56_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport56_code
def ridgeSupport56_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport56_code
def ridgeSupport56_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport56_code
def ridgeSupport56_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport56_code
def ridgeSupport56_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport56_code
def ridgeSupport56_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport56_code
def ridgeSupport56_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport56_code
def ridgeSupport56_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport56_code
def ridgeSupport56_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport56_code
def ridgeSupport56_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport56_code
def ridgeSupport56_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport56_code
def ridgeSupport56_rest_011 : Nat := PackedRawNatGrowth.drop 4433 ridgeSupport56_code
def ridgeSupport56_suffix_011 : List Nat := []
def ridgeSupport56_suffix_010 : List Nat := ridgeSupport56_010 ++ ridgeSupport56_suffix_011
def ridgeSupport56_suffix_009 : List Nat := ridgeSupport56_009 ++ ridgeSupport56_suffix_010
def ridgeSupport56_suffix_008 : List Nat := ridgeSupport56_008 ++ ridgeSupport56_suffix_009
def ridgeSupport56_suffix_007 : List Nat := ridgeSupport56_007 ++ ridgeSupport56_suffix_008
def ridgeSupport56_suffix_006 : List Nat := ridgeSupport56_006 ++ ridgeSupport56_suffix_007
def ridgeSupport56_suffix_005 : List Nat := ridgeSupport56_005 ++ ridgeSupport56_suffix_006
def ridgeSupport56_suffix_004 : List Nat := ridgeSupport56_004 ++ ridgeSupport56_suffix_005
def ridgeSupport56_suffix_003 : List Nat := ridgeSupport56_003 ++ ridgeSupport56_suffix_004
def ridgeSupport56_suffix_002 : List Nat := ridgeSupport56_002 ++ ridgeSupport56_suffix_003
def ridgeSupport56_suffix_001 : List Nat := ridgeSupport56_001 ++ ridgeSupport56_suffix_002
def ridgeSupport56_suffix_000 : List Nat := ridgeSupport56_000 ++ ridgeSupport56_suffix_001
theorem ridgeSupport56_source : candidateSupports 56 =
    (PackedRawNatGrowth.readList 13 341 ridgeSupport56_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
