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
def ridgeSupport304_000 : List Nat := [69,88,90,92,529,1002,1003,1005,1010,1012,1026,1027,1029,1034,1036,1049,1052,1054,1057,1059,1254,1255,1257,1258,1261,1262,1263,1265,1266,1268,1273,1274]
def ridgeSupport304_001 : List Nat := [1296,1298,1299,1301,1302,1304,1306,1307,1309,1310,1313,1314,1317,1319,1320,1322,1323,1325,1327,1328,1330,1331,1334,1335,4510,4511,4516,4517,4520,4521,4522,4523]
def ridgeSupport304_002 : List Nat := [4524,4525,4530,4531,4534,4535,4540,4541,4544,4545,4546,4547,4548,4549,4554,4555,4568,4569,4570,4571,4572,4573,4592,4593,4594,4595,4596,4597,4616,4617,4618,4619]
def ridgeSupport304_003 : List Nat := [4620,4621,4640,4641,4642,4643,4644,4645,4664,4665,4666,4667,4668,4669,4688,4689,4690,4691,4692,4693,4701,4704,4707,4710,4712,4713,4714,4715,4716,4717,4718,4720]
def ridgeSupport304_004 : List Nat := [4764,4768,4773,4775,4777,4779,4796,4800,4805,4807,4809,4811,4829,4833,4836,4838,4840,4842,4866,4867,4878,4879,4880,4882,4886,4888,4902,4903,4914,4915,5008,5009]
def ridgeSupport304_005 : List Nat := [5020,5021,5025,5028,5031,5034,5044,5045,5056,5057,5080,5081,5092,5093,5097,5100,5103,5106,5116,5117,5128,5129,6994,6995,6998,6999,7002,7003,7006,7007,7010,7011]
def ridgeSupport304_006 : List Nat := [7014,7015,7028,7029,7030,7031,7032,7033,7052,7053,7054,7055,7056,7057,7065,7068,7071,7074,7076,7077,7078,7079,7080,7081,7082,7084,7089,7092,7095,7098,7100,7101]
def ridgeSupport304_007 : List Nat := [7102,7103,7104,7105,7106,7108,7112,7114,7115,7117,7122,7123,7128,7130,7136,7138,7145,7147,7148,7150,7154,7156,7170,7171,7182,7183,7184,7186,7190,7192,7197,7199]
def ridgeSupport304_008 : List Nat := [7257,7260,7263,7266,7276,7277,7288,7289,7293,7296,7299,7302,7304,7309,7311,7314,7317,7320,7330,7331,7342,7343,7347,7350,7353,7356,7358,7363,7546,7547,7550,7551]
def ridgeSupport304_009 : List Nat := [7554,7555,7556,7558,7569,7572,7575,7578,8012,8013,8014,8015,8016,8017,8040,8048,8057]
def ridgeSupport304_code : Nat := 0x1f79fb87da3ea3f50fa7fd3be9bf4cecd765fb29d91ec37613b07d82ebff5fbaf7d7ae61f2fb979cb9e5b72cf95fcaee51f28b931c95e49723f91bc88e43720f901c7de3cf1e38dbc6ce31717f8b9c59e0ff077831c16e09704381fc0ee01f00b7e9bf2df76fb37d7be9df16f837b5bd8de9ef4b79bbcbde56f23789bc2de0ef0377fbbeddeeef3775bb7dda6ec7759baadd4eea374fba6dd2ee93745b9fdce6e67723b90dc7ee3b71bb8cdbcede36efb76dbaedd36cfb66db1ed8b6bfb5edaded6b6afb56da9ed4a8134089fecff27e53ef9f64fa67cb3e49eccf627833c09daced27553a79d24e8673b39c9c8ce42667332993cc9a6313169894c4261f30e981cc0a5d52e89734b925c32dd965cb2658f2c59604af25572a9953ca9654129c93849ba4db26c935c9aa4d3268933498e4c125d92ac9524a7252928c94247b23c91dc8ea473238912c892447222910c88241b20c905c82a4132088fac7d23e71f28f8c7c23bb1dc8edc76a3b31d88e5c72a38b1c48e1c70a3831c08dec6f236f1b68d9c6ca35b1ac8d5c6aa3531a88d2c69233f19e29b94d8a6653229814bca5a52b29514a0a4e5252911484a3c51d28d9468a3051628a944ca2451027d13e49e84f227893bc9dc4ed27513a49ce4e6211908483c41c20c903081440520190087e83f21f68fac7d421102e01680b0045
def ridgeSupport304_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport304_code
def ridgeSupport304_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport304_code
def ridgeSupport304_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport304_code
def ridgeSupport304_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport304_code
def ridgeSupport304_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport304_code
def ridgeSupport304_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport304_code
def ridgeSupport304_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport304_code
def ridgeSupport304_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport304_code
def ridgeSupport304_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport304_code
def ridgeSupport304_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport304_code
def ridgeSupport304_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport304_code
def ridgeSupport304_suffix_010 : List Nat := []
def ridgeSupport304_suffix_009 : List Nat := ridgeSupport304_009 ++ ridgeSupport304_suffix_010
def ridgeSupport304_suffix_008 : List Nat := ridgeSupport304_008 ++ ridgeSupport304_suffix_009
def ridgeSupport304_suffix_007 : List Nat := ridgeSupport304_007 ++ ridgeSupport304_suffix_008
def ridgeSupport304_suffix_006 : List Nat := ridgeSupport304_006 ++ ridgeSupport304_suffix_007
def ridgeSupport304_suffix_005 : List Nat := ridgeSupport304_005 ++ ridgeSupport304_suffix_006
def ridgeSupport304_suffix_004 : List Nat := ridgeSupport304_004 ++ ridgeSupport304_suffix_005
def ridgeSupport304_suffix_003 : List Nat := ridgeSupport304_003 ++ ridgeSupport304_suffix_004
def ridgeSupport304_suffix_002 : List Nat := ridgeSupport304_002 ++ ridgeSupport304_suffix_003
def ridgeSupport304_suffix_001 : List Nat := ridgeSupport304_001 ++ ridgeSupport304_suffix_002
def ridgeSupport304_suffix_000 : List Nat := ridgeSupport304_000 ++ ridgeSupport304_suffix_001
theorem ridgeSupport304_source : candidateSupports 304 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport304_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
