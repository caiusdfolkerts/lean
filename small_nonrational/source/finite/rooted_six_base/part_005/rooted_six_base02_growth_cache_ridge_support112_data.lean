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
def ridgeSupport112_000 : List Nat := [67,87,88,89,527,989,992,994,997,999,1001,1004,1006,1009,1011,1013,1016,1018,1021,1023,1255,1256,1258,1259,1260,1261,1263,1264,1266,1267,1269,1270]
def ridgeSupport112_001 : List Nat := [1276,1277,1279,1280,1281,1282,1284,1285,1287,1288,1290,1291,1297,1298,1300,1301,1302,1303,1305,1306,1308,1309,1311,1312,4508,4509,4510,4511,4512,4513,4514,4515]
def ridgeSupport112_002 : List Nat := [4520,4521,4526,4527,4532,4533,4534,4535,4536,4537,4538,4539,4544,4545,4550,4551,4556,4557,4558,4559,4560,4561,4580,4581,4582,4583,4584,4585,4604,4605,4606,4607]
def ridgeSupport112_003 : List Nat := [4608,4609,4628,4629,4630,4631,4632,4633,4652,4653,4654,4655,4656,4657,4676,4677,4678,4679,4680,4681,4700,4701,4702,4703,4704,4705,4709,4711,4715,4717,4721,4723]
def ridgeSupport112_004 : List Nat := [4749,4753,4756,4758,4760,4762,4765,4769,4772,4774,4776,4778,4781,4785,4788,4790,4792,4794,4862,4863,4874,4875,4883,4885,4889,4891,4898,4899,4910,4911,4934,4935]
def ridgeSupport112_005 : List Nat := [4946,4947,4955,4957,4961,4963,4970,4971,4982,4983,5006,5007,5018,5019,5027,5029,5033,5035,5042,5043,5054,5055,6992,6993,6994,6995,6996,6997,7004,7005,7006,7007]
def ridgeSupport112_006 : List Nat := [7008,7009,7016,7017,7018,7019,7020,7021,7040,7041,7042,7043,7044,7045,7064,7065,7066,7067,7068,7069,7073,7075,7079,7081,7085,7087,7088,7089,7090,7091,7092,7093]
def ridgeSupport112_007 : List Nat := [7097,7099,7103,7105,7109,7111,7115,7116,7118,7119,7121,7122,7125,7127,7129,7131,7133,7135,7151,7153,7157,7159,7166,7167,7178,7179,7187,7189,7193,7195,7198,7200]
def ridgeSupport112_008 : List Nat := [7205,7207,7211,7213,7220,7221,7232,7233,7241,7243,7247,7249,7252,7254,7259,7261,7265,7267,7274,7275,7286,7287,7295,7297,7301,7303,7306,7308,7544,7545,7546,7547]
def ridgeSupport112_009 : List Nat := [7548,7549,7559,7561,7565,7567,7571,7573,8000,8001,8002,8003,8004,8005,8037,8041,8045]
def ridgeSupport112_code : Nat := 0x1f6dfb4fd97e8bf44fa1fd0be83f40ecaf64fb1fd8dec4f61fafbd7cebdf5ebaf3d78e46722b90fc85e40f1ff8efc76e35f1ab8c7c61e2ef16f8adc54e28f13f897c49e20f10386bc34e16f0af84fc25e10707b837c19e0af04f817c0adffeffb7efbf5df8efbf7bfbdddedef677afbd5de96f4779fbcede66f2f78fbc5de0eeff777bb9ddaeed3767bb2dd8eec375fbaddd4ee9f747ba1dceee73737b9adccee6370bb84dc1ee0b703b80db6edb36d7b6adb4eda36c3b60dafed7b6bbb5cdaaed536a7b52da8ed4277f3be9d9ceca7573a99d2ce8e73739a9c7ce3a6ef3769b5cdaa6c73619aecd6e6a73529a3cd1a65f32e991cc8a63731998acc4e61730a97fcbfa5752b895b4ad25632ad9554aa254d2a4950ca7653529894b4a5252328d939c9c64db26b933c9964c326092fc97a4bb25c924c92248f246922c912463230917c8ba45b22c90cc86242f21690ac8524032008ffc7fa3fb1fc8f4c7a23cf1e68f2c7923a31d08e7c73a39b1cc8e3c71a3831c08ddc6ea3731b88dbc6da36b1b48d7c6ba3531a88d1c68a3431a08cfc67a33b19c290147ca3a51c28d1464a2e51628a9450a245112859428a105072829410a0450128013fc9fa4fc27b13d49e64f227813bc9da4ec27593a89d04e71ff8ff47f43f81fa8fcc7e23ee1f60fa47ce3e51f10f807ba20f02c81600ae043
def ridgeSupport112_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport112_code
def ridgeSupport112_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport112_code
def ridgeSupport112_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport112_code
def ridgeSupport112_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport112_code
def ridgeSupport112_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport112_code
def ridgeSupport112_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport112_code
def ridgeSupport112_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport112_code
def ridgeSupport112_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport112_code
def ridgeSupport112_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport112_code
def ridgeSupport112_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport112_code
def ridgeSupport112_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport112_code
def ridgeSupport112_suffix_010 : List Nat := []
def ridgeSupport112_suffix_009 : List Nat := ridgeSupport112_009 ++ ridgeSupport112_suffix_010
def ridgeSupport112_suffix_008 : List Nat := ridgeSupport112_008 ++ ridgeSupport112_suffix_009
def ridgeSupport112_suffix_007 : List Nat := ridgeSupport112_007 ++ ridgeSupport112_suffix_008
def ridgeSupport112_suffix_006 : List Nat := ridgeSupport112_006 ++ ridgeSupport112_suffix_007
def ridgeSupport112_suffix_005 : List Nat := ridgeSupport112_005 ++ ridgeSupport112_suffix_006
def ridgeSupport112_suffix_004 : List Nat := ridgeSupport112_004 ++ ridgeSupport112_suffix_005
def ridgeSupport112_suffix_003 : List Nat := ridgeSupport112_003 ++ ridgeSupport112_suffix_004
def ridgeSupport112_suffix_002 : List Nat := ridgeSupport112_002 ++ ridgeSupport112_suffix_003
def ridgeSupport112_suffix_001 : List Nat := ridgeSupport112_001 ++ ridgeSupport112_suffix_002
def ridgeSupport112_suffix_000 : List Nat := ridgeSupport112_000 ++ ridgeSupport112_suffix_001
theorem ridgeSupport112_source : candidateSupports 112 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport112_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
