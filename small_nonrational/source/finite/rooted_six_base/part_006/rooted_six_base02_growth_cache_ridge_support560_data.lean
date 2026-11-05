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
def ridgeSupport560_000 : List Nat := [70,89,91,92,530,1014,1015,1017,1022,1024,1038,1039,1041,1046,1048,1050,1051,1053,1058,1060,1275,1276,1278,1279,1282,1283,1284,1286,1287,1289,1294,1295]
def ridgeSupport560_001 : List Nat := [1296,1297,1299,1300,1303,1304,1305,1307,1308,1310,1315,1316,1317,1318,1320,1321,1324,1325,1326,1328,1329,1331,1336,1337,4512,4513,4518,4519,4524,4525,4526,4527]
def ridgeSupport560_002 : List Nat := [4528,4529,4530,4531,4536,4537,4542,4543,4548,4549,4550,4551,4552,4553,4554,4555,4574,4575,4576,4577,4578,4579,4598,4599,4600,4601,4602,4603,4622,4623,4624,4625]
def ridgeSupport560_003 : List Nat := [4626,4627,4646,4647,4648,4649,4650,4651,4670,4671,4672,4673,4674,4675,4694,4695,4696,4697,4698,4699,4700,4702,4706,4708,4712,4714,4718,4719,4720,4721,4722,4723]
def ridgeSupport560_004 : List Nat := [4780,4784,4789,4791,4793,4795,4812,4816,4821,4823,4825,4827,4828,4832,4837,4839,4841,4843,4938,4939,4950,4951,4952,4954,4958,4960,4974,4975,4986,4987,5010,5011]
def ridgeSupport560_005 : List Nat := [5022,5023,5024,5026,5030,5032,5046,5047,5058,5059,5082,5083,5094,5095,5096,5098,5102,5104,5118,5119,5130,5131,6996,6997,7000,7001,7002,7003,7008,7009,7012,7013]
def ridgeSupport560_006 : List Nat := [7014,7015,7034,7035,7036,7037,7038,7039,7058,7059,7060,7061,7062,7063,7064,7066,7070,7072,7076,7078,7082,7083,7084,7085,7086,7087,7088,7090,7094,7096,7100,7102]
def ridgeSupport560_007 : List Nat := [7106,7107,7108,7109,7110,7111,7113,7114,7116,7117,7119,7120,7132,7134,7140,7142,7144,7146,7202,7204,7208,7210,7224,7225,7236,7237,7238,7240,7244,7246,7251,7253]
def ridgeSupport560_008 : List Nat := [7256,7258,7262,7264,7278,7279,7290,7291,7292,7294,7298,7300,7305,7307,7310,7312,7316,7318,7332,7333,7344,7345,7346,7348,7352,7354,7359,7361,7548,7549,7552,7553]
def ridgeSupport560_009 : List Nat := [7554,7555,7562,7564,7568,7570,7574,7576,8018,8019,8020,8021,8022,8023,8044,8052,8056]
def ridgeSupport560_code : Nat := 0x1f78fba7db3eaff56faafd53ea7f52ecc765bb25d90ec6762bb07d82ec0f603afbd7ce60f2ff975cb8e5a72cb963cb0e52f29392dc94e48723b917c89e42720b8fdc7ce3df1eb8dfc6ee30717b8b5c58e2af14f89dc4ce24711b88bc44e1cf0e3855c28e12708b7d5be8df36f937bdbdcde86f3f79bbccde56f2778fbc6de2ef13787bc2ddf6ef3771bb6dd96ec375fbaedd6eeb3757baadd36e93741b9edcd6e6372fb96dcaee53727b92dbfedfb6fbb7cdbdedeb6cfb66db2ed936c3b60daded6b6b3b58daaed5281740a9ffcffa7e13ee9f54fa27cf3e69edcf6a7873c29dbceda7513a69d14e8273f39e9c9ce4a6f737a9b7cdba6c135e9ad4d626af3569a5cd2a5d72e9973cb965c12dc96dcb665af2d59684b325772b995bcad65612ac939c9ca4e3270937c9ba4d5268932498a4bd25c92dc96a4b325892bc95a487242920c90247f23e915c8aa453228913c89a427212908c84241f20e8fdc7ea3f31f88fbc7da3c71e28f0c7823bf1de8e5c72a3931c88e3c71a38b1c48dfc6fa3731b88d9c6ca3631b08d7c6ba35b1ac8d3c69a3431a029c94e0a6653129814b8a5a52c29494a0a4c525292148ca3c51c28d9464a3051728a144ca225102879438a125072831410a0650227f93f89f84fb212108883a41b20d106082c41120790388003fe1fc8fdc7ec21202e016c0b2046
def ridgeSupport560_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport560_code
def ridgeSupport560_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport560_code
def ridgeSupport560_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport560_code
def ridgeSupport560_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport560_code
def ridgeSupport560_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport560_code
def ridgeSupport560_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport560_code
def ridgeSupport560_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport560_code
def ridgeSupport560_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport560_code
def ridgeSupport560_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport560_code
def ridgeSupport560_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport560_code
def ridgeSupport560_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport560_code
def ridgeSupport560_suffix_010 : List Nat := []
def ridgeSupport560_suffix_009 : List Nat := ridgeSupport560_009 ++ ridgeSupport560_suffix_010
def ridgeSupport560_suffix_008 : List Nat := ridgeSupport560_008 ++ ridgeSupport560_suffix_009
def ridgeSupport560_suffix_007 : List Nat := ridgeSupport560_007 ++ ridgeSupport560_suffix_008
def ridgeSupport560_suffix_006 : List Nat := ridgeSupport560_006 ++ ridgeSupport560_suffix_007
def ridgeSupport560_suffix_005 : List Nat := ridgeSupport560_005 ++ ridgeSupport560_suffix_006
def ridgeSupport560_suffix_004 : List Nat := ridgeSupport560_004 ++ ridgeSupport560_suffix_005
def ridgeSupport560_suffix_003 : List Nat := ridgeSupport560_003 ++ ridgeSupport560_suffix_004
def ridgeSupport560_suffix_002 : List Nat := ridgeSupport560_002 ++ ridgeSupport560_suffix_003
def ridgeSupport560_suffix_001 : List Nat := ridgeSupport560_001 ++ ridgeSupport560_suffix_002
def ridgeSupport560_suffix_000 : List Nat := ridgeSupport560_000 ++ ridgeSupport560_suffix_001
theorem ridgeSupport560_source : candidateSupports 560 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport560_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
