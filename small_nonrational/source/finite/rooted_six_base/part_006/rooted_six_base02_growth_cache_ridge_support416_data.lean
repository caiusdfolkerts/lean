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
def ridgeSupport416_000 : List Nat := [50,80,90,97,100,651,652,653,654,661,662,772,773,774,777,778,783,784,789,791,834,835,839,841,842,846,848,849,851,1025,1026,1027]
def ridgeSupport416_001 : List Nat := [1028,1035,1036,1146,1147,1148,1151,1152,1157,1158,1163,1165,1208,1209,1213,1215,1216,1220,1222,1223,1225,1255,1256,1257,1260,1261,1266,1267,1272,1274,1317,1318]
def ridgeSupport416_002 : List Nat := [1322,1324,1325,1329,1331,1332,1334,1363,1366,1367,1368,1371,1372,1373,1375,1380,1381,1383,1384,3741,3743,3760,3762,3820,3821,3826,3827,3840,3841,3843,3846,3849]
def ridgeSupport416_003 : List Nat := [3852,3854,3855,3868,3869,3874,3875,3909,3911,3916,3917,3922,3923,3928,3930,3936,3937,3950,3951,3960,3961,3974,3975,3981,3983,4000,4002,4060,4061,4066,4067,4080]
def ridgeSupport416_004 : List Nat := [4081,4083,4086,4089,4092,4094,4095,4108,4109,4114,4115,4149,4151,4156,4157,4162,4163,4168,4170,4176,4177,4190,4191,4200,4201,4214,4215,4228,4230,4240,4242,4256]
def ridgeSupport416_005 : List Nat := [4257,4268,4269,4443,4445,4455,4457,4476,4477,4488,4489,4509,4511,4528,4530,4588,4589,4594,4595,4608,4609,4611,4614,4617,4620,4622,4623,4636,4637,4642,4643,4677]
def ridgeSupport416_006 : List Nat := [4679,4684,4685,4690,4691,4696,4698,4704,4705,4718,4719,4728,4729,4742,4743,4796,4797,4804,4805,4852,4854,4864,4866,4880,4881,4892,4893,5067,5069,5079,5081,5100]
def ridgeSupport416_007 : List Nat := [5101,5112,5113,6513,6515,6520,6522,6540,6541,6543,6546,6549,6552,6554,6555,6568,6569,6574,6575,6588,6589,6602,6603,6609,6611,6616,6617,6622,6623,6628,6630,6633]
def ridgeSupport416_008 : List Nat := [6634,6641,6642,6645,6647,6652,6654,6672,6673,6675,6678,6681,6684,6686,6687,6700,6701,6706,6707,6720,6721,6734,6735,6741,6743,6748,6749,6754,6755,6760,6762,6765]
def ridgeSupport416_009 : List Nat := [6766,6773,6774,6776,6777,6784,6786,6788,6789,6796,6798,6812,6813,6824,6825,6942,6943,6945,6947,6954,6955,6957,6959,6978,6979,6990,6991,6993,6995,7000,7002,7020]
def ridgeSupport416_010 : List Nat := [7021,7023,7026,7029,7032,7034,7035,7048,7049,7054,7055,7068,7069,7082,7083,7089,7091,7096,7097,7102,7103,7108,7110,7113,7114,7121,7122,7136,7137,7148,7149,7156]
def ridgeSupport416_011 : List Nat := [7158,7160,7161,7168,7170,7184,7185,7196,7197,7314,7315,7317,7319,7326,7327,7329,7331,7350,7351,7362,7363,7497,7499,7504,7506,7509,7511,7516,7518,7520,7521,7542]
def ridgeSupport416_012 : List Nat := [7543,7545,7547,7552,7554,7556,7557,7578,7579,7932,7933,7968,7969,8028,8029]
def ridgeSupport416_code : Nat := 0x7d77eb9f21f907bf7df9d9becd7617b09d82ec075efaf3d77ebb7587ac1d5eeae755faabd52ea8752fa93cc3e6172df96dca3e50f27f93dc97e4af24f925c1de0e7047821c02e006fe77f1bf6dfa6fb77d9be1df06f4b7a3bcade4ef1b789bbfddf6ee7771bb3dd8eeaf755b9ddce6e3f71db89dc46def6f5b78dbaedcb6dfb6ddb66d6b6b1b53da8ed3f69db43da16cbf65bb2bd956c8f643b1fd8f6aa7551a9dd4e6a3b519a85d426a0b501a79d3c69db4eba6ed36e9ab4d1a63d3169774b9a57d2ae93f49da41d2068cf465a2dd16687f43da1cd0ce85b427a11d0867fb3f99f7cfae7cb3e39eacf4e79b3c99dfcef67673b19d3ce8e72f3959bdcde66bf35d9a9cd4666f335998ccae64b31f98dcc665eb2f1973cb8cfe67f13ed9f64f667af3cd9e5cc766393119884c0a6012f697a4b165892bd95e4a1e50d27993c49be4dd261930496a4b12539294936499247922c88e44521d90e483e41d20c904c81a40720190047ce3e51ed8f646ca36119f8cec62631117d8be45a62cf15d8adc2b61590a1850424a12108684241de0ed069834417e0bd051828412a09104382140f607903781ac04e02500d8063ffdffcffc7fcbfd9fe6ff17f83f8dfc4fdd7ee3e89f40f8f7c6be1df0cf797bc3dbdedcf617b03d69eb0f537a93d35e98f477a2bc8de44f1d78e3c3de1cf0c784bc19e06f017803bcdde4eed7763ac9d60e9f74e95a0ace5652b2157caba55c2ad9560aae5562a994d8a6853329894b4a5852a29314949f44f827993c89da4ec27493a09ce4c926393189884c025f92f49724b8246922c90c48524011fc8f847b23d103081640420190088023531a88d4069c34a1a48d1c68634218b8c5462030f1850c2460c3051820a5852a28e1468a3051606403081680a0032
def ridgeSupport416_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport416_code
def ridgeSupport416_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport416_code
def ridgeSupport416_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport416_code
def ridgeSupport416_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport416_code
def ridgeSupport416_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport416_code
def ridgeSupport416_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport416_code
def ridgeSupport416_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport416_code
def ridgeSupport416_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport416_code
def ridgeSupport416_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport416_code
def ridgeSupport416_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport416_code
def ridgeSupport416_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport416_code
def ridgeSupport416_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport416_code
def ridgeSupport416_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport416_code
def ridgeSupport416_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport416_code
def ridgeSupport416_suffix_013 : List Nat := []
def ridgeSupport416_suffix_012 : List Nat := ridgeSupport416_012 ++ ridgeSupport416_suffix_013
def ridgeSupport416_suffix_011 : List Nat := ridgeSupport416_011 ++ ridgeSupport416_suffix_012
def ridgeSupport416_suffix_010 : List Nat := ridgeSupport416_010 ++ ridgeSupport416_suffix_011
def ridgeSupport416_suffix_009 : List Nat := ridgeSupport416_009 ++ ridgeSupport416_suffix_010
def ridgeSupport416_suffix_008 : List Nat := ridgeSupport416_008 ++ ridgeSupport416_suffix_009
def ridgeSupport416_suffix_007 : List Nat := ridgeSupport416_007 ++ ridgeSupport416_suffix_008
def ridgeSupport416_suffix_006 : List Nat := ridgeSupport416_006 ++ ridgeSupport416_suffix_007
def ridgeSupport416_suffix_005 : List Nat := ridgeSupport416_005 ++ ridgeSupport416_suffix_006
def ridgeSupport416_suffix_004 : List Nat := ridgeSupport416_004 ++ ridgeSupport416_suffix_005
def ridgeSupport416_suffix_003 : List Nat := ridgeSupport416_003 ++ ridgeSupport416_suffix_004
def ridgeSupport416_suffix_002 : List Nat := ridgeSupport416_002 ++ ridgeSupport416_suffix_003
def ridgeSupport416_suffix_001 : List Nat := ridgeSupport416_001 ++ ridgeSupport416_suffix_002
def ridgeSupport416_suffix_000 : List Nat := ridgeSupport416_000 ++ ridgeSupport416_suffix_001
theorem ridgeSupport416_source : candidateSupports 416 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport416_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
