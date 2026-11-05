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
def ridgeSupport416_000 : List Nat := [50,80,90,97,100,651,652,653,654,661,662,772,773,774,777,778,783,784,789,791,834,835,839,841,842,846,848,849,851,1025,1026,1027]
def ridgeSupport416_001 : List Nat := [1028,1035,1036,1146,1147,1148,1151,1152,1157,1158,1163,1165,1208,1209,1213,1215,1216,1220,1222,1223,1225,1255,1256,1257,1260,1261,1266,1267,1272,1274,1317,1318]
def ridgeSupport416_002 : List Nat := [1322,1324,1325,1329,1331,1332,1334,1363,1366,1367,1368,1371,1372,1373,1375,1380,1381,1383,1384,3741,3743,3760,3762,3820,3821,3826,3827,3840,3841,3843,3846,3849]
def ridgeSupport416_003 : List Nat := [3852,3854,3855,3868,3869,3874,3875,3909,3911,3916,3917,3922,3923,3928,3930,3936,3937,3950,3951,3960,3961,3974,3975,3981,3983,4000,4002,4060,4061,4066,4067,4080]
def ridgeSupport416_004 : List Nat := [4081,4083,4086,4089,4092,4094,4095,4108,4109,4114,4115,4149,4151,4156,4157,4162,4163,4168,4170,4176,4177,4190,4191,4200,4201,4214,4215,4228,4230,4240,4242,4256]
def ridgeSupport416_005 : List Nat := [4257,4268,4269,4443,4445,4455,4457,4476,4477,4488,4489,4509,4511,4528,4530,4588,4589,4594,4595,4608,4609,4611,4614,4617,4620,4622,4623,4636,4637,4642,4643,4677]
def ridgeSupport416_006 : List Nat := [4679,4684,4685,4690,4691,4696,4698,4704,4705,4718,4719,4728,4729,4742,4743,4796,4797,4804,4805,4852,4854,4864,4866,4880,4881,4892,4893,5067,5069,5079,5081,5100]
def ridgeSupport416_007 : List Nat := [5101,5112,5113,5265,5267,5272,5274,5277,5279,5284,5286,5288,5289,5310,5311,5313,5315,5320,5322,5324,5325,5346,5347,5700,5701,5736,5737,5796,5797,6340,6341,6346]
def ridgeSupport416_008 : List Nat := [6347,6356,6358,6360,6361,6364,6367,6388,6389,6394,6395,6404,6406,6408,6409,6412,6415,6428,6429,6431,6433,6482,6484,6486,6487,6508,6509,6514,6515,6524,6526,6528]
def ridgeSupport416_009 : List Nat := [6529,6532,6535,6548,6549,6551,6553,6602,6604,6606,6607]
def ridgeSupport416_code : Nat := 0x673f39d9ccce5666732f995cca661f309981cc065fb2f9973cb965b72d9957cab65532a5921c8fe47723990fc866427211906c8263ef1f58f5c7a637f1b98d9c6c635b1a98cbc6563171896a5b5259a6cd1645b22538e9c54cda66532a9914c3a60d2fe97d4a9a54529a94949fa4ed26a931493a48cfe67f13ed9f64f667af3cd9e5cc766393119884c0a6012f697a4b165892bd95e4a1e50d27993c49be4dd261930496a4b12539294936499247922c88e44521d90e483e41d20c904c81a40720190047ce3e51ed8f646ca36119f8cec62631117d8be45a62cf15d8adc2b61590a1850424a12108684241de0ed069834417e0bd051828412a09104382140f607903781ac04e02500d8063ffdffcffc7fcbfd9fe6ff17f83f8dfc4fdd7ee3e89f40f8f7c6be1df0cf797bc3dbdedcf617b03d69eb0f537a93d35e98f477a2bc8de44f1d78e3c3de1cf0c784bc19e06f017803bcdde4eed7763ac9d60e9f74e95a0ace5652b2157caba55c2ad9560aae5562a994d8a6853329894b4a5852a29314949f44f827993c89da4ec27493a09ce4c926393189884c025f92f49724b8246922c90c48524011fc8f847b23d103081640420190088023531a88d4069c34a1a48d1c68634218b8c5462030f1850c2460c3051820a5852a28e1468a3051606403081680a0032
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
def ridgeSupport416_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport416_code
def ridgeSupport416_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport416_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
