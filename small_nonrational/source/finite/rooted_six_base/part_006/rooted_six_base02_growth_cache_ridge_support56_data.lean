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
def ridgeSupport56_000 : List Nat := [0,67,68,69,70,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015]
def ridgeSupport56_001 : List Nat := [1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047]
def ridgeSupport56_002 : List Nat := [1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,4844,4845,4846,4847,4848,4849,4850,4851,4852,4853,4854,4855,4856,4857,4858,4859,4860,4861,4862]
def ridgeSupport56_003 : List Nat := [4863,4864,4865,4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4886,4887,4888,4889,4890,4891,4892,4893,4894]
def ridgeSupport56_004 : List Nat := [4895,4896,4897,4898,4899,4900,4901,4902,4903,4904,4905,4906,4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4919,4920,4921,4922,4923,4924,4925,4926]
def ridgeSupport56_005 : List Nat := [4927,4928,4929,4930,4931,4932,4933,4934,4935,4936,4937,4938,4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4953,4954,4955,4956,4957,4958]
def ridgeSupport56_006 : List Nat := [4959,4960,4961,4962,4963,4964,4965,4966,4967,4968,4969,4970,4971,4972,4973,4974,4975,4976,4977,4978,4979,4980,4981,4982,4983,4984,4985,4986,4987,4988,4989,4990]
def ridgeSupport56_007 : List Nat := [4991,4992,4993,4994,4995,4996,4997,4998,4999,5000,5001,5002,5003,5004,5005,5006,5007,5008,5009,5010,5011,5012,5013,5014,5015,5016,5017,5018,5019,5020,5021,5022]
def ridgeSupport56_008 : List Nat := [5023,5024,5025,5026,5027,5028,5029,5030,5031,5032,5033,5034,5035,5036,5037,5038,5039,5040,5041,5042,5043,5044,5045,5046,5047,5048,5049,5050,5051,5052,5053,5054]
def ridgeSupport56_009 : List Nat := [5055,5056,5057,5058,5059,5060,5061,5062,5063,5064,5065,5066,5067,5068,5069,5070,5071,5072,5073,5074,5075,5076,5077,5078,5079,5080,5081,5082,5083,5084,5085,5086]
def ridgeSupport56_010 : List Nat := [5087,5088,5089,5090,5091,5092,5093,5094,5095,5096,5097,5098,5099,5100,5101,5102,5103,5104,5105,5106,5107,5108,5109,5110,5111,5112,5113,5114,5115,5116,5117,5118]
def ridgeSupport56_011 : List Nat := [5119,5120,5121,5122,5123,5124,5125,5126,5127,5128,5129,5130,5131,7148,7149,7150,7151,7152,7153,7154,7155,7156,7157,7158,7159,7160,7161,7162,7163,7164,7165,7166]
def ridgeSupport56_012 : List Nat := [7167,7168,7169,7170,7171,7172,7173,7174,7175,7176,7177,7178,7179,7180,7181,7182,7183,7184,7185,7186,7187,7188,7189,7190,7191,7192,7193,7194,7195,7196,7197,7198]
def ridgeSupport56_013 : List Nat := [7199,7200,7201,7202,7203,7204,7205,7206,7207,7208,7209,7210,7211,7212,7213,7214,7215,7216,7217,7218,7219,7220,7221,7222,7223,7224,7225,7226,7227,7228,7229,7230]
def ridgeSupport56_014 : List Nat := [7231,7232,7233,7234,7235,7236,7237,7238,7239,7240,7241,7242,7243,7244,7245,7246,7247,7248,7249,7250,7251,7252,7253,7254,7255,7256,7257,7258,7259,7260,7261,7262]
def ridgeSupport56_015 : List Nat := [7263,7264,7265,7266,7267,7268,7269,7270,7271,7272,7273,7274,7275,7276,7277,7278,7279,7280,7281,7282,7283,7284,7285,7286,7287,7288,7289,7290,7291,7292,7293,7294]
def ridgeSupport56_016 : List Nat := [7295,7296,7297,7298,7299,7300,7301,7302,7303,7304,7305,7306,7307,7308,7309,7310,7311,7312,7313,7314,7315,7316,7317,7318,7319,7320,7321,7322,7323,7324,7325,7326]
def ridgeSupport56_017 : List Nat := [7327,7328,7329,7330,7331,7332,7333,7334,7335,7336,7337,7338,7339,7340,7341,7342,7343,7344,7345,7346,7347,7348,7349,7350,7351,7352,7353,7354,7355,7356,7357,7358]
def ridgeSupport56_018 : List Nat := [7359,7360,7361,7362,7363,7556,7557,7558,7559,7560,7561,7562,7563,7564,7565,7566,7567,7568,7569,7570,7571,7572,7573,7574,7575,7576,7577,7578,7579,8060,8061,8062]
def ridgeSupport56_019 : List Nat := [8063,8064,8065,8066,8067,8068,8069,8070,8071,8072,8073,8074,8075,8076,8077,8078,8079,8080,8081,8082,8083]
def ridgeSupport56_code : Nat := 0x1f93fc97e47f21f8ffc77e37f19f8bfc57e27f11f87fc37e17f09f83fc17e07f01f7ffbf7df7ef9d9becd7667b31d97ecb7657b29d93ec97647b21d8fec77637b19d8bec57627b11d87ec37617b09cc3e617307981cbfe5f72f7979cbbe5d72e7971cb7e5b72d7969cb3e5972c7961cafe5772b7959cabe5572a7951ca7e537297949ca3e517287941c9fe4f7277939c9be4d7267931c97e4b7257929c93e497247921c8fe477237919c8be457227911c87e437217909c83e417207901c7fe3f71f78f9c7be3d71e78f1c77e3b71d78e9c73e3971c78e1c6fe3771b78d9c6be3571a78d1c67e3371978c9c63e3171878c1c5fe2f71778b9c5be2d71678b1c57e2b71578a9c53e2971478a1c4fe277137899c4be257127891c47e237117889c43e217107881c3fe1f70f7879c3be1d70e7871c37e1b70d7869c33e1970c7861c2fe1770b7859c2be1570a7851c27e137097849c23e117087841c1fe0f7077839c1be0d7067831c17e0b7057829c13e097047821c0fe077037819c0be057027811c07e037017809c03e017007801bffdff6ff77f9bfbdfd6fe77f1bf7dfb6fd77e9bf3df96fc77e1befdf76fb77d940ba055026811407a035016809403a0150068013ff9ff4ff67f93fb9fd4fe67f13f79fb4fd67e93f39f94fc67e13ef9f74fb67d93eb9f54fa67d13e79f34f967c93e39f14f867c13df9ef4f767b93db9ed4f667b13d79eb4f567a93d39e94f467a13cf9e74f367993cb9e54f267913c79e34f167893c39e14f067813bf9df4ef67793bb9dd4ee67713b79db4ed67693b39d94ec67613af9d74eb67593ab9d54ea67513a79d34e967493a39d14e8674139f9cf4e7673939b9cd4e667313979cb4e567293939c94e4672138f9c74e3671938b9c54e267113879c34e167093839c14e0670137f9bf4df66f937b9bd4de66f13779bb4dd66e93739b94dc66e136f9b74db66d936b9b54da66d13679b34d966c93639b14d866c135f9af4d766b935b9ad4d666b13579ab4d566a93539a94d466a134f9a74d3669934b9a54d266913479a34d166893439a14d0668133f99f4cf667933b99d4ce667133799b4cd66693339994cc666132f9974cb665932b9954ca66513279934c966493239914c8664131f98f4c7663931b98d4c6663131798b4c566293139894c4662130f9874c3661930b9854c266113079834c166093039814c066012ff97f4bf65f92fb97d4be65f12f797b4bd65e92f39794bc65e12ef9774bb65d8424211908884242020f907883a41c20d906883241820b905882a4142099048822410207903881a40c2059028812408203901880a40420190088024001ff8ff87fa3fc1fd8fe87f23f81fb8fd87ea3f41f98fc87e23f01f78fb87da3ec1f58fa87d23e81f38f987ca3e41f18f887c23e01ef8f787ba0460228110086000
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
def ridgeSupport56_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport56_code
def ridgeSupport56_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport56_code
def ridgeSupport56_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport56_code
def ridgeSupport56_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport56_code
def ridgeSupport56_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport56_code
def ridgeSupport56_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport56_code
def ridgeSupport56_rest_017 : Nat := PackedRawNatGrowth.drop 7072 ridgeSupport56_code
def ridgeSupport56_rest_018 : Nat := PackedRawNatGrowth.drop 7488 ridgeSupport56_code
def ridgeSupport56_rest_019 : Nat := PackedRawNatGrowth.drop 7904 ridgeSupport56_code
def ridgeSupport56_rest_020 : Nat := PackedRawNatGrowth.drop 8177 ridgeSupport56_code
def ridgeSupport56_suffix_020 : List Nat := []
def ridgeSupport56_suffix_019 : List Nat := ridgeSupport56_019 ++ ridgeSupport56_suffix_020
def ridgeSupport56_suffix_018 : List Nat := ridgeSupport56_018 ++ ridgeSupport56_suffix_019
def ridgeSupport56_suffix_017 : List Nat := ridgeSupport56_017 ++ ridgeSupport56_suffix_018
def ridgeSupport56_suffix_016 : List Nat := ridgeSupport56_016 ++ ridgeSupport56_suffix_017
def ridgeSupport56_suffix_015 : List Nat := ridgeSupport56_015 ++ ridgeSupport56_suffix_016
def ridgeSupport56_suffix_014 : List Nat := ridgeSupport56_014 ++ ridgeSupport56_suffix_015
def ridgeSupport56_suffix_013 : List Nat := ridgeSupport56_013 ++ ridgeSupport56_suffix_014
def ridgeSupport56_suffix_012 : List Nat := ridgeSupport56_012 ++ ridgeSupport56_suffix_013
def ridgeSupport56_suffix_011 : List Nat := ridgeSupport56_011 ++ ridgeSupport56_suffix_012
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
    (PackedRawNatGrowth.readList 13 629 ridgeSupport56_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
