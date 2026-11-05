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
def ridgeSupport552_000 : List Nat := [40,70,79,81,82,640,641,643,648,650,664,665,667,672,674,676,677,679,684,686,1013,1016,1017,1020,1023,1037,1040,1041,1044,1047,1049,1052]
def ridgeSupport552_001 : List Nat := [1053,1056,1059,1166,1167,1169,1170,1173,1174,1175,1177,1178,1180,1185,1186,1187,1188,1190,1191,1194,1195,1196,1198,1199,1201,1206,1207,1208,1209,1211,1212,1215]
def ridgeSupport552_002 : List Nat := [1216,1217,1219,1220,1222,1227,1228,3984,3985,3990,3991,3996,3997,3998,3999,4000,4001,4002,4003,4008,4009,4014,4015,4020,4021,4022,4023,4024,4025,4026,4027,4046]
def ridgeSupport552_003 : List Nat := [4047,4048,4049,4050,4051,4070,4071,4072,4073,4074,4075,4094,4095,4096,4097,4098,4099,4118,4119,4120,4121,4122,4123,4142,4143,4144,4145,4146,4147,4166,4167,4168]
def ridgeSupport552_004 : List Nat := [4169,4170,4171,4172,4174,4178,4180,4184,4186,4190,4191,4192,4193,4194,4195,4314,4315,4326,4327,4328,4330,4334,4336,4350,4351,4362,4363,4386,4387,4398,4399,4400]
def ridgeSupport552_005 : List Nat := [4402,4406,4408,4422,4423,4434,4435,4458,4459,4470,4471,4472,4474,4478,4480,4494,4495,4506,4507,4926,4927,4944,4945,4962,4963,4964,4966,4970,4972,4980,4981,4998]
def ridgeSupport552_006 : List Nat := [4999,5016,5017,5034,5035,5036,5038,5042,5044,5052,5053,5070,5071,5088,5089,5106,5107,5108,5110,5114,5116,5124,5125,6648,6649,6652,6653,6654,6655,6660,6661,6664]
def ridgeSupport552_007 : List Nat := [6665,6666,6667,6686,6687,6688,6689,6690,6691,6710,6711,6712,6713,6714,6715,6716,6718,6722,6724,6728,6730,6734,6735,6736,6737,6738,6739,6740,6742,6746,6748,6752]
def ridgeSupport552_008 : List Nat := [6754,6758,6759,6760,6761,6762,6763,6765,6766,6768,6769,6771,6772,6830,6832,6836,6838,6852,6853,6864,6865,6866,6868,6872,6874,6879,6881,6884,6886,6890,6892,6906]
def ridgeSupport552_009 : List Nat := [6907,6918,6919,6920,6922,6926,6928,6933,6935,6938,6940,6944,6946,6960,6961,6972,6973,6974,6976,6980,6982,6987,6989,7212,7213,7214,7216,7220,7222,7230,7231,7239]
def ridgeSupport552_010 : List Nat := [7241,7248,7249,7250,7252,7266,7267,7268,7270,7274,7276,7284,7285,7293,7295,7302,7303,7304,7306,7320,7321,7322,7324,7328,7330,7338,7339,7347,7349,7356,7357,7358]
def ridgeSupport552_011 : List Nat := [7360,7512,7513,7516,7517,7518,7519,7526,7528,7532,7534,7538,7540,7563,7565,7569,7571,7575,7577,7958,7959,7960,7961,7962,7963]
def ridgeSupport552_code : Nat := 0x1f1bf8d7c67e31f17f8b7667b2fd93ec8f637b17d74eb975bbad9d68eb3757fabdd5deae7567ab1cc0e5f72f7979cb5e59f2af955ca2e507273935c99e4c722b911c87e4371ff8fbc75e3a71b38d5c66e32718f8c5c54e2971478a1c49e23f0ff87dc36e1a70c385dc2de166d37697b46da26d0367db3dd9e6cc7661b22d906c73635b17d8aec4361db0ad846c1f60dafbd7d6bb35d5ae6d726b875bfadad6c6b535a5ad1d686b17589ab6d5a6ac355da74d39e9c74e1a6ed36e9af4d5a69d34699f4cda62d3069734b5a56d2a694f4a5a51d28693f49da4ad246913485a3ed1e68ef475a39d1c68df46da23d116887441a1fd0f682f415a09d0468174099ffcff67f73f99f9cfc50168093fc9fd4fda7e93f39f94f867c13cf9e74ef67793b49d94eba7593ab9d54e667313879c34dd66e936c9b54d9a6c93639b14d466a133f99f466e33518f8c746022fd17a8bc45de2ed16b8b5454e2a51478a344e226d13289844be25d123891442e2150ff87f43c21dd0ea874439e1cd0db86d418e0c5061830417e0bd05a82c41520a504e826412e095049824411e08d03381940c606102f817406e03501980c405e02d0038014006000fff7ff3fadfd4fe97f43f9dfccfd37e93f45fa0fcf7e73eedf74fb97dc3eddf6cfb57da3ebdf5cfa97d43e8df44fa17d03e7df3cf9d7ce3e5df2cf917c813309964c6262130c9824c025f92f09764b925c12dc96c4b125792b89584ab255129c94c4a4251928894249c24d126492e49624a924892248f247108c84041d20e106482e414208904081a3ff1fe0fe47f03f51570ab054e2a51520a8854029b14c8a605142881418a04500052028813c08c028
def ridgeSupport552_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport552_code
def ridgeSupport552_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport552_code
def ridgeSupport552_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport552_code
def ridgeSupport552_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport552_code
def ridgeSupport552_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport552_code
def ridgeSupport552_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport552_code
def ridgeSupport552_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport552_code
def ridgeSupport552_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport552_code
def ridgeSupport552_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport552_code
def ridgeSupport552_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport552_code
def ridgeSupport552_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport552_code
def ridgeSupport552_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport552_code
def ridgeSupport552_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport552_code
def ridgeSupport552_suffix_012 : List Nat := []
def ridgeSupport552_suffix_011 : List Nat := ridgeSupport552_011 ++ ridgeSupport552_suffix_012
def ridgeSupport552_suffix_010 : List Nat := ridgeSupport552_010 ++ ridgeSupport552_suffix_011
def ridgeSupport552_suffix_009 : List Nat := ridgeSupport552_009 ++ ridgeSupport552_suffix_010
def ridgeSupport552_suffix_008 : List Nat := ridgeSupport552_008 ++ ridgeSupport552_suffix_009
def ridgeSupport552_suffix_007 : List Nat := ridgeSupport552_007 ++ ridgeSupport552_suffix_008
def ridgeSupport552_suffix_006 : List Nat := ridgeSupport552_006 ++ ridgeSupport552_suffix_007
def ridgeSupport552_suffix_005 : List Nat := ridgeSupport552_005 ++ ridgeSupport552_suffix_006
def ridgeSupport552_suffix_004 : List Nat := ridgeSupport552_004 ++ ridgeSupport552_suffix_005
def ridgeSupport552_suffix_003 : List Nat := ridgeSupport552_003 ++ ridgeSupport552_suffix_004
def ridgeSupport552_suffix_002 : List Nat := ridgeSupport552_002 ++ ridgeSupport552_suffix_003
def ridgeSupport552_suffix_001 : List Nat := ridgeSupport552_001 ++ ridgeSupport552_suffix_002
def ridgeSupport552_suffix_000 : List Nat := ridgeSupport552_000 ++ ridgeSupport552_suffix_001
theorem ridgeSupport552_source : candidateSupports 552 =
    (PackedRawNatGrowth.readList 13 377 ridgeSupport552_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
