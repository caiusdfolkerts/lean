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
def ridgeSupport552_000 : List Nat := [40,70,79,81,82,640,641,643,648,650,664,665,667,672,674,676,677,679,684,686,1013,1016,1017,1020,1023,1037,1040,1041,1044,1047,1049,1052]
def ridgeSupport552_001 : List Nat := [1053,1056,1059,1166,1167,1169,1170,1173,1174,1175,1177,1178,1180,1185,1186,1187,1188,1190,1191,1194,1195,1196,1198,1199,1201,1206,1207,1208,1209,1211,1212,1215]
def ridgeSupport552_002 : List Nat := [1216,1217,1219,1220,1222,1227,1228,3984,3985,3990,3991,3996,3997,3998,3999,4000,4001,4002,4003,4008,4009,4014,4015,4020,4021,4022,4023,4024,4025,4026,4027,4046]
def ridgeSupport552_003 : List Nat := [4047,4048,4049,4050,4051,4070,4071,4072,4073,4074,4075,4094,4095,4096,4097,4098,4099,4118,4119,4120,4121,4122,4123,4142,4143,4144,4145,4146,4147,4166,4167,4168]
def ridgeSupport552_004 : List Nat := [4169,4170,4171,4172,4174,4178,4180,4184,4186,4190,4191,4192,4193,4194,4195,4314,4315,4326,4327,4328,4330,4334,4336,4350,4351,4362,4363,4386,4387,4398,4399,4400]
def ridgeSupport552_005 : List Nat := [4402,4406,4408,4422,4423,4434,4435,4458,4459,4470,4471,4472,4474,4478,4480,4494,4495,4506,4507,4926,4927,4944,4945,4962,4963,4964,4966,4970,4972,4980,4981,4998]
def ridgeSupport552_006 : List Nat := [4999,5016,5017,5034,5035,5036,5038,5042,5044,5052,5053,5070,5071,5088,5089,5106,5107,5108,5110,5114,5116,5124,5125,5280,5281,5284,5285,5286,5287,5294,5296,5300]
def ridgeSupport552_007 : List Nat := [5302,5306,5308,5331,5333,5337,5339,5343,5345,5726,5727,5728,5729,5730,5731,6398,6399,6400,6401,6402,6403,6404,6406,6410,6412,6414,6415,6416,6418,6422,6424,6426]
def ridgeSupport552_008 : List Nat := [6427,6450,6451,6456,6457,6468,6469,6474,6475,6486,6487,6492,6493,6566,6568,6582,6583,6584,6586,6600,6601,6602,6604,6618,6619]
def ridgeSupport552_code : Nat := 0x19dbced67333959c9ce466eb3719b7cdb66a334d95dcae655f2ad94bca56517289939c9c64cf26591bc8d646322d912c88643f21d90cc85641b209903c8164072018ffc7f598ecc5661b30597ecbd4e1a6fd36e9b34d5a69d2f29754b6a5a52c295d4a7a5352969494a1a5050168093fc9fd4fda7e93f39f94f867c13cf9e74ef67793b49d94eba7593ab9d54e667313879c34dd66e936c9b54d9a6c93639b14d466a133f99f466e33518f8c746022fd17a8bc45de2ed16b8b5454e2a51478a344e226d13289844be25d123891442e2150ff87f43c21dd0ea874439e1cd0db86d418e0c5061830417e0bd05a82c41520a504e826412e095049824411e08d03381940c606102f817406e03501980c405e02d0038014006000fff7ff3fadfd4fe97f43f9dfccfd37e93f45fa0fcf7e73eedf74fb97dc3eddf6cfb57da3ebdf5cfa97d43e8df44fa17d03e7df3cf9d7ce3e5df2cf917c813309964c6262130c9824c025f92f09764b925c12dc96c4b125792b89584ab255129c94c4a4251928894249c24d126492e49624a924892248f247108c84041d20e106482e414208904081a3ff1fe0fe47f03f51570ab054e2a51520a8854029b14c8a605142881418a04500052028813c08c028
def ridgeSupport552_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport552_code
def ridgeSupport552_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport552_code
def ridgeSupport552_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport552_code
def ridgeSupport552_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport552_code
def ridgeSupport552_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport552_code
def ridgeSupport552_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport552_code
def ridgeSupport552_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport552_code
def ridgeSupport552_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport552_code
def ridgeSupport552_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport552_code
def ridgeSupport552_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport552_code
def ridgeSupport552_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 281 ridgeSupport552_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
