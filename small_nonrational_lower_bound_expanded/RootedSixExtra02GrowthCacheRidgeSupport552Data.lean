module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_code_3 552
cert_ridgeSupport_rest_2 552 000 0
cert_ridgeSupport_rest_2 552 001 416
cert_ridgeSupport_rest_2 552 002 832
cert_ridgeSupport_rest_2 552 003 1248
cert_ridgeSupport_rest_2 552 004 1664
cert_ridgeSupport_rest_2 552 005 2080
cert_ridgeSupport_rest_2 552 006 2496
cert_ridgeSupport_rest_2 552 007 2912
cert_ridgeSupport_rest_2 552 008 3328
cert_ridgeSupport_rest_2 552 009 3653
cert_ridgeSupport_suffix_4 552 009
cert_ridgeSupport_suffix_3 552 008 009
cert_ridgeSupport_suffix_3 552 007 008
cert_ridgeSupport_suffix_3 552 006 007
cert_ridgeSupport_suffix_3 552 005 006
cert_ridgeSupport_suffix_3 552 004 005
cert_ridgeSupport_suffix_3 552 003 004
cert_ridgeSupport_suffix_3 552 002 003
cert_ridgeSupport_suffix_3 552 001 002
cert_ridgeSupport_suffix_3 552 000 001
cert_ridgeSupport_source_3 552 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
