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
def ridgeSupport296_000 : List Nat := [39,69,78,80,82,628,629,631,636,638,652,653,655,660,662,675,678,680,683,685,1001,1004,1005,1008,1011,1025,1028,1029,1032,1035,1050,1051]
def ridgeSupport296_001 : List Nat := [1054,1055,1060,1145,1146,1148,1149,1152,1153,1154,1156,1157,1159,1164,1165,1187,1189,1190,1192,1193,1195,1197,1198,1200,1201,1204,1205,1208,1210,1211,1213,1214]
def ridgeSupport296_002 : List Nat := [1216,1218,1219,1221,1222,1225,1226,3982,3983,3988,3989,3992,3993,3994,3995,3996,3997,4002,4003,4006,4007,4012,4013,4016,4017,4018,4019,4020,4021,4026,4027,4040]
def ridgeSupport296_003 : List Nat := [4041,4042,4043,4044,4045,4064,4065,4066,4067,4068,4069,4088,4089,4090,4091,4092,4093,4112,4113,4114,4115,4116,4117,4136,4137,4138,4139,4140,4141,4160,4161,4162]
def ridgeSupport296_004 : List Nat := [4163,4164,4165,4173,4176,4179,4182,4184,4185,4186,4187,4188,4189,4190,4192,4242,4243,4254,4255,4256,4258,4262,4264,4278,4279,4290,4291,4384,4385,4396,4397,4401]
def ridgeSupport296_005 : List Nat := [4404,4407,4410,4420,4421,4432,4433,4456,4457,4468,4469,4473,4476,4479,4482,4492,4493,4504,4505,4854,4855,4872,4873,4890,4891,4892,4894,4898,4900,4908,4909,4996]
def ridgeSupport296_006 : List Nat := [4997,5014,5015,5032,5033,5037,5040,5043,5046,5050,5051,5068,5069,5086,5087,5104,5105,5109,5112,5115,5118,5122,5123,5278,5279,5282,5283,5286,5287,5288,5290,5301]
def ridgeSupport296_007 : List Nat := [5304,5307,5310,5325,5327,5336,5341,5342,5347,5720,5721,5722,5723,5724,5725,6392,6393,6394,6395,6396,6397,6405,6408,6411,6413,6414,6415,6417,6420,6423,6425,6426]
def ridgeSupport296_008 : List Nat := [6427,6432,6433,6438,6439,6466,6467,6472,6473,6484,6485,6490,6491,6548,6550,6564,6565,6585,6588,6598,6599,6603,6606,6616,6617]
def ridgeSupport296_code : Nat := 0x19d9cec673b3979c7ce366f33739a5cd2665b32995bcad65572a9949ca4650f285927c93648724191bc8d646722f914c88e43f21d90dc85e42320b8fdc7e63ef1f58f9c7c5976cb965bb2d5966cb14e3a6f53769b14cfa66d2fa9774b8a5ad2aa9514a7a53528e94549fa4f500e8053fe9fdcfe27eb3f19f84f7e7bd3cd9e64eee7753b69d9cec275b3a99d44e5e72d3859c24cb66593249914c7a63931b98d4c266112f797b466633118d8c6460a2ff17c8bcc5d62e91698b445462a11458a244ea26f134898c4b6259121890430e1850b785b42a214d0a2850427e13d09384941820bd05d82e416e0b505982c415a0a7050826c116089043821410608102d81640ae05502981440560290138094046020ffd7fe3fedff4ff97fc3f95fc8fe37f13f85fc0fcd7e63f2df94fc97e43eedf74fb57da3ecdf64fb17d83eb5f58fa77d33e8df44f9d7ce3e6df34f997cc3e55f28f8f7c713289924c6262930c9844c025f12f49764ba25c12d49684b125812b895a4ab25492a094c4a52519234918487242921090448124011f48f847a23c909083e41e20d906881640820290108023f31f80fb47d83e91568aac5502a61518a5852828f1468a304fc27c13b89d44e8052028013808a027
def ridgeSupport296_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport296_code
def ridgeSupport296_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport296_code
def ridgeSupport296_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport296_code
def ridgeSupport296_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport296_code
def ridgeSupport296_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport296_code
def ridgeSupport296_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport296_code
def ridgeSupport296_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport296_code
def ridgeSupport296_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport296_code
def ridgeSupport296_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport296_code
def ridgeSupport296_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport296_code
def ridgeSupport296_suffix_009 : List Nat := []
def ridgeSupport296_suffix_008 : List Nat := ridgeSupport296_008 ++ ridgeSupport296_suffix_009
def ridgeSupport296_suffix_007 : List Nat := ridgeSupport296_007 ++ ridgeSupport296_suffix_008
def ridgeSupport296_suffix_006 : List Nat := ridgeSupport296_006 ++ ridgeSupport296_suffix_007
def ridgeSupport296_suffix_005 : List Nat := ridgeSupport296_005 ++ ridgeSupport296_suffix_006
def ridgeSupport296_suffix_004 : List Nat := ridgeSupport296_004 ++ ridgeSupport296_suffix_005
def ridgeSupport296_suffix_003 : List Nat := ridgeSupport296_003 ++ ridgeSupport296_suffix_004
def ridgeSupport296_suffix_002 : List Nat := ridgeSupport296_002 ++ ridgeSupport296_suffix_003
def ridgeSupport296_suffix_001 : List Nat := ridgeSupport296_001 ++ ridgeSupport296_suffix_002
def ridgeSupport296_suffix_000 : List Nat := ridgeSupport296_000 ++ ridgeSupport296_suffix_001
theorem ridgeSupport296_source : candidateSupports 296 =
    (PackedRawNatGrowth.readList 13 281 ridgeSupport296_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
