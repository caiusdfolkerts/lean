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
def ridgeSupport296_000 : List Nat := [39,69,78,80,82,628,629,631,636,638,652,653,655,660,662,675,678,680,683,685,1001,1004,1005,1008,1011,1025,1028,1029,1032,1035,1050,1051]
def ridgeSupport296_001 : List Nat := [1054,1055,1060,1145,1146,1148,1149,1152,1153,1154,1156,1157,1159,1164,1165,1187,1189,1190,1192,1193,1195,1197,1198,1200,1201,1204,1205,1208,1210,1211,1213,1214]
def ridgeSupport296_002 : List Nat := [1216,1218,1219,1221,1222,1225,1226,3982,3983,3988,3989,3992,3993,3994,3995,3996,3997,4002,4003,4006,4007,4012,4013,4016,4017,4018,4019,4020,4021,4026,4027,4040]
def ridgeSupport296_003 : List Nat := [4041,4042,4043,4044,4045,4064,4065,4066,4067,4068,4069,4088,4089,4090,4091,4092,4093,4112,4113,4114,4115,4116,4117,4136,4137,4138,4139,4140,4141,4160,4161,4162]
def ridgeSupport296_004 : List Nat := [4163,4164,4165,4173,4176,4179,4182,4184,4185,4186,4187,4188,4189,4190,4192,4242,4243,4254,4255,4256,4258,4262,4264,4278,4279,4290,4291,4384,4385,4396,4397,4401]
def ridgeSupport296_005 : List Nat := [4404,4407,4410,4420,4421,4432,4433,4456,4457,4468,4469,4473,4476,4479,4482,4492,4493,4504,4505,4854,4855,4872,4873,4890,4891,4892,4894,4898,4900,4908,4909,4996]
def ridgeSupport296_006 : List Nat := [4997,5014,5015,5032,5033,5037,5040,5043,5046,5050,5051,5068,5069,5086,5087,5104,5105,5109,5112,5115,5118,5122,5123,6646,6647,6650,6651,6654,6655,6658,6659,6662]
def ridgeSupport296_007 : List Nat := [6663,6666,6667,6680,6681,6682,6683,6684,6685,6704,6705,6706,6707,6708,6709,6717,6720,6723,6726,6728,6729,6730,6731,6732,6733,6734,6736,6741,6744,6747,6750,6752]
def ridgeSupport296_008 : List Nat := [6753,6754,6755,6756,6757,6758,6760,6764,6766,6767,6769,6774,6775,6776,6778,6782,6784,6798,6799,6810,6811,6812,6814,6818,6820,6825,6827,6885,6888,6891,6894,6904]
def ridgeSupport296_009 : List Nat := [6905,6916,6917,6921,6924,6927,6930,6932,6937,6939,6942,6945,6948,6958,6959,6970,6971,6975,6978,6981,6984,6986,6991,7158,7159,7160,7162,7166,7168,7176,7177,7185]
def ridgeSupport296_010 : List Nat := [7187,7194,7195,7196,7198,7264,7265,7269,7272,7275,7278,7282,7283,7292,7297,7300,7301,7305,7308,7318,7319,7323,7326,7329,7332,7336,7337,7346,7351,7354,7355,7359]
def ridgeSupport296_011 : List Nat := [7362,7510,7511,7514,7515,7518,7519,7520,7522,7533,7536,7539,7542,7557,7559,7568,7573,7574,7579,7952,7953,7954,7955,7956,7957]
def ridgeSupport296_code : Nat := 0x1f15f8a7c4fe25f11f88766fb2dd95ec8761fb0bd76eb9f5c3adbd62eb0757fabdd5bead755faadcc2e5ff2ef975cb7e5972a7951ca4e50f27b937c97e4b7233913c85e4272078f9c73e3971bb8d7c68e32f1878c1c1ee0e706f835c13e08f027811c00dff6feb7f1bf7dfb6d3f695b48da2ed0b67fb3bd9d6cbf65db24d90ec7b637b19d8a6c4b61fb0cd84ec17609af9d7c6bbb5d7ae8d72eaaf553aa4d516a7b539a9bd4d6a3f51da80d3f69eb4f1a77d3b69c74dfa6ed3669a34cda65d32698f4c5a61d30697b4b7a58d2ae94349da4dd26692f495a49d24691b487a40d1ee8d7469a33d1968c7461a1dd0e686f435a19d0c682f415a07d03680f4059ffcff67ef3f59f7cfb500e8053fe9fdcfe27eb3f19f84f7e7bd3cd9e64eee7753b69d9cec275b3a99d44e5e72d3859c24cb66593249914c7a63931b98d4c266112f797b466633118d8c6460a2ff17c8bcc5d62e91698b445462a11458a244ea26f134898c4b6259121890430e1850b785b42a214d0a2850427e13d09384941820bd05d82e416e0b505982c415a0a7050826c116089043821410608102d81640ae05502981440560290138094046020ffd7fe3fedff4ff97fc3f95fc8fe37f13f85fc0fcd7e63f2df94fc97e43eedf74fb57da3ecdf64fb17d83eb5f58fa77d33e8df44f9d7ce3e6df34f997cc3e55f28f8f7c713289924c6262930c9844c025f12f49764ba25c12d49684b125812b895a4ab25492a094c4a52519234918487242921090448124011f48f847a23c909083e41e20d906881640820290108023f31f80fb47d83e91568aac5502a61518a5852828f1468a304fc27c13b89d44e8052028013808a027
def ridgeSupport296_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport296_code
def ridgeSupport296_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport296_code
def ridgeSupport296_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport296_code
def ridgeSupport296_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport296_code
def ridgeSupport296_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport296_code
def ridgeSupport296_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport296_code
def ridgeSupport296_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport296_code
def ridgeSupport296_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport296_code
def ridgeSupport296_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport296_code
def ridgeSupport296_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport296_code
def ridgeSupport296_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport296_code
def ridgeSupport296_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport296_code
def ridgeSupport296_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport296_code
def ridgeSupport296_suffix_012 : List Nat := []
def ridgeSupport296_suffix_011 : List Nat := ridgeSupport296_011 ++ ridgeSupport296_suffix_012
def ridgeSupport296_suffix_010 : List Nat := ridgeSupport296_010 ++ ridgeSupport296_suffix_011
def ridgeSupport296_suffix_009 : List Nat := ridgeSupport296_009 ++ ridgeSupport296_suffix_010
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
    (PackedRawNatGrowth.readList 13 377 ridgeSupport296_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
