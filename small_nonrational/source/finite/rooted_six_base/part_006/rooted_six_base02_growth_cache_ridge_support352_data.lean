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
def ridgeSupport352_000 : List Nat := [48,78,88,97,99,627,628,629,630,637,638,771,773,775,777,779,784,785,787,790,813,814,818,820,821,825,827,828,830,1001,1002,1003]
def ridgeSupport352_001 : List Nat := [1004,1011,1012,1145,1147,1149,1151,1153,1158,1159,1161,1164,1187,1188,1192,1194,1195,1199,1201,1202,1204,1254,1256,1258,1260,1262,1267,1268,1270,1273,1296,1297]
def ridgeSupport352_002 : List Nat := [1301,1303,1304,1308,1310,1311,1313,1364,1366,1367,1369,1370,1372,1374,1375,1377,1378,1382,1383,3747,3749,3758,3763,3814,3815,3824,3825,3837,3840,3846,3847,3851]
def ridgeSupport352_003 : List Nat := [3853,3856,3857,3862,3863,3872,3873,3910,3911,3915,3917,3920,3921,3926,3931,3942,3943,3952,3953,3966,3967,3976,3977,3987,3989,3998,4003,4054,4055,4064,4065,4077]
def ridgeSupport352_004 : List Nat := [4080,4086,4087,4091,4093,4096,4097,4102,4103,4112,4113,4150,4151,4155,4157,4160,4161,4166,4171,4182,4183,4192,4193,4206,4207,4216,4217,4226,4231,4238,4243,4258]
def ridgeSupport352_005 : List Nat := [4259,4270,4271,4371,4373,4383,4385,4404,4405,4416,4417,4515,4517,4526,4531,4582,4583,4592,4593,4605,4608,4614,4615,4619,4621,4624,4625,4630,4631,4640,4641,4678]
def ridgeSupport352_006 : List Nat := [4679,4683,4685,4688,4689,4694,4699,4710,4711,4720,4721,4734,4735,4744,4745,4764,4765,4772,4773,4850,4855,4862,4867,4882,4883,4894,4895,4995,4997,5007,5009,5028]
def ridgeSupport352_007 : List Nat := [5029,5040,5041,6513,6516,6519,6523,6537,6540,6546,6547,6551,6553,6556,6557,6562,6563,6572,6573,6594,6595,6604,6605,6610,6611,6615,6617,6620,6621,6626,6631,6636]
def ridgeSupport352_008 : List Nat := [6637,6641,6643,6645,6648,6651,6655,6669,6672,6678,6679,6683,6685,6688,6689,6694,6695,6704,6705,6726,6727,6736,6737,6742,6743,6747,6749,6752,6753,6758,6763,6768]
def ridgeSupport352_009 : List Nat := [6769,6773,6775,6778,6779,6782,6787,6790,6791,6794,6799,6814,6815,6826,6827,6888,6889,6891,6893,6900,6901,6903,6905,6924,6925,6936,6937,6993,6996,6999,7003,7017]
def ridgeSupport352_010 : List Nat := [7020,7026,7027,7031,7033,7036,7037,7042,7043,7052,7053,7074,7075,7084,7085,7090,7091,7095,7097,7100,7101,7106,7111,7116,7117,7121,7123,7128,7129,7150,7151,7154]
def ridgeSupport352_011 : List Nat := [7159,7162,7163,7166,7171,7186,7187,7198,7199,7260,7261,7263,7265,7272,7273,7275,7277,7296,7297,7308,7309,7497,7500,7503,7507,7509,7512,7515,7519,7522,7523,7536]
def ridgeSupport352_012 : List Nat := [7537,7545,7548,7551,7555,7558,7559,7572,7573,7936,7937,7972,7973,8032,8033]
def ridgeSupport352_code : Nat := 0x7d87ec1f25f927c07e01d95eca761fb0dd83ebff5f3af3d71eb8758fac5d5feadf563aabd53ea7f533a93c8de467207901c6de35f1a78d1c61e2ff1778b9c1fe0f704f825c03dff6fef7f5bf7df96fbf7ddbd9dec6f4f7a3bcdde66f1f785bbddde6ee776fbb3dd96eb7759ba3dd16e37719b83dc16df76f9b79dbbedcf6e5b6cdb4ed6f6afb54da8ec67631b0dd866be75efaf5d7a6bb75d7ae9d746aaf555a9fd4f6a3f515a87d436a0f4fda7bd3d69df4eba71d3869af4cda61d3069774b7a57d2b69474a1a47d2368c7461a27d136887441a1dd0de85f42da10d06e7ff3f79f8cfae7cf3e39edcf6679f3c59ddcee67673af9d3ce967373999c3ce166b73599a3cd16677339999ccbe64f32598ccc4e5ef2ef974cb8cec67613a59d24e4671f3859c1cc7e63d3139894c0e5fd2f79794a9654929d94e4a2651127f93f49c64e1267933496e4ad2519284936497247923488644121790b484642120d905c81e40d2008fec7c63e11e78f346ce35d1a58d1c50628113589a448623f115889c2be15d0a3851424e11d08784141e60f106f83741860c105782b412e08d04182040f607703781b40460210078034006000ffd7fdbfddfecff07f6bf85fc0fd77eb3e8df3cf957c9be25f10f7f7bf3dc5ee0f677b33d6deacf517a83d35e96f477a33c85e40f1778b3c45e20f0d785bc1de0cf0077ebbc5de0ee77733acdd5cea5751959cacc5622b0957cabc55c2ad1564aae5562aa1484a3e51e28e1460a2e51528894409f24f627a13cc9dc4ec27513a09cc4b425912c495e4ab25512a09484a3246122490e48624091fc8fa47b23c8fd07e63ec1f58fa87d233e19e0cec67233519a0cc865c32d18b0c4c6223101858c2460e30518189f84fa27613a89d04e6063030816009c030
def ridgeSupport352_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport352_code
def ridgeSupport352_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport352_code
def ridgeSupport352_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport352_code
def ridgeSupport352_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport352_code
def ridgeSupport352_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport352_code
def ridgeSupport352_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport352_code
def ridgeSupport352_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport352_code
def ridgeSupport352_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport352_code
def ridgeSupport352_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport352_code
def ridgeSupport352_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport352_code
def ridgeSupport352_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport352_code
def ridgeSupport352_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport352_code
def ridgeSupport352_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport352_code
def ridgeSupport352_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport352_code
def ridgeSupport352_suffix_013 : List Nat := []
def ridgeSupport352_suffix_012 : List Nat := ridgeSupport352_012 ++ ridgeSupport352_suffix_013
def ridgeSupport352_suffix_011 : List Nat := ridgeSupport352_011 ++ ridgeSupport352_suffix_012
def ridgeSupport352_suffix_010 : List Nat := ridgeSupport352_010 ++ ridgeSupport352_suffix_011
def ridgeSupport352_suffix_009 : List Nat := ridgeSupport352_009 ++ ridgeSupport352_suffix_010
def ridgeSupport352_suffix_008 : List Nat := ridgeSupport352_008 ++ ridgeSupport352_suffix_009
def ridgeSupport352_suffix_007 : List Nat := ridgeSupport352_007 ++ ridgeSupport352_suffix_008
def ridgeSupport352_suffix_006 : List Nat := ridgeSupport352_006 ++ ridgeSupport352_suffix_007
def ridgeSupport352_suffix_005 : List Nat := ridgeSupport352_005 ++ ridgeSupport352_suffix_006
def ridgeSupport352_suffix_004 : List Nat := ridgeSupport352_004 ++ ridgeSupport352_suffix_005
def ridgeSupport352_suffix_003 : List Nat := ridgeSupport352_003 ++ ridgeSupport352_suffix_004
def ridgeSupport352_suffix_002 : List Nat := ridgeSupport352_002 ++ ridgeSupport352_suffix_003
def ridgeSupport352_suffix_001 : List Nat := ridgeSupport352_001 ++ ridgeSupport352_suffix_002
def ridgeSupport352_suffix_000 : List Nat := ridgeSupport352_000 ++ ridgeSupport352_suffix_001
theorem ridgeSupport352_source : candidateSupports 352 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport352_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
