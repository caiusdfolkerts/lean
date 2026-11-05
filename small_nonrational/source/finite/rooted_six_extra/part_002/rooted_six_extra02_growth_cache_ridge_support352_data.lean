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
def ridgeSupport352_000 : List Nat := [48,78,88,97,99,627,628,629,630,637,638,771,773,775,777,779,784,785,787,790,813,814,818,820,821,825,827,828,830,1001,1002,1003]
def ridgeSupport352_001 : List Nat := [1004,1011,1012,1145,1147,1149,1151,1153,1158,1159,1161,1164,1187,1188,1192,1194,1195,1199,1201,1202,1204,1254,1256,1258,1260,1262,1267,1268,1270,1273,1296,1297]
def ridgeSupport352_002 : List Nat := [1301,1303,1304,1308,1310,1311,1313,1364,1366,1367,1369,1370,1372,1374,1375,1377,1378,1382,1383,3747,3749,3758,3763,3814,3815,3824,3825,3837,3840,3846,3847,3851]
def ridgeSupport352_003 : List Nat := [3853,3856,3857,3862,3863,3872,3873,3910,3911,3915,3917,3920,3921,3926,3931,3942,3943,3952,3953,3966,3967,3976,3977,3987,3989,3998,4003,4054,4055,4064,4065,4077]
def ridgeSupport352_004 : List Nat := [4080,4086,4087,4091,4093,4096,4097,4102,4103,4112,4113,4150,4151,4155,4157,4160,4161,4166,4171,4182,4183,4192,4193,4206,4207,4216,4217,4226,4231,4238,4243,4258]
def ridgeSupport352_005 : List Nat := [4259,4270,4271,4371,4373,4383,4385,4404,4405,4416,4417,4515,4517,4526,4531,4582,4583,4592,4593,4605,4608,4614,4615,4619,4621,4624,4625,4630,4631,4640,4641,4678]
def ridgeSupport352_006 : List Nat := [4679,4683,4685,4688,4689,4694,4699,4710,4711,4720,4721,4734,4735,4744,4745,4764,4765,4772,4773,4850,4855,4862,4867,4882,4883,4894,4895,4995,4997,5007,5009,5028]
def ridgeSupport352_007 : List Nat := [5029,5040,5041,5265,5268,5271,5275,5277,5280,5283,5287,5290,5291,5304,5305,5313,5316,5319,5323,5326,5327,5340,5341,5704,5705,5740,5741,5800,5801,6334,6335,6344]
def ridgeSupport352_008 : List Nat := [6345,6358,6359,6362,6364,6365,6366,6382,6383,6392,6393,6406,6407,6410,6412,6413,6414,6429,6430,6431,6432,6464,6466,6468,6469,6502,6503,6512,6513,6526,6527,6530]
def ridgeSupport352_009 : List Nat := [6532,6533,6534,6549,6550,6551,6552,6584,6586,6588,6589]
def ridgeSupport352_code : Nat := 0x66f73799bacdc666332f996ccae61b30b984cc165ff2fd971cb8659f2cd945ca2650b281920c8fe47b23b90ec86e433215907c8363e71f18efc77637b1bb8dcc6d635f1ad8c9c6462ff17d6a9b5459b6cd9649b2453769b94cfa67532e98f4c4a60d2e69714aba55529e9474a0a4ed26e92f494a48cec67613a59d24e4671f3859c1cc7e63d3139894c0e5fd2f79794a9654929d94e4a2651127f93f49c64e1267933496e4ad2519284936497247923488644121790b484642120d905c81e40d2008fec7c63e11e78f346ce35d1a58d1c50628113589a448623f115889c2be15d0a3851424e11d08784141e60f106f83741860c105782b412e08d04182040f607703781b40460210078034006000ffd7fdbfddfecff07f6bf85fc0fd77eb3e8df3cf957c9be25f10f7f7bf3dc5ee0f677b33d6deacf517a83d35e96f477a33c85e40f1778b3c45e20f0d785bc1de0cf0077ebbc5de0ee77733acdd5cea5751959cacc5622b0957cabc55c2ad1564aae5562aa1484a3e51e28e1460a2e51528894409f24f627a13cc9dc4ec27513a09cc4b425912c495e4ab25512a09484a3246122490e48624091fc8fa47b23c8fd07e63ec1f58fa87d233e19e0cec67233519a0cc865c32d18b0c4c6223101858c2460e30518189f84fa27613a89d04e6063030816009c030
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
def ridgeSupport352_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport352_code
def ridgeSupport352_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport352_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
