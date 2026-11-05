module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport400_000 : List Nat := [58,82,102,118,121,124,659,660,661,662,669,670,815,816,817,818,825,826,936,937,938,941,942,947,948,953,955,998,999,1003,1005,1006]
def ridgeSupport400_001 : List Nat := [1010,1012,1013,1015,1236,1237,1240,1241,1244,1245,1273,1274,1275,1278,1279,1284,1285,1290,1292,1335,1336,1340,1342,1343,1347,1349,1350,1352,1501,1502,1505,1506]
def ridgeSupport400_002 : List Nat := [1509,1510,1538,1539,1540,1543,1544,1549,1550,1555,1557,1600,1601,1605,1607,1608,1612,1614,1615,1617,1730,1734,1735,1736,1737,1739,1740,1747,1749,1795,1796,1797]
def ridgeSupport400_003 : List Nat := [1800,1801,1802,1804,1809,1811,1814,1817,1818,1819,1822,1823,1824,1826,1831,1832,1834,1835,4169,4171,4188,4190,4248,4249,4254,4255,4268,4269,4271,4274,4277,4280]
def ridgeSupport400_004 : List Nat := [4282,4283,4296,4297,4302,4303,4337,4339,4344,4345,4350,4351,4356,4358,4364,4365,4378,4379,4388,4389,4402,4403,4409,4411,4428,4430,4488,4489,4494,4495,4508,4509]
def ridgeSupport400_005 : List Nat := [4511,4514,4517,4520,4522,4523,4536,4537,4542,4543,4577,4579,4584,4585,4590,4591,4596,4598,4604,4605,4618,4619,4628,4629,4642,4643,4656,4658,4668,4670,4684,4685]
def ridgeSupport400_006 : List Nat := [4696,4697,4871,4873,4883,4885,4904,4905,4916,4917,4937,4939,4956,4958,5016,5017,5022,5023,5036,5037,5039,5042,5045,5048,5050,5051,5064,5065,5070,5071,5105,5107]
def ridgeSupport400_007 : List Nat := [5112,5113,5118,5119,5124,5126,5132,5133,5146,5147,5156,5157,5170,5171,5184,5186,5196,5198,5212,5213,5224,5225,5399,5401,5411,5413,5432,5433,5444,5445,6257,6259]
def ridgeSupport400_008 : List Nat := [6276,6278,6288,6289,6294,6295,6336,6337,6342,6343,6356,6357,6359,6362,6365,6368,6370,6371,6377,6379,6384,6385,6390,6391,6396,6398,6432,6433,6438,6439,6456,6457]
def ridgeSupport400_009 : List Nat := [6462,6463,6474,6476,6504,6506,6514,6515,6532,6533,6689,6691,6719,6721,6734,6735,6752,6753,6762,6764,6792,6794,6802,6803,6820,6821,6977,6979,7007,7009,7022,7023]
def ridgeSupport400_010 : List Nat := [7040,7041,7364,7365,7400,7401,7460,7461,7618,7619,8184,8185,8190,8191,8200,8202,8204,8205,8208,8211,8232,8233,8238,8239,8248,8250,8252,8253,8256,8259,8272,8273]
def ridgeSupport400_011 : List Nat := [8275,8277,8326,8328,8330,8331,8352,8353,8358,8359,8368,8370,8372,8373,8376,8379,8392,8393,8395,8397,8446,8448,8450,8451,8639,8642,8645,8648,8668,8670,8672,8673]
def ridgeSupport400_012 : List Nat := [8676,8679,8686,8687,8689,8691,8740,8742,8744,8745,8758,8759,8761,8763,8812,8814,8816,8817]
def ridgeSupport400_code : Nat := 0x89c627089ba26c88ee23988de23688a6228889a22487ce1f187be1ee879e1e487861e0877a1dc87221c5870a1bf840e10284020fe83360cb83260c882ee0b882d60b482ca0b0829e0a682860a0822e08a822208681560538146050810e04080f603c80ea03880be02e80a6028804e010803600c802a0087ffdffe7fe5ff8770ddc27495d2473a5ce87315cc46e05b806dbdb6e6d85b5f6d0db416a95aa46a4da926a29a8869b1a6a6985a60693da4e6905a3f688da21661598465cd97265a9968653194a64fd93e64e5938649d926648592063f98fc63dd8f663c58f063ad8e9638d8e263818dd63698d763558d4631d8c663058c0625d8966245890621988461cd871551554454e55385495523546551751a5468517545c513944c510944050cd4325095424506d41a503540c50194044ffd3fe4fe53f84fcd3f14f3d3ce4f253c84eed3ba4ee13b54ec93af4eb53ac4e7d39e4e653984d7935c4d2d3494cd53344ca53284c553134c253074965258493524c48f923c48c9230488d2224855214482d20a47f51fc47d91f447bd1ee47a51e8478d1e146fd1be46e51b846ad1aa46a11a5468919f467519c463d18e4625188453914c44ed13944cd1324495124446d11a443510c441910443fd0fe43e50f843cd0f1433d0ce43250c842ed0ba42e10b542c90af42b50ac427d09e4265098417905c412d0491cac72a1ca07271c887201c7c71e1c6c71a1c647161c4c7111c3070a1c247081c147041c0c6d51b4c6cc1b2c6c91b206c71b186c2194464f193864c192064719146411900615184c60e1834608181c604180c60217985e517885e117785dd1520546151454314fc53e14f053814dc50c142850514104ff13f84fb13e84f913744dc13644d813544d40fdc3f50fd03f20fb83ed0fac3e70f983bb0ee43b40ecc3ae0eb43aa0ea43a80ce83390cc83310cc032f0a7829d0a582950a5029301f007901d8066014803a
def ridgeSupport400_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport400_code
def ridgeSupport400_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport400_code
def ridgeSupport400_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport400_code
def ridgeSupport400_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport400_code
def ridgeSupport400_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport400_code
def ridgeSupport400_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport400_code
def ridgeSupport400_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport400_code
def ridgeSupport400_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport400_code
def ridgeSupport400_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport400_code
def ridgeSupport400_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport400_code
def ridgeSupport400_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport400_code
def ridgeSupport400_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport400_code
def ridgeSupport400_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport400_code
def ridgeSupport400_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport400_code
def ridgeSupport400_suffix_013 : List Nat := []
def ridgeSupport400_suffix_012 : List Nat := ridgeSupport400_012 ++ ridgeSupport400_suffix_013
def ridgeSupport400_suffix_011 : List Nat := ridgeSupport400_011 ++ ridgeSupport400_suffix_012
def ridgeSupport400_suffix_010 : List Nat := ridgeSupport400_010 ++ ridgeSupport400_suffix_011
def ridgeSupport400_suffix_009 : List Nat := ridgeSupport400_009 ++ ridgeSupport400_suffix_010
def ridgeSupport400_suffix_008 : List Nat := ridgeSupport400_008 ++ ridgeSupport400_suffix_009
def ridgeSupport400_suffix_007 : List Nat := ridgeSupport400_007 ++ ridgeSupport400_suffix_008
def ridgeSupport400_suffix_006 : List Nat := ridgeSupport400_006 ++ ridgeSupport400_suffix_007
def ridgeSupport400_suffix_005 : List Nat := ridgeSupport400_005 ++ ridgeSupport400_suffix_006
def ridgeSupport400_suffix_004 : List Nat := ridgeSupport400_004 ++ ridgeSupport400_suffix_005
def ridgeSupport400_suffix_003 : List Nat := ridgeSupport400_003 ++ ridgeSupport400_suffix_004
def ridgeSupport400_suffix_002 : List Nat := ridgeSupport400_002 ++ ridgeSupport400_suffix_003
def ridgeSupport400_suffix_001 : List Nat := ridgeSupport400_001 ++ ridgeSupport400_suffix_002
def ridgeSupport400_suffix_000 : List Nat := ridgeSupport400_000 ++ ridgeSupport400_suffix_001
theorem ridgeSupport400_source : candidateSupports 400 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport400_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
