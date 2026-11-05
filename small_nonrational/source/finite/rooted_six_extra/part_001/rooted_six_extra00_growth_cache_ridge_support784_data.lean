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
def ridgeSupport784_000 : List Nat := [60,84,104,120,123,124,683,684,685,686,693,694,839,840,841,842,849,850,978,979,980,983,984,989,990,995,997,999,1000,1001,1004,1005]
def ridgeSupport784_001 : List Nat := [1010,1011,1016,1018,1260,1261,1264,1265,1268,1269,1315,1316,1317,1320,1321,1326,1327,1332,1334,1336,1337,1338,1341,1342,1347,1348,1353,1355,1525,1526,1529,1530]
def ridgeSupport784_002 : List Nat := [1533,1534,1580,1581,1582,1585,1586,1591,1592,1597,1599,1601,1602,1603,1606,1607,1612,1613,1618,1620,1772,1776,1777,1778,1779,1781,1782,1789,1791,1793,1797,1798]
def ridgeSupport784_003 : List Nat := [1799,1800,1802,1803,1810,1812,1814,1815,1819,1820,1821,1822,1824,1825,1833,1835,1836,1838,4170,4172,4176,4178,4256,4257,4262,4263,4264,4265,4270,4271,4276,4278]
def ridgeSupport784_004 : List Nat := [4282,4284,4304,4305,4310,4311,4338,4340,4344,4346,4352,4353,4358,4359,4360,4361,4366,4367,4384,4385,4390,4391,4410,4412,4416,4418,4496,4497,4502,4503,4504,4505]
def ridgeSupport784_005 : List Nat := [4510,4511,4516,4518,4522,4524,4544,4545,4550,4551,4578,4580,4584,4586,4592,4593,4598,4599,4600,4601,4606,4607,4624,4625,4630,4631,4800,4802,4812,4814,4828,4829]
def ridgeSupport784_006 : List Nat := [4840,4841,4872,4874,4884,4886,4900,4901,4912,4913,4938,4940,4944,4946,5024,5025,5030,5031,5032,5033,5038,5039,5044,5046,5050,5052,5072,5073,5078,5079,5106,5108]
def ridgeSupport784_007 : List Nat := [5112,5114,5120,5121,5126,5127,5128,5129,5134,5135,5152,5153,5158,5159,5328,5330,5340,5342,5356,5357,5368,5369,5400,5402,5412,5414,5428,5429,5440,5441,6258,6260]
def ridgeSupport784_008 : List Nat := [6264,6266,6296,6297,6302,6303,6344,6345,6350,6351,6352,6353,6358,6359,6364,6366,6370,6372,6378,6380,6384,6386,6392,6393,6398,6399,6440,6441,6446,6447,6464,6465]
def ridgeSupport784_009 : List Nat := [6470,6471,6618,6620,6648,6650,6658,6659,6676,6677,6690,6692,6720,6722,6730,6731,6748,6749,6906,6908,6936,6938,6946,6947,6964,6965,6978,6980,7008,7010,7018,7019]
def ridgeSupport784_010 : List Nat := [7036,7037,7360,7361,7396,7397,7456,7457,7622,7623,8192,8193,8198,8199,8200,8201,8203,8205,8206,8207,8240,8241,8246,8247,8248,8249,8251,8253,8254,8255,8308,8309]
def ridgeSupport784_011 : List Nat := [8311,8313,8326,8327,8329,8331,8360,8361,8366,8367,8368,8369,8371,8373,8374,8375,8428,8429,8431,8433,8446,8447,8449,8451,8644,8646,8650,8652,8668,8669,8671,8673]
def ridgeSupport784_012 : List Nat := [8674,8675,8722,8723,8725,8727,8740,8741,8743,8745,8794,8795,8797,8799,8812,8813,8815,8817]
def ridgeSupport784_code : Nat := 0x89c626f89b626c897e25d896e25a88a62278896224885e215884e212878e1e287861df87761dc87321ca871a1c4840e10183fe0fe83c60ef83b60ec82de0b682d60b382c60b082be0ae82a60a8822e089821e08681e607781d607480fe03e80f603b80e603880de03680c6030803e00e803600b8026008801e0068006000771ddc67485d207395ce47305cc06df5b7c6dadb6a6d89b606d11b426cd5b346c8db226c69b186bf1afa6975a5c692da4a6909a406891a226855a14680da0267e99f867719da651d946650594064bd92e64a592863fd8fe63e58f863c98f063b18ea63918e263798dc635d8d663458d0633d8ce63258c8627d89e626589861e987861d1872550554054d55345499524546951853e54f853b54ec53794dc53494d0509d4265085420503d40e5025408501d40650054004fe93f84fd13f24f5d3d64f453d04ef13ba4ed93b44ebd3ae4ea53a84e9d3a64e853a04d493504d3134a4cc53304c953244c593144c293084ba52e84b752dc4b392cc4b092c0485d216484521047fd1fe47e51f847dd1f647c51f047a91e847911e2471d1c647051c046b11aa46991a4467d19e4665198465d1964645190450914044f113a449d1264485120443d10e4425108441d106440510043e90f843d10f2435d0d643450d042f10ba42d90b442bd0ae42a50a8429d0a642850a04149050413104a1cb872c1cac7291c847201c7871d1c7071b1c5c7161c507121c2c70a1c207071c187051c046ff1bf46f61bd46f31bc86f11bc06ec1950652193464c191c646190c642190463f18f463818dc63218c462e18b462c17f85fd17e85f917d85f5152c549151054314f853d14e853914e053614d052f14b852914a0525149052313d44f413c44f013b44ec0fe83f80fcc3f20fb43ec0fa43e80f9c3e50f8c3de0f743d80f5c3d40f4c3d20d483510d283490d203470ad82b50ab82ad0ab02ab01f007b01e0068015003c
def ridgeSupport784_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport784_code
def ridgeSupport784_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport784_code
def ridgeSupport784_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport784_code
def ridgeSupport784_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport784_code
def ridgeSupport784_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport784_code
def ridgeSupport784_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport784_code
def ridgeSupport784_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport784_code
def ridgeSupport784_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport784_code
def ridgeSupport784_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport784_code
def ridgeSupport784_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport784_code
def ridgeSupport784_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport784_code
def ridgeSupport784_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport784_code
def ridgeSupport784_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport784_code
def ridgeSupport784_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport784_code
def ridgeSupport784_suffix_013 : List Nat := []
def ridgeSupport784_suffix_012 : List Nat := ridgeSupport784_012 ++ ridgeSupport784_suffix_013
def ridgeSupport784_suffix_011 : List Nat := ridgeSupport784_011 ++ ridgeSupport784_suffix_012
def ridgeSupport784_suffix_010 : List Nat := ridgeSupport784_010 ++ ridgeSupport784_suffix_011
def ridgeSupport784_suffix_009 : List Nat := ridgeSupport784_009 ++ ridgeSupport784_suffix_010
def ridgeSupport784_suffix_008 : List Nat := ridgeSupport784_008 ++ ridgeSupport784_suffix_009
def ridgeSupport784_suffix_007 : List Nat := ridgeSupport784_007 ++ ridgeSupport784_suffix_008
def ridgeSupport784_suffix_006 : List Nat := ridgeSupport784_006 ++ ridgeSupport784_suffix_007
def ridgeSupport784_suffix_005 : List Nat := ridgeSupport784_005 ++ ridgeSupport784_suffix_006
def ridgeSupport784_suffix_004 : List Nat := ridgeSupport784_004 ++ ridgeSupport784_suffix_005
def ridgeSupport784_suffix_003 : List Nat := ridgeSupport784_003 ++ ridgeSupport784_suffix_004
def ridgeSupport784_suffix_002 : List Nat := ridgeSupport784_002 ++ ridgeSupport784_suffix_003
def ridgeSupport784_suffix_001 : List Nat := ridgeSupport784_001 ++ ridgeSupport784_suffix_002
def ridgeSupport784_suffix_000 : List Nat := ridgeSupport784_000 ++ ridgeSupport784_suffix_001
theorem ridgeSupport784_source : candidateSupports 784 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport784_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
