module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport280_000 : List Nat := [47,97,100,102,104,792,793,795,800,802,816,817,819,824,826,839,842,844,847,849,1477,1479,1482,1483,1485,1501,1503,1506,1507,1509,1526,1528]
def ridgeSupport280_001 : List Nat := [1529,1532,1534,1537,1538,1540,1541,1544,1545,1546,1548,1549,1551,1556,1557,1579,1581,1582,1584,1585,1587,1589,1590,1592,1593,1596,1597,1600,1602,1603,1605,1606]
def ridgeSupport280_002 : List Nat := [1608,1610,1611,1613,1614,1617,1618,4938,4939,4944,4945,4948,4949,4950,4951,4952,4953,4958,4959,4962,4963,4968,4969,4972,4973,4974,4975,4976,4977,4982,4983,4996]
def ridgeSupport280_003 : List Nat := [4997,4998,4999,5000,5001,5020,5021,5022,5023,5024,5025,5044,5045,5046,5047,5048,5049,5068,5069,5070,5071,5072,5073,5092,5093,5094,5095,5096,5097,5116,5117,5118]
def ridgeSupport280_004 : List Nat := [5119,5120,5121,5129,5132,5135,5138,5140,5141,5142,5143,5144,5145,5146,5148,5198,5199,5210,5211,5212,5214,5218,5220,5234,5235,5246,5247,5340,5341,5352,5353,5357]
def ridgeSupport280_005 : List Nat := [5360,5363,5366,5376,5377,5388,5389,5412,5413,5424,5425,5429,5432,5435,5438,5448,5449,5460,5461,6764,6765,6776,6777,6800,6801,6812,6813,6820,6822,6826,6828,6906]
def ridgeSupport280_006 : List Nat := [6907,6918,6919,6942,6943,6954,6955,6965,6968,6971,6974,6978,6979,6990,6991,7014,7015,7026,7027,7037,7040,7043,7046,7444,7445,7446,7447,7448,7449,8356,8357,8358]
def ridgeSupport280_007 : List Nat := [8359,8360,8361,8369,8372,8375,8377,8378,8379,8381,8384,8387,8389,8390,8391,8396,8397,8402,8403,8430,8431,8436,8437,8448,8449,8454,8455,8758,8760,8764,8766,8795]
cert_ridgeSupport_7 280 008 8798 8801 8804 8813 8816 8819 8822
cert_ridgeSupport_code_3 280
cert_ridgeSupport_rest_2 280 000 0
cert_ridgeSupport_rest_2 280 001 448
cert_ridgeSupport_rest_2 280 002 896
cert_ridgeSupport_rest_2 280 003 1344
cert_ridgeSupport_rest_2 280 004 1792
cert_ridgeSupport_rest_2 280 005 2240
cert_ridgeSupport_rest_2 280 006 2688
cert_ridgeSupport_rest_2 280 007 3136
cert_ridgeSupport_rest_2 280 008 3584
cert_ridgeSupport_rest_2 280 009 3682
cert_ridgeSupport_suffix_4 280 009
cert_ridgeSupport_suffix_3 280 008 009
cert_ridgeSupport_suffix_3 280 007 008
cert_ridgeSupport_suffix_3 280 006 007
cert_ridgeSupport_suffix_3 280 005 006
cert_ridgeSupport_suffix_3 280 004 005
cert_ridgeSupport_suffix_3 280 003 004
cert_ridgeSupport_suffix_3 280 002 003
cert_ridgeSupport_suffix_3 280 001 002
cert_ridgeSupport_suffix_3 280 000 001
cert_ridgeSupport_source_3 280 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
