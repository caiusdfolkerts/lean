module
prelude
public import RootedSixExtra06GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport704_000 : List Nat := [28,48,78,88,98,102,105,199,200,201,202,203,204,214,215,216,217,218,219,355,356,357,358,359,360,370,371,372,373,374,375,439]
def ridgeSupport704_001 : List Nat := [440,441,442,443,444,454,455,456,457,458,459,502,503,505,507,509,511,516,517,519,520,524,526,620,621,622,623,624,625,635,636,637]
def ridgeSupport704_002 : List Nat := [638,639,640,704,705,706,707,708,709,719,720,721,722,723,724,767,768,770,772,774,776,781,782,784,785,789,791,885,886,887,888,889]
def ridgeSupport704_003 : List Nat := [890,900,901,902,903,904,905,1041,1042,1043,1044,1045,1046,1056,1057,1058,1059,1060,1061,1125,1126,1127,1128,1129,1130,1140,1141,1142,1143,1144,1145,1188]
def ridgeSupport704_004 : List Nat := [1189,1191,1193,1195,1197,1202,1203,1205,1206,1210,1212,1234,1235,1236,1237,1238,1239,1249,1250,1251,1252,1253,1254,1297,1298,1300,1302,1304,1306,1311,1312,1314]
def ridgeSupport704_005 : List Nat := [1315,1319,1321,1343,1344,1345,1346,1347,1348,1358,1359,1360,1361,1362,1363,1406,1407,1409,1411,1413,1415,1420,1421,1423,1424,1428,1430,1431,1432,1434,1436,1438]
def ridgeSupport704_006 : List Nat := [1440,1445,1446,1448,1449,1453,1455,1457,1458,1459,1460,1463,1464,1465,1466,1474,1476,1478,1479,1505,1506,1507,1508,1511,1512,1513,1514,1522,1524,1526,1527,1553]
def ridgeSupport704_007 : List Nat := [1554,1555,1556,1559,1560,1561,1562,1570,1572,1574,1575,1673,1674,1675,1676,1679,1680,1681,1682,1690,1692,1694,1695,1721,1722,1723,1724,1727,1728,1729,1730,1738]
def ridgeSupport704_008 : List Nat := [1740,1742,1743,1841,1842,1843,1844,1847,1848,1849,1850,1858,1860,1862,1863,1889,1890,1891,1892,1895,1896,1897,1898,1906,1908,1910,1911,2009,2010,2011,2012,2015]
def ridgeSupport704_009 : List Nat := [2016,2017,2018,2026,2028,2030,2031,2057,2058,2059,2060,2063,2064,2065,2066,2074,2076,2078,2079,2177,2178,2179,2180,2183,2184,2185,2186,2194,2196,2198,2199]
def ridgeSupport704_code : Nat := 0x89789689489288a88988888788488388288181f81e81c81a81281181080f80c80b80a8097ef7ee7ec7ea7e27e17e07df7dc7db7da7d977777677477276a76976876776476376276174774674474273a7397387377347337327316cf6ce6cc6ca6c26c16c06bf6bc6bb6ba6b969f69e69c69a69269169068f68c68b68a68962762662462261a6196186176146136126115f75f65f45f25ea5e95e85e75e45e35e25e15c75c65c45c25ba5b95b85b75b45b35b25b15af5ad5a95a85a65a55a059e59c59a59859759659459058f58d58c58758558358157f57e55355255155054f54e54454354254154053f52952752352252051f51a5185165145125114e64e54e44e34e24e14d74d64d54d44d34d24bc4ba4b64b54b34b24ad4ab4a94a74a54a447947847747647547446a46946846746646542542442342242142041641541441341241138938838738638538437a37937837737637531731531131030e30d3083063043023002ff2d42d32d22d12d02cf2c52c42c32c22c12c028027f27e27d27c27b27127026f26e26d26c20e20c2082072052041ff1fd1fb1f91f71f61cb1ca1c91c81c71c61bc1bb1ba1b91b81b71771761751741731721681671661651641630db0da0d90d80d70d60cc0cb0ca0c90c80c706906606205804e03001c
def ridgeSupport704_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport704_code
def ridgeSupport704_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport704_code
def ridgeSupport704_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport704_code
def ridgeSupport704_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport704_code
def ridgeSupport704_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport704_code
def ridgeSupport704_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport704_code
def ridgeSupport704_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport704_code
def ridgeSupport704_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport704_code
def ridgeSupport704_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport704_code
def ridgeSupport704_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport704_code
def ridgeSupport704_rest_010 : Nat := PackedRawNatGrowth.drop 3828 ridgeSupport704_code
def ridgeSupport704_suffix_010 : List Nat := []
def ridgeSupport704_suffix_009 : List Nat := ridgeSupport704_009 ++ ridgeSupport704_suffix_010
def ridgeSupport704_suffix_008 : List Nat := ridgeSupport704_008 ++ ridgeSupport704_suffix_009
def ridgeSupport704_suffix_007 : List Nat := ridgeSupport704_007 ++ ridgeSupport704_suffix_008
def ridgeSupport704_suffix_006 : List Nat := ridgeSupport704_006 ++ ridgeSupport704_suffix_007
def ridgeSupport704_suffix_005 : List Nat := ridgeSupport704_005 ++ ridgeSupport704_suffix_006
def ridgeSupport704_suffix_004 : List Nat := ridgeSupport704_004 ++ ridgeSupport704_suffix_005
def ridgeSupport704_suffix_003 : List Nat := ridgeSupport704_003 ++ ridgeSupport704_suffix_004
def ridgeSupport704_suffix_002 : List Nat := ridgeSupport704_002 ++ ridgeSupport704_suffix_003
def ridgeSupport704_suffix_001 : List Nat := ridgeSupport704_001 ++ ridgeSupport704_suffix_002
def ridgeSupport704_suffix_000 : List Nat := ridgeSupport704_000 ++ ridgeSupport704_suffix_001
theorem ridgeSupport704_source : candidateSupports 704 =
    (PackedRawNatGrowth.readList 12 319 ridgeSupport704_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
