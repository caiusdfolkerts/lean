module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_code_3 704
cert_ridgeSupport_rest_2 704 000 0
cert_ridgeSupport_rest_2 704 001 384
cert_ridgeSupport_rest_2 704 002 768
cert_ridgeSupport_rest_2 704 003 1152
cert_ridgeSupport_rest_2 704 004 1536
cert_ridgeSupport_rest_2 704 005 1920
cert_ridgeSupport_rest_2 704 006 2304
cert_ridgeSupport_rest_2 704 007 2688
cert_ridgeSupport_rest_2 704 008 3072
cert_ridgeSupport_rest_2 704 009 3456
cert_ridgeSupport_rest_2 704 010 3828
cert_ridgeSupport_suffix_4 704 010
cert_ridgeSupport_suffix_3 704 009 010
cert_ridgeSupport_suffix_3 704 008 009
cert_ridgeSupport_suffix_3 704 007 008
cert_ridgeSupport_suffix_3 704 006 007
cert_ridgeSupport_suffix_3 704 005 006
cert_ridgeSupport_suffix_3 704 004 005
cert_ridgeSupport_suffix_3 704 003 004
cert_ridgeSupport_suffix_3 704 002 003
cert_ridgeSupport_suffix_3 704 001 002
cert_ridgeSupport_suffix_3 704 000 001
cert_ridgeSupport_source_3 704 12 319
end Papers.RationalityTen.RootedCaches.RootedSixExtra06
