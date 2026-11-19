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
def ridgeSupport832_000 : List Nat := [29,49,79,89,99,103,105,220,221,222,223,224,225,235,236,237,238,239,240,376,377,378,379,380,381,391,392,393,394,395,396,460]
def ridgeSupport832_001 : List Nat := [461,462,463,464,465,475,476,477,478,479,480,502,504,505,506,509,510,515,516,522,523,525,526,641,642,643,644,645,646,656,657,658]
def ridgeSupport832_002 : List Nat := [659,660,661,725,726,727,728,729,730,740,741,742,743,744,745,767,769,770,771,774,775,780,781,787,788,790,791,906,907,908,909,910]
def ridgeSupport832_003 : List Nat := [911,921,922,923,924,925,926,1062,1063,1064,1065,1066,1067,1077,1078,1079,1080,1081,1082,1146,1147,1148,1149,1150,1151,1161,1162,1163,1164,1165,1166,1188]
def ridgeSupport832_004 : List Nat := [1190,1191,1192,1195,1196,1201,1202,1208,1209,1211,1212,1255,1256,1257,1258,1259,1260,1270,1271,1272,1273,1274,1275,1297,1299,1300,1301,1304,1305,1310,1311,1317]
def ridgeSupport832_005 : List Nat := [1318,1320,1321,1364,1365,1366,1367,1368,1369,1379,1380,1381,1382,1383,1384,1406,1408,1409,1410,1413,1414,1419,1420,1426,1427,1429,1430,1431,1433,1434,1435,1438]
def ridgeSupport832_006 : List Nat := [1439,1444,1445,1451,1452,1454,1455,1456,1457,1459,1461,1469,1470,1471,1472,1475,1476,1477,1478,1504,1505,1507,1509,1517,1518,1519,1520,1523,1524,1525,1526,1552]
def ridgeSupport832_007 : List Nat := [1553,1555,1557,1565,1566,1567,1568,1571,1572,1573,1574,1672,1673,1675,1677,1685,1686,1687,1688,1691,1692,1693,1694,1720,1721,1723,1725,1733,1734,1735,1736,1739]
def ridgeSupport832_008 : List Nat := [1740,1741,1742,1840,1841,1843,1845,1853,1854,1855,1856,1859,1860,1861,1862,1888,1889,1891,1893,1901,1902,1903,1904,1907,1908,1909,1910,2008,2009,2011,2013,2021]
def ridgeSupport832_009 : List Nat := [2022,2023,2024,2027,2028,2029,2030,2056,2057,2059,2061,2069,2070,2071,2072,2075,2076,2077,2078,2176,2177,2179,2181,2189,2190,2191,2192,2195,2196,2197,2198]
cert_ridgeSupport_code_3 832
cert_ridgeSupport_rest_2 832 000 0
cert_ridgeSupport_rest_2 832 001 384
cert_ridgeSupport_rest_2 832 002 768
cert_ridgeSupport_rest_2 832 003 1152
cert_ridgeSupport_rest_2 832 004 1536
cert_ridgeSupport_rest_2 832 005 1920
cert_ridgeSupport_rest_2 832 006 2304
cert_ridgeSupport_rest_2 832 007 2688
cert_ridgeSupport_rest_2 832 008 3072
cert_ridgeSupport_rest_2 832 009 3456
cert_ridgeSupport_rest_2 832 010 3828
cert_ridgeSupport_suffix_4 832 010
cert_ridgeSupport_suffix_3 832 009 010
cert_ridgeSupport_suffix_3 832 008 009
cert_ridgeSupport_suffix_3 832 007 008
cert_ridgeSupport_suffix_3 832 006 007
cert_ridgeSupport_suffix_3 832 005 006
cert_ridgeSupport_suffix_3 832 004 005
cert_ridgeSupport_suffix_3 832 003 004
cert_ridgeSupport_suffix_3 832 002 003
cert_ridgeSupport_suffix_3 832 001 002
cert_ridgeSupport_suffix_3 832 000 001
cert_ridgeSupport_source_3 832 12 319
end Papers.RationalityTen.RootedCaches.RootedSixExtra06
