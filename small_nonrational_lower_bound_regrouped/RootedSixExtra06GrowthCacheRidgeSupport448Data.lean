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
def ridgeSupport448_000 : List Nat := [27,47,77,87,97,101,105,178,179,180,181,182,183,193,194,195,196,197,198,334,335,336,337,338,339,349,350,351,352,353,354,418]
def ridgeSupport448_001 : List Nat := [419,420,421,422,423,433,434,435,436,437,438,502,503,504,508,510,511,515,517,518,520,521,523,599,600,601,602,603,604,614,615,616]
def ridgeSupport448_002 : List Nat := [617,618,619,683,684,685,686,687,688,698,699,700,701,702,703,767,768,769,773,775,776,780,782,783,785,786,788,864,865,866,867,868]
def ridgeSupport448_003 : List Nat := [869,879,880,881,882,883,884,1020,1021,1022,1023,1024,1025,1035,1036,1037,1038,1039,1040,1104,1105,1106,1107,1108,1109,1119,1120,1121,1122,1123,1124,1188]
def ridgeSupport448_004 : List Nat := [1189,1190,1194,1196,1197,1201,1203,1204,1206,1207,1209,1213,1214,1215,1216,1217,1218,1228,1229,1230,1231,1232,1233,1297,1298,1299,1303,1305,1306,1310,1312,1313]
def ridgeSupport448_005 : List Nat := [1315,1316,1318,1322,1323,1324,1325,1326,1327,1337,1338,1339,1340,1341,1342,1406,1407,1408,1412,1414,1415,1419,1421,1422,1424,1425,1427,1431,1432,1433,1437,1439]
def ridgeSupport448_006 : List Nat := [1440,1444,1446,1447,1449,1450,1452,1456,1458,1460,1461,1462,1464,1466,1467,1468,1470,1472,1473,1504,1506,1508,1509,1510,1512,1514,1515,1516,1518,1520,1521,1552]
def ridgeSupport448_007 : List Nat := [1554,1556,1557,1558,1560,1562,1563,1564,1566,1568,1569,1672,1674,1676,1677,1678,1680,1682,1683,1684,1686,1688,1689,1720,1722,1724,1725,1726,1728,1730,1731,1732]
def ridgeSupport448_008 : List Nat := [1734,1736,1737,1840,1842,1844,1845,1846,1848,1850,1851,1852,1854,1856,1857,1888,1890,1892,1893,1894,1896,1898,1899,1900,1902,1904,1905,2008,2010,2012,2013,2014]
def ridgeSupport448_009 : List Nat := [2016,2018,2019,2020,2022,2024,2025,2056,2058,2060,2061,2062,2064,2066,2067,2068,2070,2072,2073,2176,2178,2180,2181,2182,2184,2186,2187,2188,2190,2192,2193]
cert_ridgeSupport_code_3 448
cert_ridgeSupport_rest_2 448 000 0
cert_ridgeSupport_rest_2 448 001 384
cert_ridgeSupport_rest_2 448 002 768
cert_ridgeSupport_rest_2 448 003 1152
cert_ridgeSupport_rest_2 448 004 1536
cert_ridgeSupport_rest_2 448 005 1920
cert_ridgeSupport_rest_2 448 006 2304
cert_ridgeSupport_rest_2 448 007 2688
cert_ridgeSupport_rest_2 448 008 3072
cert_ridgeSupport_rest_2 448 009 3456
cert_ridgeSupport_rest_2 448 010 3828
cert_ridgeSupport_suffix_4 448 010
cert_ridgeSupport_suffix_3 448 009 010
cert_ridgeSupport_suffix_3 448 008 009
cert_ridgeSupport_suffix_3 448 007 008
cert_ridgeSupport_suffix_3 448 006 007
cert_ridgeSupport_suffix_3 448 005 006
cert_ridgeSupport_suffix_3 448 004 005
cert_ridgeSupport_suffix_3 448 003 004
cert_ridgeSupport_suffix_3 448 002 003
cert_ridgeSupport_suffix_3 448 001 002
cert_ridgeSupport_suffix_3 448 000 001
cert_ridgeSupport_source_3 448 12 319
end Papers.RationalityTen.RootedCaches.RootedSixExtra06
