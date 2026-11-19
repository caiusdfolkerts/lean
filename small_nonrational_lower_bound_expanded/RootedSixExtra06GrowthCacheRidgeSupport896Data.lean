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
def ridgeSupport896_000 : List Nat := [30,50,80,90,100,104,105,241,242,243,244,245,246,256,257,258,259,260,261,397,398,399,400,401,402,412,413,414,415,416,417,481]
def ridgeSupport896_001 : List Nat := [482,483,484,485,486,496,497,498,499,500,501,503,504,505,506,507,508,518,519,521,522,524,525,662,663,664,665,666,667,677,678,679]
def ridgeSupport896_002 : List Nat := [680,681,682,746,747,748,749,750,751,761,762,763,764,765,766,768,769,770,771,772,773,783,784,786,787,789,790,927,928,929,930,931]
def ridgeSupport896_003 : List Nat := [932,942,943,944,945,946,947,1083,1084,1085,1086,1087,1088,1098,1099,1100,1101,1102,1103,1167,1168,1169,1170,1171,1172,1182,1183,1184,1185,1186,1187,1189]
def ridgeSupport896_004 : List Nat := [1190,1191,1192,1193,1194,1204,1205,1207,1208,1210,1211,1276,1277,1278,1279,1280,1281,1291,1292,1293,1294,1295,1296,1298,1299,1300,1301,1302,1303,1313,1314,1316]
def ridgeSupport896_005 : List Nat := [1317,1319,1320,1385,1386,1387,1388,1389,1390,1400,1401,1402,1403,1404,1405,1407,1408,1409,1410,1411,1412,1422,1423,1425,1426,1428,1429,1432,1433,1434,1435,1436]
def ridgeSupport896_006 : List Nat := [1437,1447,1448,1450,1451,1453,1454,1462,1463,1465,1467,1468,1469,1471,1473,1474,1475,1477,1479,1510,1511,1513,1515,1516,1517,1519,1521,1522,1523,1525,1527,1558]
def ridgeSupport896_007 : List Nat := [1559,1561,1563,1564,1565,1567,1569,1570,1571,1573,1575,1678,1679,1681,1683,1684,1685,1687,1689,1690,1691,1693,1695,1726,1727,1729,1731,1732,1733,1735,1737,1738]
def ridgeSupport896_008 : List Nat := [1739,1741,1743,1846,1847,1849,1851,1852,1853,1855,1857,1858,1859,1861,1863,1894,1895,1897,1899,1900,1901,1903,1905,1906,1907,1909,1911,2014,2015,2017,2019,2020]
def ridgeSupport896_009 : List Nat := [2021,2023,2025,2026,2027,2029,2031,2062,2063,2065,2067,2068,2069,2071,2073,2074,2075,2077,2079,2182,2183,2185,2187,2188,2189,2191,2193,2194,2195,2197,2199]
cert_ridgeSupport_code_3 896
cert_ridgeSupport_rest_2 896 000 0
cert_ridgeSupport_rest_2 896 001 384
cert_ridgeSupport_rest_2 896 002 768
cert_ridgeSupport_rest_2 896 003 1152
cert_ridgeSupport_rest_2 896 004 1536
cert_ridgeSupport_rest_2 896 005 1920
cert_ridgeSupport_rest_2 896 006 2304
cert_ridgeSupport_rest_2 896 007 2688
cert_ridgeSupport_rest_2 896 008 3072
cert_ridgeSupport_rest_2 896 009 3456
cert_ridgeSupport_rest_2 896 010 3828
cert_ridgeSupport_suffix_4 896 010
cert_ridgeSupport_suffix_3 896 009 010
cert_ridgeSupport_suffix_3 896 008 009
cert_ridgeSupport_suffix_3 896 007 008
cert_ridgeSupport_suffix_3 896 006 007
cert_ridgeSupport_suffix_3 896 005 006
cert_ridgeSupport_suffix_3 896 004 005
cert_ridgeSupport_suffix_3 896 003 004
cert_ridgeSupport_suffix_3 896 002 003
cert_ridgeSupport_suffix_3 896 001 002
cert_ridgeSupport_suffix_3 896 000 001
cert_ridgeSupport_source_3 896 12 319
end Papers.RationalityTen.RootedCaches.RootedSixExtra06
