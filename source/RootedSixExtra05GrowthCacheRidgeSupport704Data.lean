module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra05GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport704_000 : List Nat := [24,40,50,70,80,84,87,185,186,187,188,189,190,200,201,202,203,204,205,273,274,275,276,277,278,288,289,290,291,292,293,357]
def ridgeSupport704_001 : List Nat := [358,359,360,361,362,372,373,374,375,376,377,420,421,423,425,427,429,434,435,437,438,442,444,470,471,472,473,474,475,485,486,487]
def ridgeSupport704_002 : List Nat := [488,489,490,554,555,556,557,558,559,569,570,571,572,573,574,617,618,620,622,624,626,631,632,634,635,639,641,663,664,665,666,667]
def ridgeSupport704_003 : List Nat := [668,678,679,680,681,682,683,726,727,729,731,733,735,740,741,743,744,748,750,844,845,846,847,848,849,859,860,861,862,863,864,928]
def ridgeSupport704_004 : List Nat := [929,930,931,932,933,943,944,945,946,947,948,991,992,994,996,998,1000,1005,1006,1008,1009,1013,1015,1037,1038,1039,1040,1041,1042,1052,1053,1054]
def ridgeSupport704_005 : List Nat := [1055,1056,1057,1100,1101,1103,1105,1107,1109,1114,1115,1117,1118,1122,1124,1125,1126,1128,1130,1132,1134,1139,1140,1142,1143,1147,1149,1162,1163,1164,1165,1166]
def ridgeSupport704_006 : List Nat := [1167,1198,1199,1200,1201,1202,1203,1234,1235,1236,1237,1238,1239,1264,1265,1266,1267,1268,1269,1294,1295,1296,1297,1298,1299,1330,1331,1332,1333,1334,1335,1366]
def ridgeSupport704_007 : List Nat := [1367,1368,1369,1370,1371,1426,1427,1428,1429,1430,1431,1462,1463,1464,1465,1466,1467,1522,1523,1524,1525,1526,1527,1576,1577,1578,1579,1580,1581,1595,1596,1597]
def ridgeSupport704_008 : List Nat := [1598,1601,1602,1603,1604,1612,1614,1616,1617,1643,1644,1645,1646,1649,1650,1651,1652,1660,1662,1664,1665,1691,1692,1693,1694,1697,1698,1699,1700,1708,1710,1712]
def ridgeSupport704_009 : List Nat := [1713,1811,1812,1813,1814,1817,1818,1819,1820,1828,1830,1832,1833,1859,1860,1861,1862,1865,1866,1867,1868,1876,1878,1880,1881,1907,1908,1909,1910,1913,1914,1915]
def ridgeSupport704_010 : List Nat := [1916,1924,1926,1928,1929,1955,1956,1957,1958,1961,1962,1963,1964,1972,1974,1976,1977,2003,2004,2005,2006,2009,2010,2011,2012,2020,2022,2024,2025,2051,2052,2053]
def ridgeSupport704_011 : List Nat := [2054,2057,2058,2059,2060,2068,2070,2072,2073]
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
cert_ridgeSupport_rest_2 704 010 3840
cert_ridgeSupport_rest_2 704 011 4224
cert_ridgeSupport_rest_2 704 012 4332
cert_ridgeSupport_suffix_4 704 012
cert_ridgeSupport_suffix_3 704 011 012
cert_ridgeSupport_suffix_3 704 010 011
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
cert_ridgeSupport_source_3 704 12 361
end Papers.RationalityTen.RootedCaches.RootedSixExtra05
