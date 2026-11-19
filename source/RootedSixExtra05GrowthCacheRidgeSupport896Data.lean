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
def ridgeSupport896_000 : List Nat := [26,42,52,72,82,86,87,227,228,229,230,231,232,242,243,244,245,246,247,315,316,317,318,319,320,330,331,332,333,334,335,399]
def ridgeSupport896_001 : List Nat := [400,401,402,403,404,414,415,416,417,418,419,421,422,423,424,425,426,436,437,439,440,442,443,512,513,514,515,516,517,527,528,529]
def ridgeSupport896_002 : List Nat := [530,531,532,596,597,598,599,600,601,611,612,613,614,615,616,618,619,620,621,622,623,633,634,636,637,639,640,705,706,707,708,709]
def ridgeSupport896_003 : List Nat := [710,720,721,722,723,724,725,727,728,729,730,731,732,742,743,745,746,748,749,886,887,888,889,890,891,901,902,903,904,905,906,970]
def ridgeSupport896_004 : List Nat := [971,972,973,974,975,985,986,987,988,989,990,992,993,994,995,996,997,1007,1008,1010,1011,1013,1014,1079,1080,1081,1082,1083,1084,1094,1095,1096]
def ridgeSupport896_005 : List Nat := [1097,1098,1099,1101,1102,1103,1104,1105,1106,1116,1117,1119,1120,1122,1123,1126,1127,1128,1129,1130,1131,1141,1142,1144,1145,1147,1148,1150,1151,1152,1153,1154]
def ridgeSupport896_006 : List Nat := [1155,1186,1187,1188,1189,1190,1191,1222,1223,1224,1225,1226,1227,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1318,1319,1320,1321,1322,1323,1354]
def ridgeSupport896_007 : List Nat := [1355,1356,1357,1358,1359,1414,1415,1416,1417,1418,1419,1450,1451,1452,1453,1454,1455,1510,1511,1512,1513,1514,1515,1588,1589,1590,1591,1592,1593,1600,1601,1603]
def ridgeSupport896_008 : List Nat := [1605,1606,1607,1609,1611,1612,1613,1615,1617,1648,1649,1651,1653,1654,1655,1657,1659,1660,1661,1663,1665,1696,1697,1699,1701,1702,1703,1705,1707,1708,1709,1711]
def ridgeSupport896_009 : List Nat := [1713,1816,1817,1819,1821,1822,1823,1825,1827,1828,1829,1831,1833,1864,1865,1867,1869,1870,1871,1873,1875,1876,1877,1879,1881,1912,1913,1915,1917,1918,1919,1921]
def ridgeSupport896_010 : List Nat := [1923,1924,1925,1927,1929,1960,1961,1963,1965,1966,1967,1969,1971,1972,1973,1975,1977,2008,2009,2011,2013,2014,2015,2017,2019,2020,2021,2023,2025,2056,2057,2059]
def ridgeSupport896_011 : List Nat := [2061,2062,2063,2065,2067,2068,2069,2071,2073]
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
cert_ridgeSupport_rest_2 896 010 3840
cert_ridgeSupport_rest_2 896 011 4224
cert_ridgeSupport_rest_2 896 012 4332
cert_ridgeSupport_suffix_4 896 012
cert_ridgeSupport_suffix_3 896 011 012
cert_ridgeSupport_suffix_3 896 010 011
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
cert_ridgeSupport_source_3 896 12 361
end Papers.RationalityTen.RootedCaches.RootedSixExtra05
