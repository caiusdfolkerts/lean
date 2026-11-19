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
def ridgeSupport448_000 : List Nat := [23,39,49,69,79,83,87,164,165,166,167,168,169,179,180,181,182,183,184,252,253,254,255,256,257,267,268,269,270,271,272,336]
def ridgeSupport448_001 : List Nat := [337,338,339,340,341,351,352,353,354,355,356,420,421,422,426,428,429,433,435,436,438,439,441,449,450,451,452,453,454,464,465,466]
def ridgeSupport448_002 : List Nat := [467,468,469,533,534,535,536,537,538,548,549,550,551,552,553,617,618,619,623,625,626,630,632,633,635,636,638,642,643,644,645,646]
def ridgeSupport448_003 : List Nat := [647,657,658,659,660,661,662,726,727,728,732,734,735,739,741,742,744,745,747,823,824,825,826,827,828,838,839,840,841,842,843,907]
def ridgeSupport448_004 : List Nat := [908,909,910,911,912,922,923,924,925,926,927,991,992,993,997,999,1000,1004,1006,1007,1009,1010,1012,1016,1017,1018,1019,1020,1021,1031,1032,1033]
def ridgeSupport448_005 : List Nat := [1034,1035,1036,1100,1101,1102,1106,1108,1109,1113,1115,1116,1118,1119,1121,1125,1126,1127,1131,1133,1134,1138,1140,1141,1143,1144,1146,1168,1169,1170,1171,1172]
def ridgeSupport448_006 : List Nat := [1173,1204,1205,1206,1207,1208,1209,1240,1241,1242,1243,1244,1245,1258,1259,1260,1261,1262,1263,1300,1301,1302,1303,1304,1305,1336,1337,1338,1339,1340,1341,1372]
def ridgeSupport448_007 : List Nat := [1373,1374,1375,1376,1377,1432,1433,1434,1435,1436,1437,1468,1469,1470,1471,1472,1473,1528,1529,1530,1531,1532,1533,1570,1571,1572,1573,1574,1575,1594,1596,1598]
def ridgeSupport448_008 : List Nat := [1599,1600,1602,1604,1605,1606,1608,1610,1611,1642,1644,1646,1647,1648,1650,1652,1653,1654,1656,1658,1659,1690,1692,1694,1695,1696,1698,1700,1701,1702,1704,1706]
def ridgeSupport448_009 : List Nat := [1707,1810,1812,1814,1815,1816,1818,1820,1821,1822,1824,1826,1827,1858,1860,1862,1863,1864,1866,1868,1869,1870,1872,1874,1875,1906,1908,1910,1911,1912,1914,1916]
def ridgeSupport448_010 : List Nat := [1917,1918,1920,1922,1923,1954,1956,1958,1959,1960,1962,1964,1965,1966,1968,1970,1971,2002,2004,2006,2007,2008,2010,2012,2013,2014,2016,2018,2019,2050,2052,2054]
def ridgeSupport448_011 : List Nat := [2055,2056,2058,2060,2061,2062,2064,2066,2067]
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
cert_ridgeSupport_rest_2 448 010 3840
cert_ridgeSupport_rest_2 448 011 4224
cert_ridgeSupport_rest_2 448 012 4332
cert_ridgeSupport_suffix_4 448 012
cert_ridgeSupport_suffix_3 448 011 012
cert_ridgeSupport_suffix_3 448 010 011
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
cert_ridgeSupport_source_3 448 12 361
end Papers.RationalityTen.RootedCaches.RootedSixExtra05
