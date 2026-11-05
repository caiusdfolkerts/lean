module
prelude
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
def ridgeSupport448_code : Nat := 0x81381281080e80d80c80a8088078068048027e37e27e07de7dd7dc7da7d87d77d67d47d27b37b27b07ae7ad7ac7aa7a87a77a67a47a278378278077e77d77c77a77877777677477275375275074e74d74c74a74874774674474272372272071e71d71c71a7187177167147126ab6aa6a86a66a56a46a26a069f69e69c69a67b67a67867667567467267066f66e66c66a64b64a64864664564464264063f63e63c63a6276266256246236225fd5fc5fb5fa5f95f85c15c05bf5be5bd5bc59d59c59b59a59959856156055f55e55d55c53d53c53b53a5395385195185175165155144ef4ee4ed4ec4eb4ea4dd4dc4db4da4d94d84b94b84b74b64b54b449549449349249149047a47847747547447246e46d46b46746646546145f45e45c45b45945545445244e44d44c40c40b40a4094084073fd3fc3fb3fa3f93f83f43f23f13ef3ee3ec3e83e73e53e13e03df39f39e39d39c39b39a39038f38e38d38c38b34b34a34934834734633c33b33a3393383372eb2e92e82e62e52e32df2de2dc2d82d72d629629529429329229128728628528428328227e27c27b27927827627227126f26b26a26922922822722622522421a2192182172162151d51d41d31d21d11d01c61c51c41c31c21c11b91b71b61b41b31b11ad1ac1aa1a61a51a416416316216116015f15515415315215115011010f10e10d10c10b1011000ff0fe0fd0fc0b80b70b60b50b40b30a90a80a70a60a50a405705304f045031027017
def ridgeSupport448_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport448_code
def ridgeSupport448_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport448_code
def ridgeSupport448_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport448_code
def ridgeSupport448_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport448_code
def ridgeSupport448_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport448_code
def ridgeSupport448_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport448_code
def ridgeSupport448_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport448_code
def ridgeSupport448_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport448_code
def ridgeSupport448_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport448_code
def ridgeSupport448_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport448_code
def ridgeSupport448_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport448_code
def ridgeSupport448_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport448_code
def ridgeSupport448_rest_012 : Nat := PackedRawNatGrowth.drop 4332 ridgeSupport448_code
def ridgeSupport448_suffix_012 : List Nat := []
def ridgeSupport448_suffix_011 : List Nat := ridgeSupport448_011 ++ ridgeSupport448_suffix_012
def ridgeSupport448_suffix_010 : List Nat := ridgeSupport448_010 ++ ridgeSupport448_suffix_011
def ridgeSupport448_suffix_009 : List Nat := ridgeSupport448_009 ++ ridgeSupport448_suffix_010
def ridgeSupport448_suffix_008 : List Nat := ridgeSupport448_008 ++ ridgeSupport448_suffix_009
def ridgeSupport448_suffix_007 : List Nat := ridgeSupport448_007 ++ ridgeSupport448_suffix_008
def ridgeSupport448_suffix_006 : List Nat := ridgeSupport448_006 ++ ridgeSupport448_suffix_007
def ridgeSupport448_suffix_005 : List Nat := ridgeSupport448_005 ++ ridgeSupport448_suffix_006
def ridgeSupport448_suffix_004 : List Nat := ridgeSupport448_004 ++ ridgeSupport448_suffix_005
def ridgeSupport448_suffix_003 : List Nat := ridgeSupport448_003 ++ ridgeSupport448_suffix_004
def ridgeSupport448_suffix_002 : List Nat := ridgeSupport448_002 ++ ridgeSupport448_suffix_003
def ridgeSupport448_suffix_001 : List Nat := ridgeSupport448_001 ++ ridgeSupport448_suffix_002
def ridgeSupport448_suffix_000 : List Nat := ridgeSupport448_000 ++ ridgeSupport448_suffix_001
theorem ridgeSupport448_source : candidateSupports 448 =
    (PackedRawNatGrowth.readList 12 361 ridgeSupport448_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
