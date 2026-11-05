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
def ridgeSupport832_code : Nat := 0x89689589489389088f88e88d88588388188081e81d81c81b81881781681580d80b8098087ee7ed7ec7eb7e87e77e67e57dd7db7d97d877677577477377076f76e76d76576376176074674574474374073f73e73d7357337317306ce6cd6cc6cb6c86c76c66c56bd6bb6b96b869e69d69c69b69869769669568d68b68968862662562462362061f61e61d6156136116105f65f55f45f35f05ef5ee5ed5e55e35e15e05c65c55c45c35c05bf5be5bd5b55b35b15b05af5ae5ac5ab5a55a459f59e59b59a59959759659559359258c58b58658558258158057e56856756656556456355955855755655555452952852652551f51e5195185155145135114fb4fa4f94f84f74f64ec4eb4ea4e94e84e74bc4bb4b94b84b24b14ac4ab4a84a74a64a448e48d48c48b48a48947f47e47d47c47b47a43a43943843743643542b42a42942842742639e39d39c39b39a39938f38e38d38c38b38a31731631431330d30c3073063033023012ff2e92e82e72e62e52e42da2d92d82d72d62d529529429329229129028628528428328228120e20d20b20a2042031fe1fd1fa1f91f81f61e01df1de1dd1dc1db1d11d01cf1ce1cd1cc18c18b18a18918818717d17c17b17a1791780f00ef0ee0ed0ec0eb0e10e00df0de0dd0dc06906706305904f03101d
def ridgeSupport832_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport832_code
def ridgeSupport832_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport832_code
def ridgeSupport832_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport832_code
def ridgeSupport832_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport832_code
def ridgeSupport832_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport832_code
def ridgeSupport832_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport832_code
def ridgeSupport832_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport832_code
def ridgeSupport832_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport832_code
def ridgeSupport832_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport832_code
def ridgeSupport832_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport832_code
def ridgeSupport832_rest_010 : Nat := PackedRawNatGrowth.drop 3828 ridgeSupport832_code
def ridgeSupport832_suffix_010 : List Nat := []
def ridgeSupport832_suffix_009 : List Nat := ridgeSupport832_009 ++ ridgeSupport832_suffix_010
def ridgeSupport832_suffix_008 : List Nat := ridgeSupport832_008 ++ ridgeSupport832_suffix_009
def ridgeSupport832_suffix_007 : List Nat := ridgeSupport832_007 ++ ridgeSupport832_suffix_008
def ridgeSupport832_suffix_006 : List Nat := ridgeSupport832_006 ++ ridgeSupport832_suffix_007
def ridgeSupport832_suffix_005 : List Nat := ridgeSupport832_005 ++ ridgeSupport832_suffix_006
def ridgeSupport832_suffix_004 : List Nat := ridgeSupport832_004 ++ ridgeSupport832_suffix_005
def ridgeSupport832_suffix_003 : List Nat := ridgeSupport832_003 ++ ridgeSupport832_suffix_004
def ridgeSupport832_suffix_002 : List Nat := ridgeSupport832_002 ++ ridgeSupport832_suffix_003
def ridgeSupport832_suffix_001 : List Nat := ridgeSupport832_001 ++ ridgeSupport832_suffix_002
def ridgeSupport832_suffix_000 : List Nat := ridgeSupport832_000 ++ ridgeSupport832_suffix_001
theorem ridgeSupport832_source : candidateSupports 832 =
    (PackedRawNatGrowth.readList 12 319 ridgeSupport832_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
