module
prelude
public import RootedSixExtra01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport448_000 : List Nat := [31,57,87,97,107,111,115,260,261,262,263,264,265,275,276,277,278,279,280,416,417,418,419,420,421,431,432,433,434,435,436,500]
def ridgeSupport448_001 : List Nat := [501,502,503,504,505,515,516,517,518,519,520,584,585,586,590,592,593,597,599,600,602,603,605,681,682,683,684,685,686,696,697,698]
def ridgeSupport448_002 : List Nat := [699,700,701,769,770,771,772,773,774,784,785,786,787,788,789,853,854,855,856,857,858,868,869,870,871,872,873,937,938,939,943,945]
def ridgeSupport448_003 : List Nat := [946,950,952,953,955,956,958,1034,1035,1036,1037,1038,1039,1049,1050,1051,1052,1053,1054,1190,1191,1192,1193,1194,1195,1205,1206,1207,1208,1209,1210,1274]
def ridgeSupport448_004 : List Nat := [1275,1276,1277,1278,1279,1289,1290,1291,1292,1293,1294,1358,1359,1360,1364,1366,1367,1371,1373,1374,1376,1377,1379,1383,1384,1385,1386,1387,1388,1398,1399,1400]
def ridgeSupport448_005 : List Nat := [1401,1402,1403,1467,1468,1469,1473,1475,1476,1480,1482,1483,1485,1486,1488,1492,1493,1494,1495,1496,1497,1507,1508,1509,1510,1511,1512,1576,1577,1578,1582,1584]
def ridgeSupport448_006 : List Nat := [1585,1589,1591,1592,1594,1595,1597,1601,1602,1603,1607,1609,1610,1614,1616,1617,1619,1620,1622,1644,1645,1646,1647,1648,1649,1680,1681,1682,1683,1684,1685,1716]
def ridgeSupport448_007 : List Nat := [1717,1718,1719,1720,1721,1734,1735,1736,1737,1738,1739,1776,1777,1778,1779,1780,1781,1812,1813,1814,1815,1816,1817,1830,1831,1832,1833,1834,1835,1872,1873,1874]
def ridgeSupport448_008 : List Nat := [1875,1876,1877,1890,1891,1892,1893,1894,1895,1932,1933,1934,1935,1936,1937,1968,1969,1970,1971,1972,1973,1986,1987,1988,1989,1990,1991,2028,2029,2030,2031,2032]
def ridgeSupport448_009 : List Nat := [2033,2064,2065,2066,2067,2068,2069,2082,2083,2084,2085,2086,2087,2124,2125,2126,2127,2128,2129,2142,2143,2144,2145,2146,2147,2190,2192,2194,2195,2196,2198,2200]
def ridgeSupport448_010 : List Nat := [2201,2202,2204,2206,2207,2238,2240,2242,2243,2244,2246,2248,2249,2250,2252,2254,2255,2286,2288,2290,2291,2292,2294,2296,2297,2298,2300,2302,2303,2406,2408,2410]
def ridgeSupport448_011 : List Nat := [2411,2412,2414,2416,2417,2418,2420,2422,2423,2454,2456,2458,2459,2460,2462,2464,2465,2466,2468,2470,2471,2574,2576,2578,2579,2580,2582,2584,2585,2586,2588,2590]
def ridgeSupport448_012 : List Nat := [2591,2694,2696,2698,2699,2700,2702,2704,2705,2706,2708,2710,2711,2742,2744,2746,2747,2748,2750,2752,2753,2754,2756,2758,2759,2862,2864,2866,2867,2868,2870,2872]
def ridgeSupport448_013 : List Nat := [2873,2874,2876,2878,2879,2910,2912,2914,2915,2916,2918,2920,2921,2922,2924,2926,2927,3030,3032,3034,3035,3036,3038,3040,3041,3042,3044,3046,3047]
def ridgeSupport448_code : Nat := 0xbe7be6be4be2be1be0bdebdcbdbbdabd8bd6b6fb6eb6cb6ab69b68b66b64b63b62b60b5eb3fb3eb3cb3ab39b38b36b34b33b32b30b2eac7ac6ac4ac2ac1ac0abeabcabbabaab8ab6a97a96a94a92a91a90a8ea8ca8ba8aa88a86a1fa1ea1ca1aa19a18a16a14a13a12a10a0e9a79a69a49a29a19a099e99c99b99a99899697797697497297197096e96c96b96a9689668ff8fe8fc8fa8f98f88f68f48f38f28f08ee8cf8ce8cc8ca8c98c88c68c48c38c28c08be89f89e89c89a89989889689489389289088e86386286186085f85e85185084f84e84d84c8278268258248238228158148138128118107f17f07ef7ee7ed7ec7c77c67c57c47c37c27b57b47b37b27b17b079179078f78e78d78c76776676576476376275575475375275175072b72a7297287277267197187177167157146f56f46f36f26f16f06cb6ca6c96c86c76c66b96b86b76b66b56b469569469369269169067167066f66e66d66c65665465365165064e64a64964764364264163d63b63a63863763563163062e62a6296285e85e75e65e55e45e35d95d85d75d65d55d45d05ce5cd5cb5ca5c85c45c35c15bd5bc5bb57b57a57957857757656c56b56a56956856756356156055e55d55b55755655455054f54e50e50d50c50b50a5094ff4fe4fd4fc4fb4fa4ba4b94b84b74b64b54ab4aa4a94a84a74a641e41d41c41b41a41940f40e40d40c40b40a3be3bc3bb3b93b83b63b23b13af3ab3aa3a936936836736636536435a3593583573563553153143133123113103063053043033023012bd2bc2bb2ba2b92b82ae2ad2ac2ab2aa2a925d25b25a25825725525125024e24a2492482082072062052042031f91f81f71f61f51f41b41b31b21b11b01af1a51a41a31a21a11a011811711611511411310910810710610510407306f06b06105703901f
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
def ridgeSupport448_rest_012 : Nat := PackedRawNatGrowth.drop 4608 ridgeSupport448_code
def ridgeSupport448_rest_013 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport448_code
def ridgeSupport448_rest_014 : Nat := PackedRawNatGrowth.drop 5340 ridgeSupport448_code
def ridgeSupport448_suffix_014 : List Nat := []
def ridgeSupport448_suffix_013 : List Nat := ridgeSupport448_013 ++ ridgeSupport448_suffix_014
def ridgeSupport448_suffix_012 : List Nat := ridgeSupport448_012 ++ ridgeSupport448_suffix_013
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
    (PackedRawNatGrowth.readList 12 445 ridgeSupport448_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
