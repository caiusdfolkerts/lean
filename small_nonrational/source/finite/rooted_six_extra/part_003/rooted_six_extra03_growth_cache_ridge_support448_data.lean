module
prelude
public import RootedSixExtra03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport448_000 : List Nat := [27,57,77,97,107,111,115,260,261,262,263,264,265,275,276,277,278,279,280,348,349,350,351,352,353,363,364,365,366,367,368,432]
def ridgeSupport448_001 : List Nat := [433,434,435,436,437,447,448,449,450,451,452,516,517,518,522,524,525,529,531,532,534,535,537,613,614,615,616,617,618,628,629,630]
def ridgeSupport448_002 : List Nat := [631,632,633,769,770,771,772,773,774,784,785,786,787,788,789,853,854,855,856,857,858,868,869,870,871,872,873,937,938,939,943,945]
def ridgeSupport448_003 : List Nat := [946,950,952,953,955,956,958,1034,1035,1036,1037,1038,1039,1049,1050,1051,1052,1053,1054,1118,1119,1120,1121,1122,1123,1133,1134,1135,1136,1137,1138,1202]
def ridgeSupport448_004 : List Nat := [1203,1204,1208,1210,1211,1215,1217,1218,1220,1221,1223,1299,1300,1301,1302,1303,1304,1314,1315,1316,1317,1318,1319,1383,1384,1385,1386,1387,1388,1398,1399,1400]
def ridgeSupport448_005 : List Nat := [1401,1402,1403,1467,1468,1469,1473,1475,1476,1480,1482,1483,1485,1486,1488,1492,1493,1494,1495,1496,1497,1507,1508,1509,1510,1511,1512,1576,1577,1578,1582,1584]
def ridgeSupport448_006 : List Nat := [1585,1589,1591,1592,1594,1595,1597,1601,1602,1603,1607,1609,1610,1614,1616,1617,1619,1620,1622,1644,1645,1646,1647,1648,1649,1680,1681,1682,1683,1684,1685,1716]
def ridgeSupport448_007 : List Nat := [1717,1718,1719,1720,1721,1734,1735,1736,1737,1738,1739,1776,1777,1778,1779,1780,1781,1812,1813,1814,1815,1816,1817,1830,1831,1832,1833,1834,1835,1872,1873,1874]
def ridgeSupport448_008 : List Nat := [1875,1876,1877,1908,1909,1910,1911,1912,1913,1968,1969,1970,1971,1972,1973,2004,2005,2006,2007,2008,2009,2022,2023,2024,2025,2026,2027,2064,2065,2066,2067,2068]
def ridgeSupport448_009 : List Nat := [2069,2082,2083,2084,2085,2086,2087,2124,2125,2126,2127,2128,2129,2142,2143,2144,2145,2146,2147,2166,2167,2168,2169,2170,2171,2190,2192,2194,2195,2196,2198,2200]
def ridgeSupport448_010 : List Nat := [2201,2202,2204,2206,2207,2238,2240,2242,2243,2244,2246,2248,2249,2250,2252,2254,2255,2286,2288,2290,2291,2292,2294,2296,2297,2298,2300,2302,2303,2406,2408,2410]
def ridgeSupport448_011 : List Nat := [2411,2412,2414,2416,2417,2418,2420,2422,2423,2454,2456,2458,2459,2460,2462,2464,2465,2466,2468,2470,2471,2574,2576,2578,2579,2580,2582,2584,2585,2586,2588,2590]
def ridgeSupport448_012 : List Nat := [2591,2622,2624,2626,2627,2628,2630,2632,2633,2634,2636,2638,2639,2670,2672,2674,2675,2676,2678,2680,2681,2682,2684,2686,2687,2718,2720,2722,2723,2724,2726,2728]
def ridgeSupport448_013 : List Nat := [2729,2730,2732,2734,2735,2838,2840,2842,2843,2844,2846,2848,2849,2850,2852,2854,2855,2958,2960,2962,2963,2964,2966,2968,2969,2970,2972,2974,2975]
def ridgeSupport448_code : Nat := 0xb9fb9eb9cb9ab99b98b96b94b93b92b90b8eb27b26b24b22b21b20b1eb1cb1bb1ab18b16aafaaeaacaaaaa9aa8aa6aa4aa3aa2aa0a9ea7fa7ea7ca7aa79a78a76a74a73a72a70a6ea4fa4ea4ca4aa49a48a46a44a43a42a40a3ea1fa1ea1ca1aa19a18a16a14a13a12a10a0e9a79a69a49a29a19a099e99c99b99a99899697797697497297197096e96c96b96a9689668ff8fe8fc8fa8f98f88f68f48f38f28f08ee8cf8ce8cc8ca8c98c88c68c48c38c28c08be89f89e89c89a89989889689489389289088e87b87a87987887787686386286186085f85e85185084f84e84d84c8278268258248238228158148138128118107eb7ea7e97e87e77e67d97d87d77d67d57d47b57b47b37b27b17b077977877777677577475575475375275175072b72a7297287277267197187177167157146f56f46f36f26f16f06cb6ca6c96c86c76c66b96b86b76b66b56b469569469369269169067167066f66e66d66c65665465365165064e64a64964764364264163d63b63a63863763563163062e62a6296285e85e75e65e55e45e35d95d85d75d65d55d45d05ce5cd5cb5ca5c85c45c35c15bd5bc5bb57b57a57957857757656c56b56a5695685675275265255245235225185175165155145134c74c54c44c24c14bf4bb4ba4b84b44b34b247247147046f46e46d46346246146045f45e41e41d41c41b41a41940f40e40d40c40b40a3be3bc3bb3b93b83b63b23b13af3ab3aa3a936936836736636536435a35935835735635531531431331231131030630530430330230127927827727627527426a26926826726626521921721621421321120d20c20a2062052041c41c31c21c11c01bf1b51b41b31b21b11b017016f16e16d16c16b16116015f15e15d15c11811711611511411310910810710610510407306f06b06104d03901b
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
