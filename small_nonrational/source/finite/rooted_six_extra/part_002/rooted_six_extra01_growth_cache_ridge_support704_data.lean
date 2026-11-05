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
def ridgeSupport704_000 : List Nat := [32,58,88,98,108,112,115,281,282,283,284,285,286,296,297,298,299,300,301,437,438,439,440,441,442,452,453,454,455,456,457,521]
def ridgeSupport704_001 : List Nat := [522,523,524,525,526,536,537,538,539,540,541,584,585,587,589,591,593,598,599,601,602,606,608,702,703,704,705,706,707,717,718,719]
def ridgeSupport704_002 : List Nat := [720,721,722,790,791,792,793,794,795,805,806,807,808,809,810,874,875,876,877,878,879,889,890,891,892,893,894,937,938,940,942,944]
def ridgeSupport704_003 : List Nat := [946,951,952,954,955,959,961,1055,1056,1057,1058,1059,1060,1070,1071,1072,1073,1074,1075,1211,1212,1213,1214,1215,1216,1226,1227,1228,1229,1230,1231,1295]
def ridgeSupport704_004 : List Nat := [1296,1297,1298,1299,1300,1310,1311,1312,1313,1314,1315,1358,1359,1361,1363,1365,1367,1372,1373,1375,1376,1380,1382,1404,1405,1406,1407,1408,1409,1419,1420,1421]
def ridgeSupport704_005 : List Nat := [1422,1423,1424,1467,1468,1470,1472,1474,1476,1481,1482,1484,1485,1489,1491,1513,1514,1515,1516,1517,1518,1528,1529,1530,1531,1532,1533,1576,1577,1579,1581,1583]
def ridgeSupport704_006 : List Nat := [1585,1590,1591,1593,1594,1598,1600,1601,1602,1604,1606,1608,1610,1615,1616,1618,1619,1623,1625,1638,1639,1640,1641,1642,1643,1674,1675,1676,1677,1678,1679,1710]
def ridgeSupport704_007 : List Nat := [1711,1712,1713,1714,1715,1740,1741,1742,1743,1744,1745,1770,1771,1772,1773,1774,1775,1806,1807,1808,1809,1810,1811,1836,1837,1838,1839,1840,1841,1866,1867,1868]
def ridgeSupport704_008 : List Nat := [1869,1870,1871,1896,1897,1898,1899,1900,1901,1926,1927,1928,1929,1930,1931,1962,1963,1964,1965,1966,1967,1992,1993,1994,1995,1996,1997,2022,2023,2024,2025,2026]
def ridgeSupport704_009 : List Nat := [2027,2058,2059,2060,2061,2062,2063,2088,2089,2090,2091,2092,2093,2118,2119,2120,2121,2122,2123,2148,2149,2150,2151,2152,2153,2191,2192,2193,2194,2197,2198,2199]
def ridgeSupport704_010 : List Nat := [2200,2208,2210,2212,2213,2239,2240,2241,2242,2245,2246,2247,2248,2256,2258,2260,2261,2287,2288,2289,2290,2293,2294,2295,2296,2304,2306,2308,2309,2407,2408,2409]
def ridgeSupport704_011 : List Nat := [2410,2413,2414,2415,2416,2424,2426,2428,2429,2455,2456,2457,2458,2461,2462,2463,2464,2472,2474,2476,2477,2575,2576,2577,2578,2581,2582,2583,2584,2592,2594,2596]
def ridgeSupport704_012 : List Nat := [2597,2695,2696,2697,2698,2701,2702,2703,2704,2712,2714,2716,2717,2743,2744,2745,2746,2749,2750,2751,2752,2760,2762,2764,2765,2863,2864,2865,2866,2869,2870,2871]
def ridgeSupport704_013 : List Nat := [2872,2880,2882,2884,2885,2911,2912,2913,2914,2917,2918,2919,2920,2928,2930,2932,2933,3031,3032,3033,3034,3037,3038,3039,3040,3048,3050,3052,3053]
def ridgeSupport704_code : Nat := 0xbedbecbeabe8be0bdfbdebddbdabd9bd8bd7b75b74b72b70b68b67b66b65b62b61b60b5fb45b44b42b40b38b37b36b35b32b31b30b2facdaccacaac8ac0abfabeabdabaab9ab8ab7a9da9ca9aa98a90a8fa8ea8da8aa89a88a87a25a24a22a20a18a17a16a15a12a11a10a0f9ad9ac9aa9a89a099f99e99d99a99999899797d97c97a97897096f96e96d96a9699689679059049029008f88f78f68f58f28f18f08ef8d58d48d28d08c88c78c68c58c28c18c08bf8a58a48a28a089889789689589289189088f86986886786686586484b84a84984884784682d82c82b82a82982880f80e80d80c80b80a7eb7ea7e97e87e77e67cd7cc7cb7ca7c97c87af7ae7ad7ac7ab7aa78b78a78978878778676d76c76b76a76976874f74e74d74c74b74a73173072f72e72d72c71371271171070f70e6ef6ee6ed6ec6eb6ea6d16d06cf6ce6cd6cc6b36b26b16b06af6ae68f68e68d68c68b68a66b66a66966866766665965765365265064f64a64864664464264164063e63a63963763663162f62d62b6296285fd5fc5fb5fa5f95f85ee5ed5ec5eb5ea5e95d35d15cd5cc5ca5c95c45c25c05be5bc5bb59058f58e58d58c58b58158057f57e57d57c56656456055f55d55c55755555355154f54e52352252152051f51e51451351251151050f4cf4ce4cd4cc4cb4ca4c04bf4be4bd4bc4bb43343243143042f42e42442342242142041f3c13bf3bb3ba3b83b73b23b03ae3ac3aa3a937e37d37c37b37a37936f36e36d36c36b36a32a32932832732632531b31a3193183173162d22d12d02cf2ce2cd2c32c22c12c02bf2be26025e25a25925725625124f24d24b24924821d21c21b21a21921820e20d20c20b20a2091c91c81c71c61c51c41ba1b91b81b71b61b512d12c12b12a12912811e11d11c11b11a11907307006c06205803a020
def ridgeSupport704_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport704_code
def ridgeSupport704_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport704_code
def ridgeSupport704_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport704_code
def ridgeSupport704_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport704_code
def ridgeSupport704_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport704_code
def ridgeSupport704_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport704_code
def ridgeSupport704_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport704_code
def ridgeSupport704_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport704_code
def ridgeSupport704_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport704_code
def ridgeSupport704_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport704_code
def ridgeSupport704_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport704_code
def ridgeSupport704_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport704_code
def ridgeSupport704_rest_012 : Nat := PackedRawNatGrowth.drop 4608 ridgeSupport704_code
def ridgeSupport704_rest_013 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport704_code
def ridgeSupport704_rest_014 : Nat := PackedRawNatGrowth.drop 5340 ridgeSupport704_code
def ridgeSupport704_suffix_014 : List Nat := []
def ridgeSupport704_suffix_013 : List Nat := ridgeSupport704_013 ++ ridgeSupport704_suffix_014
def ridgeSupport704_suffix_012 : List Nat := ridgeSupport704_012 ++ ridgeSupport704_suffix_013
def ridgeSupport704_suffix_011 : List Nat := ridgeSupport704_011 ++ ridgeSupport704_suffix_012
def ridgeSupport704_suffix_010 : List Nat := ridgeSupport704_010 ++ ridgeSupport704_suffix_011
def ridgeSupport704_suffix_009 : List Nat := ridgeSupport704_009 ++ ridgeSupport704_suffix_010
def ridgeSupport704_suffix_008 : List Nat := ridgeSupport704_008 ++ ridgeSupport704_suffix_009
def ridgeSupport704_suffix_007 : List Nat := ridgeSupport704_007 ++ ridgeSupport704_suffix_008
def ridgeSupport704_suffix_006 : List Nat := ridgeSupport704_006 ++ ridgeSupport704_suffix_007
def ridgeSupport704_suffix_005 : List Nat := ridgeSupport704_005 ++ ridgeSupport704_suffix_006
def ridgeSupport704_suffix_004 : List Nat := ridgeSupport704_004 ++ ridgeSupport704_suffix_005
def ridgeSupport704_suffix_003 : List Nat := ridgeSupport704_003 ++ ridgeSupport704_suffix_004
def ridgeSupport704_suffix_002 : List Nat := ridgeSupport704_002 ++ ridgeSupport704_suffix_003
def ridgeSupport704_suffix_001 : List Nat := ridgeSupport704_001 ++ ridgeSupport704_suffix_002
def ridgeSupport704_suffix_000 : List Nat := ridgeSupport704_000 ++ ridgeSupport704_suffix_001
theorem ridgeSupport704_source : candidateSupports 704 =
    (PackedRawNatGrowth.readList 12 445 ridgeSupport704_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
