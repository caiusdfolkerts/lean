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
def ridgeSupport704_000 : List Nat := [28,58,78,98,108,112,115,281,282,283,284,285,286,296,297,298,299,300,301,369,370,371,372,373,374,384,385,386,387,388,389,453]
def ridgeSupport704_001 : List Nat := [454,455,456,457,458,468,469,470,471,472,473,516,517,519,521,523,525,530,531,533,534,538,540,634,635,636,637,638,639,649,650,651]
def ridgeSupport704_002 : List Nat := [652,653,654,790,791,792,793,794,795,805,806,807,808,809,810,874,875,876,877,878,879,889,890,891,892,893,894,937,938,940,942,944]
def ridgeSupport704_003 : List Nat := [946,951,952,954,955,959,961,1055,1056,1057,1058,1059,1060,1070,1071,1072,1073,1074,1075,1139,1140,1141,1142,1143,1144,1154,1155,1156,1157,1158,1159,1202]
def ridgeSupport704_004 : List Nat := [1203,1205,1207,1209,1211,1216,1217,1219,1220,1224,1226,1320,1321,1322,1323,1324,1325,1335,1336,1337,1338,1339,1340,1404,1405,1406,1407,1408,1409,1419,1420,1421]
def ridgeSupport704_005 : List Nat := [1422,1423,1424,1467,1468,1470,1472,1474,1476,1481,1482,1484,1485,1489,1491,1513,1514,1515,1516,1517,1518,1528,1529,1530,1531,1532,1533,1576,1577,1579,1581,1583]
def ridgeSupport704_006 : List Nat := [1585,1590,1591,1593,1594,1598,1600,1601,1602,1604,1606,1608,1610,1615,1616,1618,1619,1623,1625,1638,1639,1640,1641,1642,1643,1674,1675,1676,1677,1678,1679,1710]
def ridgeSupport704_007 : List Nat := [1711,1712,1713,1714,1715,1740,1741,1742,1743,1744,1745,1770,1771,1772,1773,1774,1775,1806,1807,1808,1809,1810,1811,1836,1837,1838,1839,1840,1841,1866,1867,1868]
def ridgeSupport704_008 : List Nat := [1869,1870,1871,1902,1903,1904,1905,1906,1907,1962,1963,1964,1965,1966,1967,1998,1999,2000,2001,2002,2003,2028,2029,2030,2031,2032,2033,2058,2059,2060,2061,2062]
def ridgeSupport704_009 : List Nat := [2063,2088,2089,2090,2091,2092,2093,2118,2119,2120,2121,2122,2123,2148,2149,2150,2151,2152,2153,2172,2173,2174,2175,2176,2177,2191,2192,2193,2194,2197,2198,2199]
def ridgeSupport704_010 : List Nat := [2200,2208,2210,2212,2213,2239,2240,2241,2242,2245,2246,2247,2248,2256,2258,2260,2261,2287,2288,2289,2290,2293,2294,2295,2296,2304,2306,2308,2309,2407,2408,2409]
def ridgeSupport704_011 : List Nat := [2410,2413,2414,2415,2416,2424,2426,2428,2429,2455,2456,2457,2458,2461,2462,2463,2464,2472,2474,2476,2477,2575,2576,2577,2578,2581,2582,2583,2584,2592,2594,2596]
def ridgeSupport704_012 : List Nat := [2597,2623,2624,2625,2626,2629,2630,2631,2632,2640,2642,2644,2645,2671,2672,2673,2674,2677,2678,2679,2680,2688,2690,2692,2693,2719,2720,2721,2722,2725,2726,2727]
def ridgeSupport704_013 : List Nat := [2728,2736,2738,2740,2741,2839,2840,2841,2842,2845,2846,2847,2848,2856,2858,2860,2861,2959,2960,2961,2962,2965,2966,2967,2968,2976,2978,2980,2981]
def ridgeSupport704_code : Nat := 0xba5ba4ba2ba0b98b97b96b95b92b91b90b8fb2db2cb2ab28b20b1fb1eb1db1ab19b18b17ab5ab4ab2ab0aa8aa7aa6aa5aa2aa1aa0a9fa85a84a82a80a78a77a76a75a72a71a70a6fa55a54a52a50a48a47a46a45a42a41a40a3fa25a24a22a20a18a17a16a15a12a11a10a0f9ad9ac9aa9a89a099f99e99d99a99999899797d97c97a97897096f96e96d96a9699689679059049029008f88f78f68f58f28f18f08ef8d58d48d28d08c88c78c68c58c28c18c08bf8a58a48a28a089889789689589289189088f88188087f87e87d87c86986886786686586484b84a84984884784682d82c82b82a82982880f80e80d80c80b80a7f17f07ef7ee7ed7ec7d37d27d17d07cf7ce7af7ae7ad7ac7ab7aa77377277177076f76e74f74e74d74c74b74a73173072f72e72d72c71371271171070f70e6ef6ee6ed6ec6eb6ea6d16d06cf6ce6cd6cc6b36b26b16b06af6ae68f68e68d68c68b68a66b66a66966866766665965765365265064f64a64864664464264164063e63a63963763663162f62d62b6296285fd5fc5fb5fa5f95f85ee5ed5ec5eb5ea5e95d35d15cd5cc5ca5c95c45c25c05be5bc5bb59058f58e58d58c58b58158057f57e57d57c53c53b53a53953853752d52c52b52a5295284ca4c84c44c34c14c04bb4b94b74b54b34b248748648548448348247847747647547447343343243143042f42e42442342242142041f3c13bf3bb3ba3b83b73b23b03ae3ac3aa3a937e37d37c37b37a37936f36e36d36c36b36a32a32932832732632531b31a31931831731628e28d28c28b28a28927f27e27d27c27b27a21c21a21621521321220d20b2092072052041d91d81d71d61d51d41ca1c91c81c71c61c518518418318218118017617517417317217112d12c12b12a12912811e11d11c11b11a11907307006c06204e03a01c
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
