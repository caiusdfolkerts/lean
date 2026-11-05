module
prelude
public import RootedSixBase04GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport448_000 : List Nat := [41,71,91,111,121,125,129,274,275,276,277,278,279,289,290,291,292,293,294,430,431,432,433,434,435,445,446,447,448,449,450,586]
def ridgeSupport448_001 : List Nat := [587,588,589,590,591,601,602,603,604,605,606,670,671,672,673,674,675,685,686,687,688,689,690,754,755,756,760,762,763,767,769,770]
def ridgeSupport448_002 : List Nat := [772,773,775,851,852,853,854,855,856,866,867,868,869,870,871,1007,1008,1009,1010,1011,1012,1022,1023,1024,1025,1026,1027,1091,1092,1093,1094,1095]
def ridgeSupport448_003 : List Nat := [1096,1106,1107,1108,1109,1110,1111,1175,1176,1177,1181,1183,1184,1188,1190,1191,1193,1194,1196,1272,1273,1274,1275,1276,1277,1287,1288,1289,1290,1291,1292,1356]
def ridgeSupport448_004 : List Nat := [1357,1358,1359,1360,1361,1371,1372,1373,1374,1375,1376,1440,1441,1442,1446,1448,1449,1453,1455,1456,1458,1459,1461,1537,1538,1539,1540,1541,1542,1552,1553,1554]
def ridgeSupport448_005 : List Nat := [1555,1556,1557,1621,1622,1623,1624,1625,1626,1636,1637,1638,1639,1640,1641,1705,1706,1707,1711,1713,1714,1718,1720,1721,1723,1724,1726,1730,1731,1732,1733,1734]
def ridgeSupport448_006 : List Nat := [1735,1745,1746,1747,1748,1749,1750,1814,1815,1816,1820,1822,1823,1827,1829,1830,1832,1833,1835,1839,1840,1841,1845,1847,1848,1852,1854,1855,1857,1858,1860,1868]
def ridgeSupport448_007 : List Nat := [1869,1872,1873,1874,1875,1880,1881,1884,1885,1886,1887,1892,1893,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1928,1929,1932,1933,1934,1935,1940,1941,1944]
def ridgeSupport448_008 : List Nat := [1945,1946,1947,1948,1949,1950,1951,1952,1953,1976,1977,1980,1981,1982,1983,1988,1989,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2024,2025,2028,2029,2030]
def ridgeSupport448_009 : List Nat := [2031,2032,2033,2034,2035,2036,2037,2060,2061,2064,2065,2066,2067,2072,2073,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2108,2109,2112,2113,2114,2115,2116]
def ridgeSupport448_010 : List Nat := [2117,2118,2119,2120,2121,2144,2145,2148,2149,2150,2151,2152,2153,2154,2155,2156,2157,2176,2177,2178,2179,2180,2181,2218,2219,2220,2221,2222,2223,2254,2255,2256]
def ridgeSupport448_011 : List Nat := [2257,2258,2259,2290,2291,2292,2293,2294,2295,2308,2309,2310,2311,2312,2313,2350,2351,2352,2353,2354,2355,2386,2387,2388,2389,2390,2391,2404,2405,2406,2407,2408]
def ridgeSupport448_012 : List Nat := [2409,2446,2447,2448,2449,2450,2451,2482,2483,2484,2485,2486,2487,2500,2501,2502,2503,2504,2505,2542,2543,2544,2545,2546,2547,2560,2561,2562,2563,2564,2565,2602]
def ridgeSupport448_013 : List Nat := [2603,2604,2605,2606,2607,2638,2639,2640,2641,2642,2643,2656,2657,2658,2659,2660,2661,2698,2699,2700,2701,2702,2703,2716,2717,2718,2719,2720,2721,2758,2759,2760]
def ridgeSupport448_014 : List Nat := [2761,2762,2763,2776,2777,2778,2779,2780,2781,2800,2801,2802,2803,2804,2805]
def ridgeSupport448_code : Nat := 0xaf5af4af3af2af1af0addadcadbadaad9ad8acbacaac9ac8ac7ac6aa1aa0a9fa9ea9da9ca8fa8ea8da8ca8ba8aa65a64a63a62a61a60a53a52a51a50a4fa4ea2fa2ea2da2ca2ba2aa05a04a03a02a01a009f39f29f19f09ef9ee9c99c89c79c69c59c49b79b69b59b49b39b299399299199098f98e96996896796696596495795695595495395293393293193092f92e9099089079069059048f78f68f58f48f38f28d38d28d18d08cf8ce8af8ae8ad8ac8ab8aa88588488388288188086d86c86b86a86986886786686586486186084984884784684584484384284184083d83c82582482382282182081f81e81d81c81981881381281181080d80c7f57f47f37f27f17f07ef7ee7ed7ec7e97e87d17d07cf7ce7cd7cc7cb7ca7c97c87c57c47bf7be7bd7bc7b97b87a17a079f79e79d79c79b79a79979879579478f78e78d78c78978877177076f76e76d76c76b76a76976876576475f75e75d75c75975875375275175074d74c74474274173f73e73c73873773573173072f72b72972872672572371f71e71c7187177166d66d56d46d36d26d16c76c66c56c46c36c26be6bc6bb6b96b86b66b26b16af6ab6aa6a966966866766666566465a6596586576566556156146136126116106066056046036026015b55b35b25b05af5ad5a95a85a65a25a15a056055f55e55d55c55b55155054f54e54d54c50c50b50a5095085074fd4fc4fb4fa4f94f84ac4aa4a94a74a64a44a049f49d4994984974574564554544534524484474464454444434034024014003ff3fe3f43f33f23f13f03ef3673663653643633623583573563553543533073053043023012ff2fb2fa2f82f42f32f22b22b12b02af2ae2ad2a32a22a12a029f29e25e25d25c25b25a25924f24e24d24c24b24a1c21c11c01bf1be1bd1b31b21b11b01af1ae12612512412312212111711611511411311208107d07906f05b047029
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
def ridgeSupport448_rest_014 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport448_code
def ridgeSupport448_rest_015 : Nat := PackedRawNatGrowth.drop 5556 ridgeSupport448_code
def ridgeSupport448_suffix_015 : List Nat := []
def ridgeSupport448_suffix_014 : List Nat := ridgeSupport448_014 ++ ridgeSupport448_suffix_015
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
    (PackedRawNatGrowth.readList 12 463 ridgeSupport448_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
