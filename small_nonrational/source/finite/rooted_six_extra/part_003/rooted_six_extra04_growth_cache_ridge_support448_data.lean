module
prelude
public import RootedSixExtra04GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport448_000 : List Nat := [41,71,91,111,121,125,129,274,275,276,277,278,279,289,290,291,292,293,294,430,431,432,433,434,435,445,446,447,448,449,450,586]
def ridgeSupport448_001 : List Nat := [587,588,589,590,591,601,602,603,604,605,606,670,671,672,673,674,675,685,686,687,688,689,690,754,755,756,760,762,763,767,769,770]
def ridgeSupport448_002 : List Nat := [772,773,775,851,852,853,854,855,856,866,867,868,869,870,871,1007,1008,1009,1010,1011,1012,1022,1023,1024,1025,1026,1027,1091,1092,1093,1094,1095]
def ridgeSupport448_003 : List Nat := [1096,1106,1107,1108,1109,1110,1111,1175,1176,1177,1181,1183,1184,1188,1190,1191,1193,1194,1196,1272,1273,1274,1275,1276,1277,1287,1288,1289,1290,1291,1292,1356]
def ridgeSupport448_004 : List Nat := [1357,1358,1359,1360,1361,1371,1372,1373,1374,1375,1376,1440,1441,1442,1446,1448,1449,1453,1455,1456,1458,1459,1461,1537,1538,1539,1540,1541,1542,1552,1553,1554]
def ridgeSupport448_005 : List Nat := [1555,1556,1557,1621,1622,1623,1624,1625,1626,1636,1637,1638,1639,1640,1641,1705,1706,1707,1711,1713,1714,1718,1720,1721,1723,1724,1726,1730,1731,1732,1733,1734]
def ridgeSupport448_006 : List Nat := [1735,1745,1746,1747,1748,1749,1750,1814,1815,1816,1820,1822,1823,1827,1829,1830,1832,1833,1835,1839,1840,1841,1845,1847,1848,1852,1854,1855,1857,1858,1860,1882]
def ridgeSupport448_007 : List Nat := [1883,1884,1885,1886,1887,1918,1919,1920,1921,1922,1923,1954,1955,1956,1957,1958,1959,1972,1973,1974,1975,1976,1977,2014,2015,2016,2017,2018,2019,2050,2051,2052]
def ridgeSupport448_008 : List Nat := [2053,2054,2055,2068,2069,2070,2071,2072,2073,2110,2111,2112,2113,2114,2115,2146,2147,2148,2149,2150,2151,2164,2165,2166,2167,2168,2169,2206,2207,2208,2209,2210]
def ridgeSupport448_009 : List Nat := [2211,2224,2225,2226,2227,2228,2229,2266,2267,2268,2269,2270,2271,2302,2303,2304,2305,2306,2307,2320,2321,2322,2323,2324,2325,2362,2363,2364,2365,2366,2367,2380]
def ridgeSupport448_010 : List Nat := [2381,2382,2383,2384,2385,2422,2423,2424,2425,2426,2427,2440,2441,2442,2443,2444,2445,2464,2465,2466,2467,2468,2469,2488,2490,2492,2493,2494,2496,2498,2499,2500]
def ridgeSupport448_011 : List Nat := [2502,2504,2505,2536,2538,2540,2541,2542,2544,2546,2547,2548,2550,2552,2553,2584,2586,2588,2589,2590,2592,2594,2595,2596,2598,2600,2601,2704,2706,2708,2709,2710]
def ridgeSupport448_012 : List Nat := [2712,2714,2715,2716,2718,2720,2721,2752,2754,2756,2757,2758,2760,2762,2763,2764,2766,2768,2769,2872,2874,2876,2877,2878,2880,2882,2883,2884,2886,2888,2889,2920]
def ridgeSupport448_013 : List Nat := [2922,2924,2925,2926,2928,2930,2931,2932,2934,2936,2937,3040,3042,3044,3045,3046,3048,3050,3051,3052,3054,3056,3057,3160,3162,3164,3165,3166,3168,3170,3171,3172]
def ridgeSupport448_014 : List Nat := [3174,3176,3177,3208,3210,3212,3213,3214,3216,3218,3219,3220,3222,3224,3225,3328,3330,3332,3333,3334,3336,3338,3339,3340,3342,3344,3345,3448,3450,3452,3453,3454]
def ridgeSupport448_015 : List Nat := [3456,3458,3459,3460,3462,3464,3465]
def ridgeSupport448_code : Nat := 0xd89d88d86d84d83d82d80d7ed7dd7cd7ad78d11d10d0ed0cd0bd0ad08d06d05d04d02d00c99c98c96c94c93c92c90c8ec8dc8cc8ac88c69c68c66c64c63c62c60c5ec5dc5cc5ac58bf1bf0beebecbebbeabe8be6be5be4be2be0b79b78b76b74b73b72b70b6eb6db6cb6ab68b49b48b46b44b43b42b40b3eb3db3cb3ab38ad1ad0aceaccacbacaac8ac6ac5ac4ac2ac0aa1aa0a9ea9ca9ba9aa98a96a95a94a92a90a29a28a26a24a23a22a20a1ea1da1ca1aa189f99f89f69f49f39f29f09ee9ed9ec9ea9e89c99c89c69c49c39c29c09be9bd9bc9ba9b89a59a49a39a29a19a098d98c98b98a98998897b97a97997897797695195094f94e94d94c93f93e93d93c93b93a9159149139129119109039029019008ff8fe8df8de8dd8dc8db8da8b58b48b38b28b18b08a38a28a18a089f89e87987887787687587486786686586486386284384284184083f83e8198188178168158148078068058048038027e37e27e17e07df7de7b97b87b77b67b57b47a77a67a57a47a37a278378278178077f77e75f75e75d75c75b75a74474274173f73e73c73873773573173072f72b72972872672572371f71e71c7187177166d66d56d46d36d26d16c76c66c56c46c36c26be6bc6bb6b96b86b66b26b16af6ab6aa6a966966866766666566465a6596586576566556156146136126116106066056046036026015b55b35b25b05af5ad5a95a85a65a25a15a056055f55e55d55c55b55155054f54e54d54c50c50b50a5095085074fd4fc4fb4fa4f94f84ac4aa4a94a74a64a44a049f49d4994984974574564554544534524484474464454444434034024014003ff3fe3f43f33f23f13f03ef3673663653643633623583573563553543533073053043023012ff2fb2fa2f82f42f32f22b22b12b02af2ae2ad2a32a22a12a029f29e25e25d25c25b25a25924f24e24d24c24b24a1c21c11c01bf1be1bd1b31b21b11b01af1ae12612512412312212111711611511411311208107d07906f05b047029
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
def ridgeSupport448_rest_015 : Nat := PackedRawNatGrowth.drop 5760 ridgeSupport448_code
def ridgeSupport448_rest_016 : Nat := PackedRawNatGrowth.drop 5844 ridgeSupport448_code
def ridgeSupport448_suffix_016 : List Nat := []
def ridgeSupport448_suffix_015 : List Nat := ridgeSupport448_015 ++ ridgeSupport448_suffix_016
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
    (PackedRawNatGrowth.readList 12 487 ridgeSupport448_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
