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
def ridgeSupport704_000 : List Nat := [42,72,92,112,122,126,129,295,296,297,298,299,300,310,311,312,313,314,315,451,452,453,454,455,456,466,467,468,469,470,471,607]
def ridgeSupport704_001 : List Nat := [608,609,610,611,612,622,623,624,625,626,627,691,692,693,694,695,696,706,707,708,709,710,711,754,755,757,759,761,763,768,769,771]
def ridgeSupport704_002 : List Nat := [772,776,778,872,873,874,875,876,877,887,888,889,890,891,892,1028,1029,1030,1031,1032,1033,1043,1044,1045,1046,1047,1048,1112,1113,1114,1115,1116]
def ridgeSupport704_003 : List Nat := [1117,1127,1128,1129,1130,1131,1132,1175,1176,1178,1180,1182,1184,1189,1190,1192,1193,1197,1199,1293,1294,1295,1296,1297,1298,1308,1309,1310,1311,1312,1313,1377]
def ridgeSupport704_004 : List Nat := [1378,1379,1380,1381,1382,1392,1393,1394,1395,1396,1397,1440,1441,1443,1445,1447,1449,1454,1455,1457,1458,1462,1464,1558,1559,1560,1561,1562,1563,1573,1574,1575]
def ridgeSupport704_005 : List Nat := [1576,1577,1578,1642,1643,1644,1645,1646,1647,1657,1658,1659,1660,1661,1662,1705,1706,1708,1710,1712,1714,1719,1720,1722,1723,1727,1729,1751,1752,1753,1754,1755]
def ridgeSupport704_006 : List Nat := [1756,1766,1767,1768,1769,1770,1771,1814,1815,1817,1819,1821,1823,1828,1829,1831,1832,1836,1838,1839,1840,1842,1844,1846,1848,1853,1854,1856,1857,1861,1863,1876]
def ridgeSupport704_007 : List Nat := [1877,1878,1879,1880,1881,1912,1913,1914,1915,1916,1917,1948,1949,1950,1951,1952,1953,1978,1979,1980,1981,1982,1983,2008,2009,2010,2011,2012,2013,2044,2045,2046]
def ridgeSupport704_008 : List Nat := [2047,2048,2049,2074,2075,2076,2077,2078,2079,2104,2105,2106,2107,2108,2109,2140,2141,2142,2143,2144,2145,2170,2171,2172,2173,2174,2175,2200,2201,2202,2203,2204]
def ridgeSupport704_009 : List Nat := [2205,2230,2231,2232,2233,2234,2235,2260,2261,2262,2263,2264,2265,2296,2297,2298,2299,2300,2301,2326,2327,2328,2329,2330,2331,2356,2357,2358,2359,2360,2361,2386]
def ridgeSupport704_010 : List Nat := [2387,2388,2389,2390,2391,2416,2417,2418,2419,2420,2421,2446,2447,2448,2449,2450,2451,2470,2471,2472,2473,2474,2475,2489,2490,2491,2492,2495,2496,2497,2498,2506]
def ridgeSupport704_011 : List Nat := [2508,2510,2511,2537,2538,2539,2540,2543,2544,2545,2546,2554,2556,2558,2559,2585,2586,2587,2588,2591,2592,2593,2594,2602,2604,2606,2607,2705,2706,2707,2708,2711]
def ridgeSupport704_012 : List Nat := [2712,2713,2714,2722,2724,2726,2727,2753,2754,2755,2756,2759,2760,2761,2762,2770,2772,2774,2775,2873,2874,2875,2876,2879,2880,2881,2882,2890,2892,2894,2895,2921]
def ridgeSupport704_013 : List Nat := [2922,2923,2924,2927,2928,2929,2930,2938,2940,2942,2943,3041,3042,3043,3044,3047,3048,3049,3050,3058,3060,3062,3063,3161,3162,3163,3164,3167,3168,3169,3170,3178]
def ridgeSupport704_014 : List Nat := [3180,3182,3183,3209,3210,3211,3212,3215,3216,3217,3218,3226,3228,3230,3231,3329,3330,3331,3332,3335,3336,3337,3338,3346,3348,3350,3351,3449,3450,3451,3452,3455]
def ridgeSupport704_015 : List Nat := [3456,3457,3458,3466,3468,3470,3471]
def ridgeSupport704_code : Nat := 0xd8fd8ed8cd8ad82d81d80d7fd7cd7bd7ad79d17d16d14d12d0ad09d08d07d04d03d02d01c9fc9ec9cc9ac92c91c90c8fc8cc8bc8ac89c6fc6ec6cc6ac62c61c60c5fc5cc5bc5ac59bf7bf6bf4bf2beabe9be8be7be4be3be2be1b7fb7eb7cb7ab72b71b70b6fb6cb6bb6ab69b4fb4eb4cb4ab42b41b40b3fb3cb3bb3ab39ad7ad6ad4ad2acaac9ac8ac7ac4ac3ac2ac1aa7aa6aa4aa2a9aa99a98a97a94a93a92a91a2fa2ea2ca2aa22a21a20a1fa1ca1ba1aa199ff9fe9fc9fa9f29f19f09ef9ec9eb9ea9e99cf9ce9cc9ca9c29c19c09bf9bc9bb9ba9b99ab9aa9a99a89a79a699399299199098f98e97597497397297197095795695595495395293993893793693593491b91a9199189179168fd8fc8fb8fa8f98f88d98d88d78d68d58d48bb8ba8b98b88b78b689d89c89b89a89989887f87e87d87c87b87a86186085f85e85d85c83d83c83b83a83983881f81e81d81c81b81a8018007ff7fe7fd7fc7dd7dc7db7da7d97d87bf7be7bd7bc7bb7ba7a17a079f79e79d79c77d77c77b77a77977875975875775675575474774574174073e73d73873673473273072f72e72c72872772572471f71d71b7197177166eb6ea6e96e86e76e66dc6db6da6d96d86d76c16bf6bb6ba6b86b76b26b06ae6ac6aa6a967e67d67c67b67a67966f66e66d66c66b66a62a62962862762662561b61a6196186176165b85b65b25b15af5ae5a95a75a55a35a15a057557457357257157056656556456356256152152051f51e51d51c51251151050f50e50d4af4ad4a94a84a64a54a049e49c49a49849746c46b46a46946846745d45c45b45a45945841841741641541441340940840740640540437c37b37a37937837736d36c36b36a36936830a3083043033013002fb2f92f72f52f32f22c72c62c52c42c32c22b82b72b62b52b42b327327227127026f26e26426326226126025f1d71d61d51d41d31d21c81c71c61c51c41c313b13a13913813713612c12b12a12912812708107e07a07005c04802a
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
def ridgeSupport704_rest_014 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport704_code
def ridgeSupport704_rest_015 : Nat := PackedRawNatGrowth.drop 5760 ridgeSupport704_code
def ridgeSupport704_rest_016 : Nat := PackedRawNatGrowth.drop 5844 ridgeSupport704_code
def ridgeSupport704_suffix_016 : List Nat := []
def ridgeSupport704_suffix_015 : List Nat := ridgeSupport704_015 ++ ridgeSupport704_suffix_016
def ridgeSupport704_suffix_014 : List Nat := ridgeSupport704_014 ++ ridgeSupport704_suffix_015
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
    (PackedRawNatGrowth.readList 12 487 ridgeSupport704_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
