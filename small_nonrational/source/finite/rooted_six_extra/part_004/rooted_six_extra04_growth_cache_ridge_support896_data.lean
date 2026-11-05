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
def ridgeSupport896_000 : List Nat := [44,74,94,114,124,128,129,337,338,339,340,341,342,352,353,354,355,356,357,493,494,495,496,497,498,508,509,510,511,512,513,649]
def ridgeSupport896_001 : List Nat := [650,651,652,653,654,664,665,666,667,668,669,733,734,735,736,737,738,748,749,750,751,752,753,755,756,757,758,759,760,770,771,773]
def ridgeSupport896_002 : List Nat := [774,776,777,914,915,916,917,918,919,929,930,931,932,933,934,1070,1071,1072,1073,1074,1075,1085,1086,1087,1088,1089,1090,1154,1155,1156,1157,1158]
def ridgeSupport896_003 : List Nat := [1159,1169,1170,1171,1172,1173,1174,1176,1177,1178,1179,1180,1181,1191,1192,1194,1195,1197,1198,1335,1336,1337,1338,1339,1340,1350,1351,1352,1353,1354,1355,1419]
def ridgeSupport896_004 : List Nat := [1420,1421,1422,1423,1424,1434,1435,1436,1437,1438,1439,1441,1442,1443,1444,1445,1446,1456,1457,1459,1460,1462,1463,1600,1601,1602,1603,1604,1605,1615,1616,1617]
def ridgeSupport896_005 : List Nat := [1618,1619,1620,1684,1685,1686,1687,1688,1689,1699,1700,1701,1702,1703,1704,1706,1707,1708,1709,1710,1711,1721,1722,1724,1725,1727,1728,1793,1794,1795,1796,1797]
def ridgeSupport896_006 : List Nat := [1798,1808,1809,1810,1811,1812,1813,1815,1816,1817,1818,1819,1820,1830,1831,1833,1834,1836,1837,1840,1841,1842,1843,1844,1845,1855,1856,1858,1859,1861,1862,1864]
def ridgeSupport896_007 : List Nat := [1865,1866,1867,1868,1869,1900,1901,1902,1903,1904,1905,1936,1937,1938,1939,1940,1941,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2032,2033,2034]
def ridgeSupport896_008 : List Nat := [2035,2036,2037,2086,2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2128,2129,2130,2131,2132,2133,2182,2183,2184,2185,2186,2187,2188,2189,2190,2191,2192]
def ridgeSupport896_009 : List Nat := [2193,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2284,2285,2286,2287,2288,2289,2338,2339,2340,2341,2342,2343,2344,2345,2346,2347,2348,2349,2398]
def ridgeSupport896_010 : List Nat := [2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2458,2459,2460,2461,2462,2463,2482,2483,2484,2485,2486,2487,2494,2495,2497,2499,2500,2501,2503,2505,2506]
def ridgeSupport896_011 : List Nat := [2507,2509,2511,2542,2543,2545,2547,2548,2549,2551,2553,2554,2555,2557,2559,2590,2591,2593,2595,2596,2597,2599,2601,2602,2603,2605,2607,2710,2711,2713,2715,2716]
def ridgeSupport896_012 : List Nat := [2717,2719,2721,2722,2723,2725,2727,2758,2759,2761,2763,2764,2765,2767,2769,2770,2771,2773,2775,2878,2879,2881,2883,2884,2885,2887,2889,2890,2891,2893,2895,2926]
def ridgeSupport896_013 : List Nat := [2927,2929,2931,2932,2933,2935,2937,2938,2939,2941,2943,3046,3047,3049,3051,3052,3053,3055,3057,3058,3059,3061,3063,3166,3167,3169,3171,3172,3173,3175,3177,3178]
def ridgeSupport896_014 : List Nat := [3179,3181,3183,3214,3215,3217,3219,3220,3221,3223,3225,3226,3227,3229,3231,3334,3335,3337,3339,3340,3341,3343,3345,3346,3347,3349,3351,3454,3455,3457,3459,3460]
def ridgeSupport896_015 : List Nat := [3461,3463,3465,3466,3467,3469,3471]
def ridgeSupport896_code : Nat := 0xd8fd8dd8bd8ad89d87d85d84d83d81d7fd7ed17d15d13d12d11d0fd0dd0cd0bd09d07d06c9fc9dc9bc9ac99c97c95c94c93c91c8fc8ec6fc6dc6bc6ac69c67c65c64c63c61c5fc5ebf7bf5bf3bf2bf1befbedbecbebbe9be7be6b7fb7db7bb7ab79b77b75b74b73b71b6fb6eb4fb4db4bb4ab49b47b45b44b43b41b3fb3ead7ad5ad3ad2ad1acfacdaccacbac9ac7ac6aa7aa5aa3aa2aa1a9fa9da9ca9ba99a97a96a2fa2da2ba2aa29a27a25a24a23a21a1fa1e9ff9fd9fb9fa9f99f79f59f49f39f19ef9ee9cf9cd9cb9ca9c99c79c59c49c39c19bf9be9b79b69b59b49b39b299f99e99d99c99b99a96996896796696596496396296196095f95e92d92c92b92a9299289279269259249239228f18f08ef8ee8ed8ec8cd8cc8cb8ca8c98c88c78c68c58c48c38c289189088f88e88d88c88b88a88988888788685585485385285185083183082f82e82d82c82b82a8298288278267f57f47f37f27f17f07d17d07cf7ce7cd7cc7cb7ca7c97c87c77c679579479379279179077177076f76e76d76c74d74c74b74a74974874674574374274073f73573473373273173072d72c72a72972772671c71b71a7197187177157147137127117107067057047037027016c06bf6bd6bc6ba6b96af6ae6ad6ac6ab6aa6a86a76a66a56a46a369969869769669569465465365265165064f6456446436426416405b75b65b45b35b15b05a65a55a45a35a25a159f59e59d59c59b59a59058f58e58d58c58b54b54a54954854754653c53b53a5395385374ae4ad4ab4aa4a84a749d49c49b49a49949849649549449349249148748648548448348244244144043f43e43d43343243143042f42e3a63a53a43a33a23a13973963953943933923093083063053033022f82f72f62f52f42f32f12f02ef2ee2ed2ec2e22e12e02df2de2dd29d29c29b29a29929828e28d28c28b28a2892012001ff1fe1fd1fc1f21f11f01ef1ee1ed16516416316216116015615515415315215108108007c07205e04a02c
def ridgeSupport896_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport896_code
def ridgeSupport896_rest_001 : Nat := PackedRawNatGrowth.drop 384 ridgeSupport896_code
def ridgeSupport896_rest_002 : Nat := PackedRawNatGrowth.drop 768 ridgeSupport896_code
def ridgeSupport896_rest_003 : Nat := PackedRawNatGrowth.drop 1152 ridgeSupport896_code
def ridgeSupport896_rest_004 : Nat := PackedRawNatGrowth.drop 1536 ridgeSupport896_code
def ridgeSupport896_rest_005 : Nat := PackedRawNatGrowth.drop 1920 ridgeSupport896_code
def ridgeSupport896_rest_006 : Nat := PackedRawNatGrowth.drop 2304 ridgeSupport896_code
def ridgeSupport896_rest_007 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport896_code
def ridgeSupport896_rest_008 : Nat := PackedRawNatGrowth.drop 3072 ridgeSupport896_code
def ridgeSupport896_rest_009 : Nat := PackedRawNatGrowth.drop 3456 ridgeSupport896_code
def ridgeSupport896_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport896_code
def ridgeSupport896_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport896_code
def ridgeSupport896_rest_012 : Nat := PackedRawNatGrowth.drop 4608 ridgeSupport896_code
def ridgeSupport896_rest_013 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport896_code
def ridgeSupport896_rest_014 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport896_code
def ridgeSupport896_rest_015 : Nat := PackedRawNatGrowth.drop 5760 ridgeSupport896_code
def ridgeSupport896_rest_016 : Nat := PackedRawNatGrowth.drop 5844 ridgeSupport896_code
def ridgeSupport896_suffix_016 : List Nat := []
def ridgeSupport896_suffix_015 : List Nat := ridgeSupport896_015 ++ ridgeSupport896_suffix_016
def ridgeSupport896_suffix_014 : List Nat := ridgeSupport896_014 ++ ridgeSupport896_suffix_015
def ridgeSupport896_suffix_013 : List Nat := ridgeSupport896_013 ++ ridgeSupport896_suffix_014
def ridgeSupport896_suffix_012 : List Nat := ridgeSupport896_012 ++ ridgeSupport896_suffix_013
def ridgeSupport896_suffix_011 : List Nat := ridgeSupport896_011 ++ ridgeSupport896_suffix_012
def ridgeSupport896_suffix_010 : List Nat := ridgeSupport896_010 ++ ridgeSupport896_suffix_011
def ridgeSupport896_suffix_009 : List Nat := ridgeSupport896_009 ++ ridgeSupport896_suffix_010
def ridgeSupport896_suffix_008 : List Nat := ridgeSupport896_008 ++ ridgeSupport896_suffix_009
def ridgeSupport896_suffix_007 : List Nat := ridgeSupport896_007 ++ ridgeSupport896_suffix_008
def ridgeSupport896_suffix_006 : List Nat := ridgeSupport896_006 ++ ridgeSupport896_suffix_007
def ridgeSupport896_suffix_005 : List Nat := ridgeSupport896_005 ++ ridgeSupport896_suffix_006
def ridgeSupport896_suffix_004 : List Nat := ridgeSupport896_004 ++ ridgeSupport896_suffix_005
def ridgeSupport896_suffix_003 : List Nat := ridgeSupport896_003 ++ ridgeSupport896_suffix_004
def ridgeSupport896_suffix_002 : List Nat := ridgeSupport896_002 ++ ridgeSupport896_suffix_003
def ridgeSupport896_suffix_001 : List Nat := ridgeSupport896_001 ++ ridgeSupport896_suffix_002
def ridgeSupport896_suffix_000 : List Nat := ridgeSupport896_000 ++ ridgeSupport896_suffix_001
theorem ridgeSupport896_source : candidateSupports 896 =
    (PackedRawNatGrowth.readList 12 487 ridgeSupport896_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
