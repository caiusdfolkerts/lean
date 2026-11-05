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
def ridgeSupport832_000 : List Nat := [43,73,93,113,123,127,129,316,317,318,319,320,321,331,332,333,334,335,336,472,473,474,475,476,477,487,488,489,490,491,492,628]
def ridgeSupport832_001 : List Nat := [629,630,631,632,633,643,644,645,646,647,648,712,713,714,715,716,717,727,728,729,730,731,732,754,756,757,758,761,762,767,768,774]
def ridgeSupport832_002 : List Nat := [775,777,778,893,894,895,896,897,898,908,909,910,911,912,913,1049,1050,1051,1052,1053,1054,1064,1065,1066,1067,1068,1069,1133,1134,1135,1136,1137]
def ridgeSupport832_003 : List Nat := [1138,1148,1149,1150,1151,1152,1153,1175,1177,1178,1179,1182,1183,1188,1189,1195,1196,1198,1199,1314,1315,1316,1317,1318,1319,1329,1330,1331,1332,1333,1334,1398]
def ridgeSupport832_004 : List Nat := [1399,1400,1401,1402,1403,1413,1414,1415,1416,1417,1418,1440,1442,1443,1444,1447,1448,1453,1454,1460,1461,1463,1464,1579,1580,1581,1582,1583,1584,1594,1595,1596]
def ridgeSupport832_005 : List Nat := [1597,1598,1599,1663,1664,1665,1666,1667,1668,1678,1679,1680,1681,1682,1683,1705,1707,1708,1709,1712,1713,1718,1719,1725,1726,1728,1729,1772,1773,1774,1775,1776]
def ridgeSupport832_006 : List Nat := [1777,1787,1788,1789,1790,1791,1792,1814,1816,1817,1818,1821,1822,1827,1828,1834,1835,1837,1838,1839,1841,1842,1843,1846,1847,1852,1853,1859,1860,1862,1863,1870]
def ridgeSupport832_007 : List Nat := [1871,1872,1873,1874,1875,1906,1907,1908,1909,1910,1911,1942,1943,1944,1945,1946,1947,1984,1985,1986,1987,1988,1989,2002,2003,2004,2005,2006,2007,2038,2039,2040]
def ridgeSupport832_008 : List Nat := [2041,2042,2043,2080,2081,2082,2083,2084,2085,2098,2099,2100,2101,2102,2103,2134,2135,2136,2137,2138,2139,2176,2177,2178,2179,2180,2181,2194,2195,2196,2197,2198]
def ridgeSupport832_009 : List Nat := [2199,2236,2237,2238,2239,2240,2241,2254,2255,2256,2257,2258,2259,2290,2291,2292,2293,2294,2295,2332,2333,2334,2335,2336,2337,2350,2351,2352,2353,2354,2355,2392]
def ridgeSupport832_010 : List Nat := [2393,2394,2395,2396,2397,2410,2411,2412,2413,2414,2415,2452,2453,2454,2455,2456,2457,2476,2477,2478,2479,2480,2481,2488,2489,2491,2493,2501,2502,2503,2504,2507]
def ridgeSupport832_011 : List Nat := [2508,2509,2510,2536,2537,2539,2541,2549,2550,2551,2552,2555,2556,2557,2558,2584,2585,2587,2589,2597,2598,2599,2600,2603,2604,2605,2606,2704,2705,2707,2709,2717]
def ridgeSupport832_012 : List Nat := [2718,2719,2720,2723,2724,2725,2726,2752,2753,2755,2757,2765,2766,2767,2768,2771,2772,2773,2774,2872,2873,2875,2877,2885,2886,2887,2888,2891,2892,2893,2894,2920]
def ridgeSupport832_013 : List Nat := [2921,2923,2925,2933,2934,2935,2936,2939,2940,2941,2942,3040,3041,3043,3045,3053,3054,3055,3056,3059,3060,3061,3062,3160,3161,3163,3165,3173,3174,3175,3176,3179]
def ridgeSupport832_014 : List Nat := [3180,3181,3182,3208,3209,3211,3213,3221,3222,3223,3224,3227,3228,3229,3230,3328,3329,3331,3333,3341,3342,3343,3344,3347,3348,3349,3350,3448,3449,3451,3453,3461]
def ridgeSupport832_015 : List Nat := [3462,3463,3464,3467,3468,3469,3470]
def ridgeSupport832_code : Nat := 0xd8ed8dd8cd8bd88d87d86d85d7dd7bd79d78d16d15d14d13d10d0fd0ed0dd05d03d01d00c9ec9dc9cc9bc98c97c96c95c8dc8bc89c88c6ec6dc6cc6bc68c67c66c65c5dc5bc59c58bf6bf5bf4bf3bf0befbeebedbe5be3be1be0b7eb7db7cb7bb78b77b76b75b6db6bb69b68b4eb4db4cb4bb48b47b46b45b3db3bb39b38ad6ad5ad4ad3ad0acfaceacdac5ac3ac1ac0aa6aa5aa4aa3aa0a9fa9ea9da95a93a91a90a2ea2da2ca2ba28a27a26a25a1da1ba19a189fe9fd9fc9fb9f89f79f69f59ed9eb9e99e89ce9cd9cc9cb9c89c79c69c59bd9bb9b99b89b19b09af9ae9ad9ac99999899799699599496f96e96d96c96b96a95d95c95b95a95995893393293193092f92e92192091f91e91d91c8f78f68f58f48f38f28d38d28d18d08cf8ce8c18c08bf8be8bd8bc89789689589489389288588488388288188085b85a8598588578568378368358348338328258248238228218207fb7fa7f97f87f77f67d77d67d57d47d37d27c57c47c37c27c17c079b79a79979879779677777677577477377275375275175074f74e74774674474373d73c73773673373273172f72e72d72b72a72472371e71d71a7197187167006ff6fe6fd6fc6fb6f16f06ef6ee6ed6ec6c16c06be6bd6b76b66b16b06ad6ac6ab6a969369269169068f68e68468368268168067f63f63e63d63c63b63a63062f62e62d62c62b5b85b75b55b45ae5ad5a85a75a45a35a25a058a58958858758658557b57a5795785775765365355345335325315275265255245235224af4ae4ac4ab4a54a449f49e49b49a49949748148047f47e47d47c47247147046f46e46d42d42c42b42a42942841e41d41c41b41a41939139038f38e38d38c38238138037f37e37d30a3093073063002ff2fa2f92f62f52f42f22dc2db2da2d92d82d72cd2cc2cb2ca2c92c82882872862852842832792782772762752741ec1eb1ea1e91e81e71dd1dc1db1da1d91d815014f14e14d14c14b14114013f13e13d13c08107f07b07105d04902b
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
def ridgeSupport832_rest_010 : Nat := PackedRawNatGrowth.drop 3840 ridgeSupport832_code
def ridgeSupport832_rest_011 : Nat := PackedRawNatGrowth.drop 4224 ridgeSupport832_code
def ridgeSupport832_rest_012 : Nat := PackedRawNatGrowth.drop 4608 ridgeSupport832_code
def ridgeSupport832_rest_013 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport832_code
def ridgeSupport832_rest_014 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport832_code
def ridgeSupport832_rest_015 : Nat := PackedRawNatGrowth.drop 5760 ridgeSupport832_code
def ridgeSupport832_rest_016 : Nat := PackedRawNatGrowth.drop 5844 ridgeSupport832_code
def ridgeSupport832_suffix_016 : List Nat := []
def ridgeSupport832_suffix_015 : List Nat := ridgeSupport832_015 ++ ridgeSupport832_suffix_016
def ridgeSupport832_suffix_014 : List Nat := ridgeSupport832_014 ++ ridgeSupport832_suffix_015
def ridgeSupport832_suffix_013 : List Nat := ridgeSupport832_013 ++ ridgeSupport832_suffix_014
def ridgeSupport832_suffix_012 : List Nat := ridgeSupport832_012 ++ ridgeSupport832_suffix_013
def ridgeSupport832_suffix_011 : List Nat := ridgeSupport832_011 ++ ridgeSupport832_suffix_012
def ridgeSupport832_suffix_010 : List Nat := ridgeSupport832_010 ++ ridgeSupport832_suffix_011
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
    (PackedRawNatGrowth.readList 12 487 ridgeSupport832_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
