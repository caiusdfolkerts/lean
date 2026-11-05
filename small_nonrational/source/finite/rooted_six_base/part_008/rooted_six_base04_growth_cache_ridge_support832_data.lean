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
def ridgeSupport832_000 : List Nat := [43,73,93,113,123,127,129,316,317,318,319,320,321,331,332,333,334,335,336,472,473,474,475,476,477,487,488,489,490,491,492,628]
def ridgeSupport832_001 : List Nat := [629,630,631,632,633,643,644,645,646,647,648,712,713,714,715,716,717,727,728,729,730,731,732,754,756,757,758,761,762,767,768,774]
def ridgeSupport832_002 : List Nat := [775,777,778,893,894,895,896,897,898,908,909,910,911,912,913,1049,1050,1051,1052,1053,1054,1064,1065,1066,1067,1068,1069,1133,1134,1135,1136,1137]
def ridgeSupport832_003 : List Nat := [1138,1148,1149,1150,1151,1152,1153,1175,1177,1178,1179,1182,1183,1188,1189,1195,1196,1198,1199,1314,1315,1316,1317,1318,1319,1329,1330,1331,1332,1333,1334,1398]
def ridgeSupport832_004 : List Nat := [1399,1400,1401,1402,1403,1413,1414,1415,1416,1417,1418,1440,1442,1443,1444,1447,1448,1453,1454,1460,1461,1463,1464,1579,1580,1581,1582,1583,1584,1594,1595,1596]
def ridgeSupport832_005 : List Nat := [1597,1598,1599,1663,1664,1665,1666,1667,1668,1678,1679,1680,1681,1682,1683,1705,1707,1708,1709,1712,1713,1718,1719,1725,1726,1728,1729,1772,1773,1774,1775,1776]
def ridgeSupport832_006 : List Nat := [1777,1787,1788,1789,1790,1791,1792,1814,1816,1817,1818,1821,1822,1827,1828,1834,1835,1837,1838,1839,1841,1842,1843,1846,1847,1852,1853,1859,1860,1862,1863,1864]
def ridgeSupport832_007 : List Nat := [1865,1870,1871,1872,1873,1876,1877,1882,1883,1884,1885,1888,1889,1894,1895,1896,1897,1912,1913,1914,1915,1916,1917,1924,1925,1930,1931,1932,1933,1936,1937,1942]
def ridgeSupport832_008 : List Nat := [1943,1944,1945,1960,1961,1962,1963,1964,1965,1972,1973,1978,1979,1980,1981,1984,1985,1990,1991,1992,1993,2008,2009,2010,2011,2012,2013,2020,2021,2026,2027,2028]
def ridgeSupport832_009 : List Nat := [2029,2044,2045,2046,2047,2048,2049,2056,2057,2062,2063,2064,2065,2068,2069,2074,2075,2076,2077,2092,2093,2094,2095,2096,2097,2104,2105,2110,2111,2112,2113,2128]
def ridgeSupport832_010 : List Nat := [2129,2130,2131,2132,2133,2140,2141,2146,2147,2148,2149,2164,2165,2166,2167,2168,2169,2188,2189,2190,2191,2192,2193,2206,2207,2208,2209,2210,2211,2242,2243,2244]
def ridgeSupport832_011 : List Nat := [2245,2246,2247,2278,2279,2280,2281,2282,2283,2320,2321,2322,2323,2324,2325,2338,2339,2340,2341,2342,2343,2374,2375,2376,2377,2378,2379,2416,2417,2418,2419,2420]
def ridgeSupport832_012 : List Nat := [2421,2434,2435,2436,2437,2438,2439,2470,2471,2472,2473,2474,2475,2512,2513,2514,2515,2516,2517,2530,2531,2532,2533,2534,2535,2572,2573,2574,2575,2576,2577,2590]
def ridgeSupport832_013 : List Nat := [2591,2592,2593,2594,2595,2626,2627,2628,2629,2630,2631,2668,2669,2670,2671,2672,2673,2686,2687,2688,2689,2690,2691,2728,2729,2730,2731,2732,2733,2746,2747,2748]
def ridgeSupport832_014 : List Nat := [2749,2750,2751,2788,2789,2790,2791,2792,2793,2812,2813,2814,2815,2816,2817]
def ridgeSupport832_code : Nat := 0xb01b00affafeafdafcae9ae8ae7ae6ae5ae4abfabeabdabcabbabaaadaacaabaaaaa9aa8a83a82a81a80a7fa7ea71a70a6fa6ea6da6ca47a46a45a44a43a42a23a22a21a20a1fa1ea11a10a0fa0ea0da0c9e79e69e59e49e39e29d59d49d39d29d19d09ab9aa9a99a89a79a698798698598498398297597497397297197094b94a9499489479469279269259249239229159149139129119108eb8ea8e98e88e78e68c78c68c58c48c38c28a38a28a18a089f89e89189088f88e88d88c87987887787687587486586486386285d85c85585485385285185084184083f83e83983883183082f82e82d82c81d81c81b81a81581481181080f80e8098088018007ff7fe7fd7fc7ed7ec7eb7ea7e57e47dd7dc7db7da7d97d87c97c87c77c67c17c07bd7bc7bb7ba7b57b47ad7ac7ab7aa7a97a879979879779679179078d78c78b78a78578477d77c77b77a77977876976876776676176075d75c75b75a75575475175074f74e74974874774674474373d73c73773673373273172f72e72d72b72a72472371e71d71a7197187167006ff6fe6fd6fc6fb6f16f06ef6ee6ed6ec6c16c06be6bd6b76b66b16b06ad6ac6ab6a969369269169068f68e68468368268168067f63f63e63d63c63b63a63062f62e62d62c62b5b85b75b55b45ae5ad5a85a75a45a35a25a058a58958858758658557b57a5795785775765365355345335325315275265255245235224af4ae4ac4ab4a54a449f49e49b49a49949748148047f47e47d47c47247147046f46e46d42d42c42b42a42942841e41d41c41b41a41939139038f38e38d38c38238138037f37e37d30a3093073063002ff2fa2f92f62f52f42f22dc2db2da2d92d82d72cd2cc2cb2ca2c92c82882872862852842832792782772762752741ec1eb1ea1e91e81e71dd1dc1db1da1d91d815014f14e14d14c14b14114013f13e13d13c08107f07b07105d04902b
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
def ridgeSupport832_rest_015 : Nat := PackedRawNatGrowth.drop 5556 ridgeSupport832_code
def ridgeSupport832_suffix_015 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 463 ridgeSupport832_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
