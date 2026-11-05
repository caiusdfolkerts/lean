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
def ridgeSupport704_000 : List Nat := [42,72,92,112,122,126,129,295,296,297,298,299,300,310,311,312,313,314,315,451,452,453,454,455,456,466,467,468,469,470,471,607]
def ridgeSupport704_001 : List Nat := [608,609,610,611,612,622,623,624,625,626,627,691,692,693,694,695,696,706,707,708,709,710,711,754,755,757,759,761,763,768,769,771]
def ridgeSupport704_002 : List Nat := [772,776,778,872,873,874,875,876,877,887,888,889,890,891,892,1028,1029,1030,1031,1032,1033,1043,1044,1045,1046,1047,1048,1112,1113,1114,1115,1116]
def ridgeSupport704_003 : List Nat := [1117,1127,1128,1129,1130,1131,1132,1175,1176,1178,1180,1182,1184,1189,1190,1192,1193,1197,1199,1293,1294,1295,1296,1297,1298,1308,1309,1310,1311,1312,1313,1377]
def ridgeSupport704_004 : List Nat := [1378,1379,1380,1381,1382,1392,1393,1394,1395,1396,1397,1440,1441,1443,1445,1447,1449,1454,1455,1457,1458,1462,1464,1558,1559,1560,1561,1562,1563,1573,1574,1575]
def ridgeSupport704_005 : List Nat := [1576,1577,1578,1642,1643,1644,1645,1646,1647,1657,1658,1659,1660,1661,1662,1705,1706,1708,1710,1712,1714,1719,1720,1722,1723,1727,1729,1751,1752,1753,1754,1755]
def ridgeSupport704_006 : List Nat := [1756,1766,1767,1768,1769,1770,1771,1814,1815,1817,1819,1821,1823,1828,1829,1831,1832,1836,1838,1839,1840,1842,1844,1846,1848,1853,1854,1856,1857,1861,1863,1866]
def ridgeSupport704_007 : List Nat := [1867,1870,1871,1874,1875,1878,1879,1882,1883,1886,1887,1890,1891,1894,1895,1898,1899,1906,1907,1908,1909,1910,1911,1926,1927,1930,1931,1934,1935,1938,1939,1942]
def ridgeSupport704_008 : List Nat := [1943,1946,1947,1954,1955,1956,1957,1958,1959,1974,1975,1978,1979,1982,1983,1986,1987,1990,1991,1994,1995,2002,2003,2004,2005,2006,2007,2022,2023,2026,2027,2030]
def ridgeSupport704_009 : List Nat := [2031,2038,2039,2040,2041,2042,2043,2058,2059,2062,2063,2066,2067,2070,2071,2074,2075,2078,2079,2086,2087,2088,2089,2090,2091,2106,2107,2110,2111,2114,2115,2122]
def ridgeSupport704_010 : List Nat := [2123,2124,2125,2126,2127,2142,2143,2146,2147,2150,2151,2158,2159,2160,2161,2162,2163,2182,2183,2184,2185,2186,2187,2212,2213,2214,2215,2216,2217,2248,2249,2250]
def ridgeSupport704_011 : List Nat := [2251,2252,2253,2284,2285,2286,2287,2288,2289,2314,2315,2316,2317,2318,2319,2344,2345,2346,2347,2348,2349,2380,2381,2382,2383,2384,2385,2410,2411,2412,2413,2414]
def ridgeSupport704_012 : List Nat := [2415,2440,2441,2442,2443,2444,2445,2476,2477,2478,2479,2480,2481,2506,2507,2508,2509,2510,2511,2536,2537,2538,2539,2540,2541,2566,2567,2568,2569,2570,2571,2596]
def ridgeSupport704_013 : List Nat := [2597,2598,2599,2600,2601,2632,2633,2634,2635,2636,2637,2662,2663,2664,2665,2666,2667,2692,2693,2694,2695,2696,2697,2722,2723,2724,2725,2726,2727,2752,2753,2754]
def ridgeSupport704_014 : List Nat := [2755,2756,2757,2782,2783,2784,2785,2786,2787,2806,2807,2808,2809,2810,2811]
def ridgeSupport704_code : Nat := 0xafbafaaf9af8af7af6ae3ae2ae1ae0adfadeac5ac4ac3ac2ac1ac0aa7aa6aa5aa4aa3aa2a89a88a87a86a85a84a6ba6aa69a68a67a66a4da4ca4ba4aa49a48a29a28a27a26a25a24a0ba0aa09a08a07a069ed9ec9eb9ea9e99e89cf9ce9cd9cc9cb9ca9b19b09af9ae9ad9ac98d98c98b98a98998896f96e96d96c96b96a95195094f94e94d94c92d92c92b92a92992890f90e90d90c90b90a8f18f08ef8ee8ed8ec8cd8cc8cb8ca8c98c88a98a88a78a68a58a488b88a88988888788687387287187086f86e86786686386285f85e84f84e84d84c84b84a84384283f83e83b83a82b82a82982882782681f81e81b81a81781681381280f80e80b80a7fb7fa7f97f87f77f67ef7ee7eb7ea7e77e67d77d67d57d47d37d27cb7ca7c77c67c37c27bf7be7bb7ba7b77b67a77a67a57a47a37a279b79a79779679379278f78e78b78a78778677777677577477377276b76a76776676376275f75e75b75a75775675375274f74e74b74a74774574174073e73d73873673473273072f72e72c72872772572471f71d71b7197177166eb6ea6e96e86e76e66dc6db6da6d96d86d76c16bf6bb6ba6b86b76b26b06ae6ac6aa6a967e67d67c67b67a67966f66e66d66c66b66a62a62962862762662561b61a6196186176165b85b65b25b15af5ae5a95a75a55a35a15a057557457357257157056656556456356256152152051f51e51d51c51251151050f50e50d4af4ad4a94a84a64a54a049e49c49a49849746c46b46a46946846745d45c45b45a45945841841741641541441340940840740640540437c37b37a37937837736d36c36b36a36936830a3083043033013002fb2f92f72f52f32f22c72c62c52c42c32c22b82b72b62b52b42b327327227127026f26e26426326226126025f1d71d61d51d41d31d21c81c71c61c51c41c313b13a13913813713612c12b12a12912812708107e07a07005c04802a
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
def ridgeSupport704_rest_015 : Nat := PackedRawNatGrowth.drop 5556 ridgeSupport704_code
def ridgeSupport704_suffix_015 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 463 ridgeSupport704_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
