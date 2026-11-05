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
def ridgeSupport896_000 : List Nat := [30,60,80,100,110,114,115,323,324,325,326,327,328,338,339,340,341,342,343,411,412,413,414,415,416,426,427,428,429,430,431,495]
def ridgeSupport896_001 : List Nat := [496,497,498,499,500,510,511,512,513,514,515,517,518,519,520,521,522,532,533,535,536,538,539,676,677,678,679,680,681,691,692,693]
def ridgeSupport896_002 : List Nat := [694,695,696,832,833,834,835,836,837,847,848,849,850,851,852,916,917,918,919,920,921,931,932,933,934,935,936,938,939,940,941,942]
def ridgeSupport896_003 : List Nat := [943,953,954,956,957,959,960,1097,1098,1099,1100,1101,1102,1112,1113,1114,1115,1116,1117,1181,1182,1183,1184,1185,1186,1196,1197,1198,1199,1200,1201,1203]
def ridgeSupport896_004 : List Nat := [1204,1205,1206,1207,1208,1218,1219,1221,1222,1224,1225,1362,1363,1364,1365,1366,1367,1377,1378,1379,1380,1381,1382,1446,1447,1448,1449,1450,1451,1461,1462,1463]
def ridgeSupport896_005 : List Nat := [1464,1465,1466,1468,1469,1470,1471,1472,1473,1483,1484,1486,1487,1489,1490,1555,1556,1557,1558,1559,1560,1570,1571,1572,1573,1574,1575,1577,1578,1579,1580,1581]
def ridgeSupport896_006 : List Nat := [1582,1592,1593,1595,1596,1598,1599,1602,1603,1604,1605,1606,1607,1617,1618,1620,1621,1623,1624,1626,1627,1628,1629,1630,1631,1662,1663,1664,1665,1666,1667,1698]
def ridgeSupport896_007 : List Nat := [1699,1700,1701,1702,1703,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1794,1795,1796,1797,1798,1799,1848,1849,1850,1851,1852,1853,1854,1855,1856]
def ridgeSupport896_008 : List Nat := [1857,1858,1859,1890,1891,1892,1893,1894,1895,1950,1951,1952,1953,1954,1955,1986,1987,1988,1989,1990,1991,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050]
def ridgeSupport896_009 : List Nat := [2051,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2160,2161,2162,2163,2164,2165,2184,2185,2186,2187,2188,2189,2196,2197,2199,2201,2202,2203,2205]
def ridgeSupport896_010 : List Nat := [2207,2208,2209,2211,2213,2244,2245,2247,2249,2250,2251,2253,2255,2256,2257,2259,2261,2292,2293,2295,2297,2298,2299,2301,2303,2304,2305,2307,2309,2412,2413,2415]
def ridgeSupport896_011 : List Nat := [2417,2418,2419,2421,2423,2424,2425,2427,2429,2460,2461,2463,2465,2466,2467,2469,2471,2472,2473,2475,2477,2580,2581,2583,2585,2586,2587,2589,2591,2592,2593,2595]
def ridgeSupport896_012 : List Nat := [2597,2628,2629,2631,2633,2634,2635,2637,2639,2640,2641,2643,2645,2676,2677,2679,2681,2682,2683,2685,2687,2688,2689,2691,2693,2724,2725,2727,2729,2730,2731,2733]
def ridgeSupport896_013 : List Nat := [2735,2736,2737,2739,2741,2844,2845,2847,2849,2850,2851,2853,2855,2856,2857,2859,2861,2964,2965,2967,2969,2970,2971,2973,2975,2976,2977,2979,2981]
def ridgeSupport896_code : Nat := 0xba5ba3ba1ba0b9fb9db9bb9ab99b97b95b94b2db2bb29b28b27b25b23b22b21b1fb1db1cab5ab3ab1ab0aafaadaabaaaaa9aa7aa5aa4a85a83a81a80a7fa7da7ba7aa79a77a75a74a55a53a51a50a4fa4da4ba4aa49a47a45a44a25a23a21a20a1fa1da1ba1aa19a17a15a149ad9ab9a99a89a79a59a39a29a199f99d99c97d97b97997897797597397297196f96d96c9059039019008ff8fd8fb8fa8f98f78f58f48d58d38d18d08cf8cd8cb8ca8c98c78c58c48a58a38a18a089f89d89b89a89989789589488d88c88b88a88988887587487387287187083f83e83d83c83b83a8398388378368358348038028018007ff7fe7fd7fc7fb7fa7f97f87c77c67c57c47c37c27a37a27a17a079f79e76776676576476376274374274174073f73e73d73c73b73a7397387077067057047037026e36e26e16e06df6de6dd6dc6db6da6d96d86a76a66a56a46a36a268368268168067f67e65f65e65d65c65b65a65865765565465265164764664564464364263f63e63c63b63963862e62d62c62b62a6296276266256246236226186176166156146135d25d15cf5ce5cc5cb5c15c05bf5be5bd5bc5ba5b95b85b75b65b55ab5aa5a95a85a75a65665655645635625615575565555545535524c94c84c64c54c34c24b84b74b64b54b44b34b14b04af4ae4ad4ac4a24a14a049f49e49d45d45c45b45a45945844e44d44c44b44a4493c03bf3bd3bc3ba3b93af3ae3ad3ac3ab3aa3a83a73a63a53a43a339939839739639539435435335235135034f3453443433423413402b82b72b62b52b42b32a92a82a72a62a52a421b21a21821721521420a2092082072062052032022012001ff1fe1f41f31f21f11f01ef1af1ae1ad1ac1ab1aa1a019f19e19d19c19b15715615515415315214814714614514414307307206e06405003c01e
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
def ridgeSupport896_rest_014 : Nat := PackedRawNatGrowth.drop 5340 ridgeSupport896_code
def ridgeSupport896_suffix_014 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 445 ridgeSupport896_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
