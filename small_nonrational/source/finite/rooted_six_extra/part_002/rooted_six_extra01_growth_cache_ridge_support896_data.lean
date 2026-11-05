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
def ridgeSupport896_000 : List Nat := [34,60,90,100,110,114,115,323,324,325,326,327,328,338,339,340,341,342,343,479,480,481,482,483,484,494,495,496,497,498,499,563]
def ridgeSupport896_001 : List Nat := [564,565,566,567,568,578,579,580,581,582,583,585,586,587,588,589,590,600,601,603,604,606,607,744,745,746,747,748,749,759,760,761]
def ridgeSupport896_002 : List Nat := [762,763,764,832,833,834,835,836,837,847,848,849,850,851,852,916,917,918,919,920,921,931,932,933,934,935,936,938,939,940,941,942]
def ridgeSupport896_003 : List Nat := [943,953,954,956,957,959,960,1097,1098,1099,1100,1101,1102,1112,1113,1114,1115,1116,1117,1253,1254,1255,1256,1257,1258,1268,1269,1270,1271,1272,1273,1337]
def ridgeSupport896_004 : List Nat := [1338,1339,1340,1341,1342,1352,1353,1354,1355,1356,1357,1359,1360,1361,1362,1363,1364,1374,1375,1377,1378,1380,1381,1446,1447,1448,1449,1450,1451,1461,1462,1463]
def ridgeSupport896_005 : List Nat := [1464,1465,1466,1468,1469,1470,1471,1472,1473,1483,1484,1486,1487,1489,1490,1555,1556,1557,1558,1559,1560,1570,1571,1572,1573,1574,1575,1577,1578,1579,1580,1581]
def ridgeSupport896_006 : List Nat := [1582,1592,1593,1595,1596,1598,1599,1602,1603,1604,1605,1606,1607,1617,1618,1620,1621,1623,1624,1626,1627,1628,1629,1630,1631,1662,1663,1664,1665,1666,1667,1698]
def ridgeSupport896_007 : List Nat := [1699,1700,1701,1702,1703,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1794,1795,1796,1797,1798,1799,1848,1849,1850,1851,1852,1853,1854,1855,1856]
def ridgeSupport896_008 : List Nat := [1857,1858,1859,1908,1909,1910,1911,1912,1913,1914,1915,1916,1917,1918,1919,1950,1951,1952,1953,1954,1955,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014]
def ridgeSupport896_009 : List Nat := [2015,2046,2047,2048,2049,2050,2051,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2160,2161,2162,2163,2164,2165,2196,2197,2199,2201,2202,2203,2205]
def ridgeSupport896_010 : List Nat := [2207,2208,2209,2211,2213,2244,2245,2247,2249,2250,2251,2253,2255,2256,2257,2259,2261,2292,2293,2295,2297,2298,2299,2301,2303,2304,2305,2307,2309,2412,2413,2415]
def ridgeSupport896_011 : List Nat := [2417,2418,2419,2421,2423,2424,2425,2427,2429,2460,2461,2463,2465,2466,2467,2469,2471,2472,2473,2475,2477,2580,2581,2583,2585,2586,2587,2589,2591,2592,2593,2595]
def ridgeSupport896_012 : List Nat := [2597,2700,2701,2703,2705,2706,2707,2709,2711,2712,2713,2715,2717,2748,2749,2751,2753,2754,2755,2757,2759,2760,2761,2763,2765,2868,2869,2871,2873,2874,2875,2877]
def ridgeSupport896_013 : List Nat := [2879,2880,2881,2883,2885,2916,2917,2919,2921,2922,2923,2925,2927,2928,2929,2931,2933,3036,3037,3039,3041,3042,3043,3045,3047,3048,3049,3051,3053]
def ridgeSupport896_code : Nat := 0xbedbebbe9be8be7be5be3be2be1bdfbddbdcb75b73b71b70b6fb6db6bb6ab69b67b65b64b45b43b41b40b3fb3db3bb3ab39b37b35b34acdacbac9ac8ac7ac5ac3ac2ac1abfabdabca9da9ba99a98a97a95a93a92a91a8fa8da8ca25a23a21a20a1fa1da1ba1aa19a17a15a149ad9ab9a99a89a79a59a39a29a199f99d99c97d97b97997897797597397297196f96d96c9059039019008ff8fd8fb8fa8f98f78f58f48d58d38d18d08cf8cd8cb8ca8c98c78c58c48a58a38a18a089f89d89b89a89989789589487587487387287187083f83e83d83c83b83a8398388378368358348038028018007ff7fe7df7de7dd7dc7db7da7d97d87d77d67d57d47a37a27a17a079f79e77f77e77d77c77b77a77977877777677577474374274174073f73e73d73c73b73a7397387077067057047037026e36e26e16e06df6de6dd6dc6db6da6d96d86a76a66a56a46a36a268368268168067f67e65f65e65d65c65b65a65865765565465265164764664564464364263f63e63c63b63963862e62d62c62b62a6296276266256246236226186176166156146135d25d15cf5ce5cc5cb5c15c05bf5be5bd5bc5ba5b95b85b75b65b55ab5aa5a95a85a75a656556456256155f55e55455355255155054f54d54c54b54a54954853e53d53c53b53a5394f94f84f74f64f54f44ea4e94e84e74e64e545d45c45b45a45945844e44d44c44b44a4493c03bf3bd3bc3ba3b93af3ae3ad3ac3ab3aa3a83a73a63a53a43a339939839739639539435435335235135034f3453443433423413402fc2fb2fa2f92f82f72ed2ec2eb2ea2e92e825f25e25c25b25925824e24d24c24b24a2492472462452442432422382372362352342331f31f21f11f01ef1ee1e41e31e21e11e01df15715615515415315214814714614514414307307206e06405a03c022
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
