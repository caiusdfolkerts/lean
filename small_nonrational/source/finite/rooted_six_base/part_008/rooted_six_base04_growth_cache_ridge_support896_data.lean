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
def ridgeSupport896_000 : List Nat := [44,74,94,114,124,128,129,337,338,339,340,341,342,352,353,354,355,356,357,493,494,495,496,497,498,508,509,510,511,512,513,649]
def ridgeSupport896_001 : List Nat := [650,651,652,653,654,664,665,666,667,668,669,733,734,735,736,737,738,748,749,750,751,752,753,755,756,757,758,759,760,770,771,773]
def ridgeSupport896_002 : List Nat := [774,776,777,914,915,916,917,918,919,929,930,931,932,933,934,1070,1071,1072,1073,1074,1075,1085,1086,1087,1088,1089,1090,1154,1155,1156,1157,1158]
def ridgeSupport896_003 : List Nat := [1159,1169,1170,1171,1172,1173,1174,1176,1177,1178,1179,1180,1181,1191,1192,1194,1195,1197,1198,1335,1336,1337,1338,1339,1340,1350,1351,1352,1353,1354,1355,1419]
def ridgeSupport896_004 : List Nat := [1420,1421,1422,1423,1424,1434,1435,1436,1437,1438,1439,1441,1442,1443,1444,1445,1446,1456,1457,1459,1460,1462,1463,1600,1601,1602,1603,1604,1605,1615,1616,1617]
def ridgeSupport896_005 : List Nat := [1618,1619,1620,1684,1685,1686,1687,1688,1689,1699,1700,1701,1702,1703,1704,1706,1707,1708,1709,1710,1711,1721,1722,1724,1725,1727,1728,1793,1794,1795,1796,1797]
def ridgeSupport896_006 : List Nat := [1798,1808,1809,1810,1811,1812,1813,1815,1816,1817,1818,1819,1820,1830,1831,1833,1834,1836,1837,1840,1841,1842,1843,1844,1845,1855,1856,1858,1859,1861,1862,1864]
def ridgeSupport896_007 : List Nat := [1865,1866,1867,1868,1869,1876,1877,1878,1879,1880,1881,1888,1889,1890,1891,1892,1893,1918,1919,1920,1921,1922,1923,1924,1925,1926,1927,1928,1929,1936,1937,1938]
def ridgeSupport896_008 : List Nat := [1939,1940,1941,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1984,1985,1986,1987,1988,1989,2014,2015,2016,2017,2018,2019,2020,2021,2022,2023,2024]
def ridgeSupport896_009 : List Nat := [2025,2050,2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2068,2069,2070,2071,2072,2073,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2134]
def ridgeSupport896_010 : List Nat := [2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2170,2171,2172,2173,2174,2175,2194,2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2236,2237,2238]
def ridgeSupport896_011 : List Nat := [2239,2240,2241,2272,2273,2274,2275,2276,2277,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2368,2369,2370,2371,2372,2373,2422,2423,2424,2425,2426]
def ridgeSupport896_012 : List Nat := [2427,2428,2429,2430,2431,2432,2433,2464,2465,2466,2467,2468,2469,2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2578,2579,2580,2581,2582,2583,2584]
def ridgeSupport896_013 : List Nat := [2585,2586,2587,2588,2589,2620,2621,2622,2623,2624,2625,2674,2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2734,2735,2736,2737,2738,2739,2740,2741,2742]
def ridgeSupport896_014 : List Nat := [2743,2744,2745,2794,2795,2796,2797,2798,2799,2818,2819,2820,2821,2822,2823]
def ridgeSupport896_code : Nat := 0xb07b06b05b04b03b02aefaeeaedaecaebaeaab9ab8ab7ab6ab5ab4ab3ab2ab1ab0aafaaea7da7ca7ba7aa79a78a77a76a75a74a73a72a41a40a3fa3ea3da3ca1da1ca1ba1aa19a18a17a16a15a14a13a129e19e09df9de9dd9dc9db9da9d99d89d79d69a59a49a39a29a19a098198097f97e97d97c97b97a97997897797694594494394294194092192091f91e91d91c91b91a9199189179168e58e48e38e28e18e08c18c08bf8be8bd8bc89d89c89b89a89989889789689589489389287f87e87d87c87b87a86186085f85e85d85c85b85a85985885785683d83c83b83a83983883783683583483383281981881781681581480d80c80b80a8098088078068058048038027e97e87e77e67e57e47e37e27e17e07df7de7c57c47c37c27c17c07b97b87b77b67b57b47b37b27b17b07af7ae79579479379279179078978878778678578478378278178077f77e76576476376276176075975875775675575474d74c74b74a74974874674574374274073f73573473373273173072d72c72a72972772671c71b71a7197187177157147137127117107067057047037027016c06bf6bd6bc6ba6b96af6ae6ad6ac6ab6aa6a86a76a66a56a46a369969869769669569465465365265165064f6456446436426416405b75b65b45b35b15b05a65a55a45a35a25a159f59e59d59c59b59a59058f58e58d58c58b54b54a54954854754653c53b53a5395385374ae4ad4ab4aa4a84a749d49c49b49a49949849649549449349249148748648548448348244244144043f43e43d43343243143042f42e3a63a53a43a33a23a13973963953943933923093083063053033022f82f72f62f52f42f32f12f02ef2ee2ed2ec2e22e12e02df2de2dd29d29c29b29a29929828e28d28c28b28a2892012001ff1fe1fd1fc1f21f11f01ef1ee1ed16516416316216116015615515415315215108108007c07205e04a02c
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
def ridgeSupport896_rest_015 : Nat := PackedRawNatGrowth.drop 5556 ridgeSupport896_code
def ridgeSupport896_suffix_015 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 463 ridgeSupport896_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase04
