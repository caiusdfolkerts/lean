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
def ridgeSupport832_000 : List Nat := [29,59,79,99,109,113,115,302,303,304,305,306,307,317,318,319,320,321,322,390,391,392,393,394,395,405,406,407,408,409,410,474]
def ridgeSupport832_001 : List Nat := [475,476,477,478,479,489,490,491,492,493,494,516,518,519,520,523,524,529,530,536,537,539,540,655,656,657,658,659,660,670,671,672]
def ridgeSupport832_002 : List Nat := [673,674,675,811,812,813,814,815,816,826,827,828,829,830,831,895,896,897,898,899,900,910,911,912,913,914,915,937,939,940,941,944]
def ridgeSupport832_003 : List Nat := [945,950,951,957,958,960,961,1076,1077,1078,1079,1080,1081,1091,1092,1093,1094,1095,1096,1160,1161,1162,1163,1164,1165,1175,1176,1177,1178,1179,1180,1202]
def ridgeSupport832_004 : List Nat := [1204,1205,1206,1209,1210,1215,1216,1222,1223,1225,1226,1341,1342,1343,1344,1345,1346,1356,1357,1358,1359,1360,1361,1425,1426,1427,1428,1429,1430,1440,1441,1442]
def ridgeSupport832_005 : List Nat := [1443,1444,1445,1467,1469,1470,1471,1474,1475,1480,1481,1487,1488,1490,1491,1534,1535,1536,1537,1538,1539,1549,1550,1551,1552,1553,1554,1576,1578,1579,1580,1583]
def ridgeSupport832_006 : List Nat := [1584,1589,1590,1596,1597,1599,1600,1601,1603,1604,1605,1608,1609,1614,1615,1621,1622,1624,1625,1632,1633,1634,1635,1636,1637,1668,1669,1670,1671,1672,1673,1704]
def ridgeSupport832_007 : List Nat := [1705,1706,1707,1708,1709,1746,1747,1748,1749,1750,1751,1764,1765,1766,1767,1768,1769,1800,1801,1802,1803,1804,1805,1842,1843,1844,1845,1846,1847,1860,1861,1862]
def ridgeSupport832_008 : List Nat := [1863,1864,1865,1896,1897,1898,1899,1900,1901,1956,1957,1958,1959,1960,1961,1992,1993,1994,1995,1996,1997,2034,2035,2036,2037,2038,2039,2052,2053,2054,2055,2056]
def ridgeSupport832_009 : List Nat := [2057,2094,2095,2096,2097,2098,2099,2112,2113,2114,2115,2116,2117,2154,2155,2156,2157,2158,2159,2178,2179,2180,2181,2182,2183,2190,2191,2193,2195,2203,2204,2205]
def ridgeSupport832_010 : List Nat := [2206,2209,2210,2211,2212,2238,2239,2241,2243,2251,2252,2253,2254,2257,2258,2259,2260,2286,2287,2289,2291,2299,2300,2301,2302,2305,2306,2307,2308,2406,2407,2409]
def ridgeSupport832_011 : List Nat := [2411,2419,2420,2421,2422,2425,2426,2427,2428,2454,2455,2457,2459,2467,2468,2469,2470,2473,2474,2475,2476,2574,2575,2577,2579,2587,2588,2589,2590,2593,2594,2595]
def ridgeSupport832_012 : List Nat := [2596,2622,2623,2625,2627,2635,2636,2637,2638,2641,2642,2643,2644,2670,2671,2673,2675,2683,2684,2685,2686,2689,2690,2691,2692,2718,2719,2721,2723,2731,2732,2733]
def ridgeSupport832_013 : List Nat := [2734,2737,2738,2739,2740,2838,2839,2841,2843,2851,2852,2853,2854,2857,2858,2859,2860,2958,2959,2961,2963,2971,2972,2973,2974,2977,2978,2979,2980]
def ridgeSupport832_code : Nat := 0xba4ba3ba2ba1b9eb9db9cb9bb93b91b8fb8eb2cb2bb2ab29b26b25b24b23b1bb19b17b16ab4ab3ab2ab1aaeaadaacaabaa3aa1a9fa9ea84a83a82a81a7ea7da7ca7ba73a71a6fa6ea54a53a52a51a4ea4da4ca4ba43a41a3fa3ea24a23a22a21a1ea1da1ca1ba13a11a0fa0e9ac9ab9aa9a99a69a59a49a399b99999799697c97b97a97997697597497396b9699679669049039029018fe8fd8fc8fb8f38f18ef8ee8d48d38d28d18ce8cd8cc8cb8c38c18bf8be8a48a38a28a189e89d89c89b89389188f88e88788688588488388286f86e86d86c86b86a84584484384284184083383283183082f82e8098088078068058047f77f67f57f47f37f27cd7cc7cb7ca7c97c87a97a87a77a67a57a476d76c76b76a76976874974874774674574473773673573473373270d70c70b70a7097086e96e86e76e66e56e46d76d66d56d46d36d26ad6ac6ab6aa6a96a868968868768668568466566466366266166065965865665564f64e64964864564464364164063f63d63c63663563062f62c62b62a62861261161060f60e60d6036026016005ff5fe5d35d25d05cf5c95c85c35c25bf5be5bd5bb5a55a45a35a25a15a059659559459359259155155054f54e54d54c54254154053f53e53d4ca4c94c74c64c04bf4ba4b94b64b54b44b249c49b49a49949849748d48c48b48a4894884484474464454444434394384374364354343c13c03be3bd3b73b63b13b03ad3ac3ab3a939339239139038f38e38438338238138037f33f33e33d33c33b33a33032f32e32d32c32b2a32a22a12a029f29e29429329229129028f21c21b21921821221120c20b2082072062041ee1ed1ec1eb1ea1e91df1de1dd1dc1db1da19a19919819719619518b18a18918818718614214114013f13e13d13313213113012f12e07307106d06304f03b01d
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
def ridgeSupport832_rest_014 : Nat := PackedRawNatGrowth.drop 5340 ridgeSupport832_code
def ridgeSupport832_suffix_014 : List Nat := []
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
    (PackedRawNatGrowth.readList 12 445 ridgeSupport832_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
