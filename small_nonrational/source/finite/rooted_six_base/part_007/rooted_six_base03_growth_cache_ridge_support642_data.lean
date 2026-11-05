module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport642_000 : List Nat := [13,39,49,55,58,60,164,165,168,169,172,173,236,237,240,241,244,245,282,283,284,287,288,293,294,299,301,323,325,327,329,331]
def ridgeSupport642_001 : List Nat := [336,337,339,342,591,592,593,594,595,596,634,638,639,640,641,643,644,651,653,677,679,681,682,684,686,687,691,696,747,748,749,750]
def ridgeSupport642_002 : List Nat := [751,752,790,794,795,796,797,799,800,807,809,833,835,837,838,840,842,843,847,852,874,878,879,880,881,883,884,891,893,917,919,921]
def ridgeSupport642_003 : List Nat := [922,924,926,927,931,936,937,939,941,943,944,946,948,949,953,955,960,961,1626,1631,1632,1636,1652,1653,1656,1658,1662,1663,1669,1672,1684,1685]
def ridgeSupport642_004 : List Nat := [1694,1695,1700,1701,1710,1711,1722,1727,1732,1733,1736,1738,1742,1743,1746,1748,1752,1753,1902,1907,1908,1912,1924,1925,1934,1935,1940,1941,1944,1946,1950,1951]
def ridgeSupport642_005 : List Nat := [1957,1960,1962,1967,1972,1973,1976,1978,1982,1983,1988,1989,1998,1999,2014,2015,2019,2021,2078,2080,2082,2083,2100,2101,2108,2110,2118,2119,2127,2129,2184,2189]
def ridgeSupport642_006 : List Nat := [2192,2193,2210,2211,2214,2219,2228,2229,2233,2236,2382,2387,2388,2392,2404,2405,2414,2415,2420,2421,2424,2426,2430,2431,2437,2440,2442,2447,2452,2453,2456,2458]
def ridgeSupport642_007 : List Nat := [2462,2463,2468,2469,2478,2479,2494,2495,2499,2501,2558,2560,2562,2563,2580,2581,2588,2590,2598,2599,2607,2609,2664,2669,2672,2673,2690,2691,2694,2699,2708,2709]
def ridgeSupport642_008 : List Nat := [2713,2716,3018,3023,3024,3028,3040,3041,3050,3051,3056,3057,3060,3062,3066,3067,3073,3076,3078,3083,3088,3089,3092,3094,3098,3099,3104,3105,3114,3115,3130,3131]
def ridgeSupport642_009 : List Nat := [3135,3137,3338,3340,3342,3343,3350,3352,3354,3355,3363,3365,3369,3371,3444,3449,3452,3453,3456,3461,3464,3465,3469,3472,3475,3478,3686,3688,3690,3691,3698,3700]
def ridgeSupport642_010 : List Nat := [3702,3703,3711,3713,3717,3719,3792,3797,3800,3801,3804,3809,3812,3813,3817,3820,3823,3826,4398,4403,4404,4408,4423,4426,4429,4433,4442,4444,4452,4457,4471,4474]
def ridgeSupport642_011 : List Nat := [4477,4481,4490,4492,4500,4505,4531,4534,4537,4541,4563,4565,4573,4576,4599,4601,4609,4612,4700,4701,4778,4779,4874,4875,5030,5031]
def ridgeSupport642_code : Nat := 0x274f3a6985cc2a5572aa92ec9724092018fcc7de3c11dd8eac74e37b1b98db46ce3331948c6462a30317d8bd45de2d31648ae456a2a314d8a5451e271134899c4b9de4eef7763ba5dcaee4770bb71db2ed876abb41d0ee85740b9fdceee7673a39c9cd6e6a7343999b2cd936c83635b12d886c2b601afad7c6bcb5d1a56d29692b48da36d1a68c3459a1ed0e6863429882c3f61db0e9856c2a610b081836c1a60b3051822c10605b019808c015fdafe97ecbf45f8afc17d6bea5f0af817a8bd05e7af29538a9954aaa51516a86541aa094e2a70536a9a1462a2f513a89943ca1c50aa851406a0250027f938a9c34dfa6f935e9ae4d2a69133e99e4cd266132a9944c7a6293109854bfa5f92f49784baa5d12de96e4b2a5912b09544a9a5391788b945aa2d11568a6451a289122890446a2210a284f423a11907c83c41aa0d10468224102078fca7e33ef9f78f9e7ce3e29f10f7e7be3dd1ee0f6a7b43d79ea8f507a53cf9e78f347983ca9e50f1e78e3c29e10ef07743b99db8db26d836a1b48d9e6ce3651b20d8a6c435f9ae8d5e6ae3529a90d3e69e34a9a50d1068533f99f8cf467833a99d0cc866032f99687823c01dd8ee476a3b41d90ec075e3ad1d58ea47503a31cf8e7873839a1cc8e5c72a37d1bd8dd06e63711b80dbc6dc36a1aa0d3c69634a1a40d1868a3431a08ca464e32018f8c7463831b18d0c585e02ef1770bb45d82eb15c0acc55e2ae1560aa85522a71528a345162841418a0450027f13f09e84a825312909444a024f0ab054c2a21500a5852428e1450a184b4256126092848023e11c08d84681ea0f407883c01da0ec05682b01520a8052829007803a01b80c404e00d
def ridgeSupport642_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport642_code
def ridgeSupport642_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport642_code
def ridgeSupport642_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport642_code
def ridgeSupport642_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport642_code
def ridgeSupport642_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport642_code
def ridgeSupport642_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport642_code
def ridgeSupport642_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport642_code
def ridgeSupport642_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport642_code
def ridgeSupport642_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport642_code
def ridgeSupport642_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport642_code
def ridgeSupport642_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport642_code
def ridgeSupport642_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport642_code
def ridgeSupport642_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport642_code
def ridgeSupport642_suffix_012 : List Nat := []
def ridgeSupport642_suffix_011 : List Nat := ridgeSupport642_011 ++ ridgeSupport642_suffix_012
def ridgeSupport642_suffix_010 : List Nat := ridgeSupport642_010 ++ ridgeSupport642_suffix_011
def ridgeSupport642_suffix_009 : List Nat := ridgeSupport642_009 ++ ridgeSupport642_suffix_010
def ridgeSupport642_suffix_008 : List Nat := ridgeSupport642_008 ++ ridgeSupport642_suffix_009
def ridgeSupport642_suffix_007 : List Nat := ridgeSupport642_007 ++ ridgeSupport642_suffix_008
def ridgeSupport642_suffix_006 : List Nat := ridgeSupport642_006 ++ ridgeSupport642_suffix_007
def ridgeSupport642_suffix_005 : List Nat := ridgeSupport642_005 ++ ridgeSupport642_suffix_006
def ridgeSupport642_suffix_004 : List Nat := ridgeSupport642_004 ++ ridgeSupport642_suffix_005
def ridgeSupport642_suffix_003 : List Nat := ridgeSupport642_003 ++ ridgeSupport642_suffix_004
def ridgeSupport642_suffix_002 : List Nat := ridgeSupport642_002 ++ ridgeSupport642_suffix_003
def ridgeSupport642_suffix_001 : List Nat := ridgeSupport642_001 ++ ridgeSupport642_suffix_002
def ridgeSupport642_suffix_000 : List Nat := ridgeSupport642_000 ++ ridgeSupport642_suffix_001
theorem ridgeSupport642_source : candidateSupports 642 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport642_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
