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
def ridgeSupport194_000 : List Nat := [9,35,45,51,57,58,116,117,120,121,124,125,188,189,192,193,196,197,260,261,265,267,268,272,274,275,277,281,282,286,288,289]
def ridgeSupport194_001 : List Nat := [293,295,296,298,543,544,545,546,547,548,615,616,617,620,621,622,624,629,631,636,637,638,641,642,643,645,650,652,699,700,701,702]
def ridgeSupport194_002 : List Nat := [703,704,771,772,773,776,777,778,780,785,787,792,793,794,797,798,799,801,806,808,855,856,857,860,861,862,864,869,871,876,877,878]
def ridgeSupport194_003 : List Nat := [881,882,883,885,890,892,939,940,942,943,944,945,947,948,950,951,953,954,1629,1631,1633,1635,1653,1655,1659,1661,1666,1667,1672,1673,1674,1675]
def ridgeSupport194_004 : List Nat := [1680,1681,1714,1715,1720,1721,1722,1723,1728,1729,1735,1737,1741,1743,1753,1754,1756,1757,1905,1907,1909,1911,1914,1915,1920,1921,1941,1943,1947,1949,1954,1955]
def ridgeSupport194_005 : List Nat := [1960,1961,1962,1963,1968,1969,1975,1977,1981,1983,2002,2003,2008,2009,2010,2011,2013,2014,2023,2025,2032,2033,2050,2051,2053,2055,2068,2069,2070,2072,2077,2079]
def ridgeSupport194_006 : List Nat := [2086,2087,2104,2105,2107,2109,2122,2123,2124,2126,2385,2387,2389,2391,2394,2395,2400,2401,2421,2423,2427,2429,2434,2435,2440,2441,2442,2443,2448,2449,2455,2457]
def ridgeSupport194_007 : List Nat := [2461,2463,2482,2483,2488,2489,2490,2491,2493,2494,2503,2505,2512,2513,2530,2531,2533,2535,2548,2549,2550,2552,2557,2559,2566,2567,2584,2585,2587,2589,2602,2603]
def ridgeSupport194_008 : List Nat := [2604,2606,3021,3023,3025,3027,3030,3031,3036,3037,3057,3059,3063,3065,3070,3071,3076,3077,3078,3079,3084,3085,3091,3093,3097,3099,3118,3119,3124,3125,3126,3127]
def ridgeSupport194_009 : List Nat := [3129,3130,3283,3285,3292,3293,3295,3297,3304,3305,3306,3308,3312,3314,3337,3339,3346,3347,3349,3351,3358,3359,3360,3362,3366,3368,3631,3633,3640,3641,3643,3645]
def ridgeSupport194_010 : List Nat := [3652,3653,3654,3656,3660,3662,3685,3687,3694,3695,3697,3699,3706,3707,3708,3710,3714,3716,4401,4403,4405,4407,4424,4426,4428,4430,4435,4437,4441,4443,4472,4474]
def ridgeSupport194_011 : List Nat := [4476,4478,4483,4485,4489,4491,4532,4534,4536,4538,4554,4556,4560,4562,4590,4592,4596,4598,4708,4709,4770,4771,4866,4867,5022,5023]
def ridgeSupport194_code : Nat := 0x273f39e981cc0a5472a2932c9923ed1f48f847ba3a51d08e6472a3751b88db46d23171898c2c60e2fd17c8bd45e22b71598aac54e29d14c8a5452226f135899c4c5d08e8273f39f1cf6e7a739b9c5cdee6e733b995c9ce4c7243919c8ae4471eb8edc72e38718b8bda50d266913481a3ed1e68bb455a26d12685b4259e4cf067633a99d2ce8670b37d9bacdc66ab34d874c3961bb0d986ac34617b0b9836c1960ab04d81ac0c603b01980ac045ffaff97f2bf75f9afc57babdc5ebaf597a6bd15e7af3545ca2c515a8a943aa1b50ca86140ea064ffa7f53f09f64faa7d13ce9e54f1a7893a29d04e4a71d37c9bd4dda6e93729b84d9a6c933e99d4cca65d3229904c5a6293129884c1a6092fa97b4bba5d52c29604ada5692ae9554a9a54509c84c425a12907a83b41ca0e104e82640fa07503081640aa05100e805401a008fe27f03f49f9cfbc7dd3ed9f68fb27d83e99f48f7e7bd3dc9edcf627b03d59ea8f527a83d19e88f3a79b3cb9e54f027803bd9de8eee7753b99dc4dba6dc36d1b64d9e6cd3649b1cd826c035d9ae8d726b83599ac8d226903459a28d126883419a08cfa67b33b99d4cc666132f99747743b91db8ed87683b31d88ec075e3ae1d60eac6f837a1ba8dcc6e43711b70db46d83671b28d806bc35d1ae0d646b03571940c9864231f18f0c7463431918c0c4c62230c1850c246103051820c0c5802bf15f0af45782bb1460a2850a2831410a044fc27d13e09dc4ea27013709b44d8269134099c448223111088444021f09504a024e125090848023c11a08c84542261120880430216109082841018a0c4060830017a0bc03e81f00f207803a81d007403901980b4046009
def ridgeSupport194_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport194_code
def ridgeSupport194_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport194_code
def ridgeSupport194_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport194_code
def ridgeSupport194_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport194_code
def ridgeSupport194_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport194_code
def ridgeSupport194_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport194_code
def ridgeSupport194_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport194_code
def ridgeSupport194_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport194_code
def ridgeSupport194_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport194_code
def ridgeSupport194_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport194_code
def ridgeSupport194_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport194_code
def ridgeSupport194_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport194_code
def ridgeSupport194_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport194_code
def ridgeSupport194_suffix_012 : List Nat := []
def ridgeSupport194_suffix_011 : List Nat := ridgeSupport194_011 ++ ridgeSupport194_suffix_012
def ridgeSupport194_suffix_010 : List Nat := ridgeSupport194_010 ++ ridgeSupport194_suffix_011
def ridgeSupport194_suffix_009 : List Nat := ridgeSupport194_009 ++ ridgeSupport194_suffix_010
def ridgeSupport194_suffix_008 : List Nat := ridgeSupport194_008 ++ ridgeSupport194_suffix_009
def ridgeSupport194_suffix_007 : List Nat := ridgeSupport194_007 ++ ridgeSupport194_suffix_008
def ridgeSupport194_suffix_006 : List Nat := ridgeSupport194_006 ++ ridgeSupport194_suffix_007
def ridgeSupport194_suffix_005 : List Nat := ridgeSupport194_005 ++ ridgeSupport194_suffix_006
def ridgeSupport194_suffix_004 : List Nat := ridgeSupport194_004 ++ ridgeSupport194_suffix_005
def ridgeSupport194_suffix_003 : List Nat := ridgeSupport194_003 ++ ridgeSupport194_suffix_004
def ridgeSupport194_suffix_002 : List Nat := ridgeSupport194_002 ++ ridgeSupport194_suffix_003
def ridgeSupport194_suffix_001 : List Nat := ridgeSupport194_001 ++ ridgeSupport194_suffix_002
def ridgeSupport194_suffix_000 : List Nat := ridgeSupport194_000 ++ ridgeSupport194_suffix_001
theorem ridgeSupport194_source : candidateSupports 194 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport194_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
