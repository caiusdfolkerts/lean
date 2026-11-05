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
def ridgeSupport322_000 : List Nat := [10,36,46,52,57,59,128,129,132,133,136,137,200,201,204,205,208,209,260,262,264,266,268,273,274,276,279,302,303,307,309,310]
def ridgeSupport322_001 : List Nat := [314,316,317,319,555,556,557,558,559,560,614,616,618,619,621,623,624,628,633,657,658,659,662,663,664,666,671,673,711,712,713,714]
def ridgeSupport322_002 : List Nat := [715,716,770,772,774,775,777,779,780,784,789,813,814,815,818,819,820,822,827,829,854,856,858,859,861,863,864,868,873,897,898,899]
def ridgeSupport322_003 : List Nat := [902,903,904,906,911,913,938,940,941,943,944,946,948,949,951,952,956,957,1627,1630,1633,1637,1651,1654,1660,1661,1665,1667,1670,1671,1676,1677]
def ridgeSupport322_004 : List Nat := [1686,1687,1708,1709,1718,1719,1724,1725,1729,1731,1734,1735,1740,1745,1750,1751,1755,1757,1903,1906,1909,1913,1916,1917,1926,1927,1939,1942,1948,1949,1953,1955]
def ridgeSupport322_005 : List Nat := [1958,1959,1964,1965,1969,1971,1974,1975,1980,1985,1996,1997,2006,2007,2010,2012,2016,2017,2022,2027,2030,2031,2048,2049,2052,2057,2066,2067,2071,2074,2131,2133]
def ridgeSupport322_006 : List Nat := [2140,2141,2158,2159,2161,2163,2176,2177,2178,2180,2383,2386,2389,2393,2396,2397,2406,2407,2419,2422,2428,2429,2433,2435,2438,2439,2444,2445,2449,2451,2454,2455]
def ridgeSupport322_007 : List Nat := [2460,2465,2476,2477,2486,2487,2490,2492,2496,2497,2502,2507,2510,2511,2528,2529,2532,2537,2546,2547,2551,2554,2611,2613,2620,2621,2638,2639,2641,2643,2656,2657]
def ridgeSupport322_008 : List Nat := [2658,2660,3019,3022,3025,3029,3032,3033,3042,3043,3055,3058,3064,3065,3069,3071,3074,3075,3080,3081,3085,3087,3090,3091,3096,3101,3112,3113,3122,3123,3126,3128]
def ridgeSupport322_009 : List Nat := [3132,3133,3282,3287,3290,3291,3294,3299,3302,3303,3307,3310,3313,3316,3391,3393,3400,3401,3403,3405,3412,3413,3414,3416,3420,3422,3630,3635,3638,3639,3642,3647]
def ridgeSupport322_010 : List Nat := [3650,3651,3655,3658,3661,3664,3739,3741,3748,3749,3751,3753,3760,3761,3762,3764,3768,3770,4399,4402,4405,4409,4422,4427,4428,4432,4434,4439,4447,4449,4470,4475]
def ridgeSupport322_011 : List Nat := [4476,4480,4482,4487,4495,4497,4530,4535,4536,4540,4555,4558,4566,4568,4591,4594,4602,4604,4706,4707,4772,4773,4868,4869,5024,5025]
def ridgeSupport322_code : Nat := 0x27433a0982cc1254b2a4931c98a3f91fa8f947be3b11d68e7472e3791b88dbc6ca32318f8c3c60a30117c8bdc5da2c315f8abc54a2a114c8a5c51a27313589944bdd74eb875a3ac9d62eb0754ba9dd4aea474eba6dca0e4d725391dc86e4271fb8e9c6ee36719b8b9abcd5c6ac3559aaad546a6b52da92d486a0b4fd9e8cf167733ad9cece6671b3799b6cda66bb34987ac3c61c30d9866c32614b0a183ac18609b04981ec0d604b021806c025ffaff57f2bf85f92fbd7c6be25ecaf617aabd15e72f2d4c8a62530a9814a6a51527a93947aa3c51aa8cd3f49f74f9a7c93d29e44f0a78139e9ce4e5a7193829c04de26e936e9b64d6a6b134299c4cba6593269914c6a63130e9864c1a6052fa97c4bb25cd2ce9664aea5712b29554a9253d108882440a2010e6871437a1b90ba85c42aa14d034817409a049012804400a000fde7ee3f59f98fc27e03ee1f68fae7d63e69f30f827bc3db9ed8f667b13d69eb0f4e7a63d19e84f3a79c3cb1e4cf0e7863be9df0ef27753b91dbcdba6db36b9b58da26cc3639b18d866c135e9af0d6e6b63569ab0d2e6963469a30d0e6863419a04cfa67c33b19cccca66132f196c77a3bc1dc0edc76a3b41d90ec075e3ad1d60ea872238f1c50e2070e3861c18e087023691b20d806be35d1ad8d686b035619e8cec66c3341998cc865e32e1968c5462030c1858c2460e3061820c085982cb1650b245902c71508a7c53429814b8a5852629214889e44e827013789b44d626a134099846022f11708b445822b09f84f427813a09b04d426612f097045c228112088843021410808304101a20d006683301920c8044822010a084040820007603901a00b804800a
def ridgeSupport322_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport322_code
def ridgeSupport322_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport322_code
def ridgeSupport322_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport322_code
def ridgeSupport322_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport322_code
def ridgeSupport322_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport322_code
def ridgeSupport322_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport322_code
def ridgeSupport322_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport322_code
def ridgeSupport322_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport322_code
def ridgeSupport322_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport322_code
def ridgeSupport322_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport322_code
def ridgeSupport322_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport322_code
def ridgeSupport322_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport322_code
def ridgeSupport322_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport322_code
def ridgeSupport322_suffix_012 : List Nat := []
def ridgeSupport322_suffix_011 : List Nat := ridgeSupport322_011 ++ ridgeSupport322_suffix_012
def ridgeSupport322_suffix_010 : List Nat := ridgeSupport322_010 ++ ridgeSupport322_suffix_011
def ridgeSupport322_suffix_009 : List Nat := ridgeSupport322_009 ++ ridgeSupport322_suffix_010
def ridgeSupport322_suffix_008 : List Nat := ridgeSupport322_008 ++ ridgeSupport322_suffix_009
def ridgeSupport322_suffix_007 : List Nat := ridgeSupport322_007 ++ ridgeSupport322_suffix_008
def ridgeSupport322_suffix_006 : List Nat := ridgeSupport322_006 ++ ridgeSupport322_suffix_007
def ridgeSupport322_suffix_005 : List Nat := ridgeSupport322_005 ++ ridgeSupport322_suffix_006
def ridgeSupport322_suffix_004 : List Nat := ridgeSupport322_004 ++ ridgeSupport322_suffix_005
def ridgeSupport322_suffix_003 : List Nat := ridgeSupport322_003 ++ ridgeSupport322_suffix_004
def ridgeSupport322_suffix_002 : List Nat := ridgeSupport322_002 ++ ridgeSupport322_suffix_003
def ridgeSupport322_suffix_001 : List Nat := ridgeSupport322_001 ++ ridgeSupport322_suffix_002
def ridgeSupport322_suffix_000 : List Nat := ridgeSupport322_000 ++ ridgeSupport322_suffix_001
theorem ridgeSupport322_source : candidateSupports 322 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport322_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
