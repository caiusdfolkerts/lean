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
def ridgeSupport770_000 : List Nat := [14,40,50,56,59,60,176,177,180,181,184,185,248,249,252,253,256,257,303,304,305,308,309,314,315,320,322,324,325,326,329,330]
def ridgeSupport770_001 : List Nat := [335,336,341,343,603,604,605,606,607,608,655,659,660,661,662,664,665,672,674,676,680,681,682,683,685,686,693,695,759,760,761,762]
def ridgeSupport770_002 : List Nat := [763,764,811,815,816,817,818,820,821,828,830,832,836,837,838,839,841,842,849,851,895,899,900,901,902,904,905,912,914,916,920,921]
def ridgeSupport770_003 : List Nat := [922,923,925,926,933,935,937,938,942,943,944,945,947,948,956,958,959,961,1628,1630,1632,1634,1650,1651,1656,1657,1662,1664,1668,1670,1690,1691]
def ridgeSupport770_004 : List Nat := [1696,1697,1698,1699,1704,1705,1724,1726,1730,1732,1738,1739,1744,1745,1746,1747,1749,1750,1904,1906,1908,1910,1930,1931,1936,1937,1938,1939,1944,1945,1950,1952]
def ridgeSupport770_005 : List Nat := [1956,1958,1964,1966,1970,1972,1978,1979,1984,1985,1986,1987,1992,1993,2017,2018,2020,2021,2132,2134,2136,2137,2154,2155,2162,2164,2172,2173,2181,2183,2186,2188]
def ridgeSupport770_006 : List Nat := [2190,2191,2208,2209,2216,2218,2226,2227,2235,2237,2384,2386,2388,2390,2410,2411,2416,2417,2418,2419,2424,2425,2430,2432,2436,2438,2444,2446,2450,2452,2458,2459]
def ridgeSupport770_007 : List Nat := [2464,2465,2466,2467,2472,2473,2497,2498,2500,2501,2612,2614,2616,2617,2634,2635,2642,2644,2652,2653,2661,2663,2666,2668,2670,2671,2688,2689,2696,2698,2706,2707]
def ridgeSupport770_008 : List Nat := [2715,2717,3020,3022,3024,3026,3046,3047,3052,3053,3054,3055,3060,3061,3066,3068,3072,3074,3080,3082,3086,3088,3094,3095,3100,3101,3102,3103,3108,3109,3133,3134]
def ridgeSupport770_009 : List Nat := [3136,3137,3392,3394,3396,3397,3404,3406,3408,3409,3417,3419,3423,3425,3446,3448,3450,3451,3458,3460,3462,3463,3471,3473,3477,3479,3740,3742,3744,3745,3752,3754]
def ridgeSupport770_010 : List Nat := [3756,3757,3765,3767,3771,3773,3794,3796,3798,3799,3806,3808,3810,3811,3819,3821,3825,3827,4400,4402,4404,4406,4425,4427,4429,4431,4448,4450,4454,4456,4473,4475]
def ridgeSupport770_011 : List Nat := [4477,4479,4496,4498,4502,4504,4533,4535,4537,4539,4569,4571,4575,4577,4605,4607,4611,4613,4698,4699,4780,4781,4876,4877,5032,5033]
def ridgeSupport770_code : Nat := 0x27533a8986cc3255b2ac92dc96a40b2038ffc7f63c31df8edc7663771b98dbc6d63311968c946422ff17d8bdc5e62d11668b1458229f14d8a5c52626d13489944c1de6ef1776bbaddc6ee27703b79daeed676a3b49d7aebb75bbad5d5aeac7553aa1d42ea074f3a71b2ed956c8b63db0ed866c23609af6d7a6bc35d9ac2d5f6adb565aa2d506a73531a8ad446a13501882c4061f30f584ac2460fb07983ac1c60bb059820c0e6053021804c005fe2fe97eabf45f7afb97dabec5f3af997a4bd05e72f3153aa9b549aa49514a88540aa014dea6e53629a94cea6552ea9714a8a52525a929472a3851b28d138a9c44e127053529a84d1a6893429a04cda6693289924c7263130c9844c025f92f29784b9a5c92e29704b5a5a92ac9544a9254117a8bb459a2c91548a8450a28111e88e446222910e88543ea1f10e8872435a1a90b285842b2150fca7e43f11f84f927c83e19f08f827c03dd9ee8f687b23d71eb0f4c7a43d01e78f327983c99e48f227903c59e28eec7743b91dc0dac6d53699b48da26d03659b28d886c235f1af0d526a83519a88d426a034d9a68d0c68434019f8cf267833999c8cc466032f19707823bf1df0ef07683b31d88ec075e3ae1d50ea474e3a51cf0e7473639a1cc8e607283921c80e247103861c28e1070637f1a98d446943491a38d1868a3441a00cf867833519a0cc86623301978cac5f82fb17d0be45f02f715b8ad455c2ad1558aa85522a81520a8854029914c0a5852a2941498a3c4c025f12f09744b825b0ab85542a014f0a5052428c1450a2050828013b09d04d426813109804bc20210007e83f01f20f805c82e016a0b405882c007803b01c00c805000e
def ridgeSupport770_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport770_code
def ridgeSupport770_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport770_code
def ridgeSupport770_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport770_code
def ridgeSupport770_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport770_code
def ridgeSupport770_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport770_code
def ridgeSupport770_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport770_code
def ridgeSupport770_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport770_code
def ridgeSupport770_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport770_code
def ridgeSupport770_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport770_code
def ridgeSupport770_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport770_code
def ridgeSupport770_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport770_code
def ridgeSupport770_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport770_code
def ridgeSupport770_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport770_code
def ridgeSupport770_suffix_012 : List Nat := []
def ridgeSupport770_suffix_011 : List Nat := ridgeSupport770_011 ++ ridgeSupport770_suffix_012
def ridgeSupport770_suffix_010 : List Nat := ridgeSupport770_010 ++ ridgeSupport770_suffix_011
def ridgeSupport770_suffix_009 : List Nat := ridgeSupport770_009 ++ ridgeSupport770_suffix_010
def ridgeSupport770_suffix_008 : List Nat := ridgeSupport770_008 ++ ridgeSupport770_suffix_009
def ridgeSupport770_suffix_007 : List Nat := ridgeSupport770_007 ++ ridgeSupport770_suffix_008
def ridgeSupport770_suffix_006 : List Nat := ridgeSupport770_006 ++ ridgeSupport770_suffix_007
def ridgeSupport770_suffix_005 : List Nat := ridgeSupport770_005 ++ ridgeSupport770_suffix_006
def ridgeSupport770_suffix_004 : List Nat := ridgeSupport770_004 ++ ridgeSupport770_suffix_005
def ridgeSupport770_suffix_003 : List Nat := ridgeSupport770_003 ++ ridgeSupport770_suffix_004
def ridgeSupport770_suffix_002 : List Nat := ridgeSupport770_002 ++ ridgeSupport770_suffix_003
def ridgeSupport770_suffix_001 : List Nat := ridgeSupport770_001 ++ ridgeSupport770_suffix_002
def ridgeSupport770_suffix_000 : List Nat := ridgeSupport770_000 ++ ridgeSupport770_suffix_001
theorem ridgeSupport770_source : candidateSupports 770 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport770_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
