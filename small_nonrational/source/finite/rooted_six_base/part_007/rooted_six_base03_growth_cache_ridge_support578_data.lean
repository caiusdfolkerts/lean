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
def ridgeSupport578_000 : List Nat := [11,37,47,53,58,59,140,141,144,145,148,149,212,213,216,217,220,221,281,283,285,287,289,294,295,297,300,302,304,306,308,310]
def ridgeSupport578_001 : List Nat := [315,316,318,321,567,568,569,570,571,572,635,637,639,640,642,644,645,649,654,656,658,660,661,663,665,666,670,675,723,724,725,726]
def ridgeSupport578_002 : List Nat := [727,728,791,793,795,796,798,800,801,805,810,812,814,816,817,819,821,822,826,831,875,877,879,880,882,884,885,889,894,896,898,900]
def ridgeSupport578_003 : List Nat := [901,903,905,906,910,915,938,939,941,942,945,946,947,949,950,952,959,960,1626,1628,1635,1637,1650,1652,1658,1659,1664,1665,1671,1673,1678,1679]
def ridgeSupport578_004 : List Nat := [1692,1693,1706,1707,1712,1713,1726,1727,1728,1733,1734,1739,1740,1741,1749,1751,1752,1754,1902,1904,1911,1913,1918,1919,1932,1933,1938,1940,1946,1947,1952,1953]
def ridgeSupport578_005 : List Nat := [1959,1961,1966,1967,1968,1973,1974,1979,1980,1981,1994,1995,2000,2001,2011,2012,2019,2020,2076,2081,2084,2085,2102,2103,2106,2111,2120,2121,2125,2128,2130,2135]
def ridgeSupport578_006 : List Nat := [2138,2139,2156,2157,2160,2165,2174,2175,2179,2182,2382,2384,2391,2393,2398,2399,2412,2413,2418,2420,2426,2427,2432,2433,2439,2441,2446,2447,2448,2453,2454,2459]
def ridgeSupport578_007 : List Nat := [2460,2461,2474,2475,2480,2481,2491,2492,2499,2500,2556,2561,2564,2565,2582,2583,2586,2591,2600,2601,2605,2608,2610,2615,2618,2619,2636,2637,2640,2645,2654,2655]
def ridgeSupport578_008 : List Nat := [2659,2662,3018,3020,3027,3029,3034,3035,3048,3049,3054,3056,3062,3063,3068,3069,3075,3077,3082,3083,3084,3089,3090,3095,3096,3097,3110,3111,3116,3117,3127,3128]
def ridgeSupport578_009 : List Nat := [3135,3136,3336,3341,3344,3345,3348,3353,3356,3357,3361,3364,3367,3370,3390,3395,3398,3399,3402,3407,3410,3411,3415,3418,3421,3424,3684,3689,3692,3693,3696,3701]
def ridgeSupport578_010 : List Nat := [3704,3705,3709,3712,3715,3718,3738,3743,3746,3747,3750,3755,3758,3759,3763,3766,3769,3772,4398,4400,4407,4409,4423,4425,4430,4432,4440,4445,4446,4451,4471,4473]
def ridgeSupport578_011 : List Nat := [4478,4480,4488,4493,4494,4499,4531,4533,4538,4540,4561,4564,4567,4570,4597,4600,4603,4606,4704,4705,4774,4775,4870,4871,5026,5027]
def ridgeSupport578_code : Nat := 0x27473a2983cc1a54f2a6930c9823fd1fb8fc47d63b51d78ea47463791ba8dac6ce32718e8c6c62230117e8bcc5de2c715e8aec5622a114e8a4c51e27313789844b9d78eb975b3acdd5eeae755ba99d46ea274fba69d0ce8374039f5cf2e7873ab9c1cdae6c734b991ac0d5d6ad355daa6d526a7b529a8ed466a1b4f9a54d276923485a3ad1c68cb451a22d10686b421880c3f61c30dd85ac2c613b099832c1860bb049822c0c605b02980ac035feaff17eebf65f82fb97d2be85edaf697aabd35e62f294cca6352fa9794aaa50526a931476a3a51ba8c9460a2d514a8a143ea1a50ba85940aa04500a7f13889c34de26ed3629b04d5a6a933a99c4cda65932a9904c7a6393129874c0a6012f697a4ba25c92da96c4afa5792b29574a8253910c88343fa1f90ea870436a1b10b685a42ba1490a084d424a12107e83a41ba0d904a824410a070fc87e33ee1f6cfa27d03e59f28f7a7bc3dd9ed8f6a7b03d79eb8f527a73d09e80f3679a3ca1e48f1a78c3bf9df8ef27773b81db8db46d836b9b54d9a6cc3659b18d8a6c035f9af8d626b03559aa8d3a69c3479a38d126873409a00cf667a33a19c8cca66332e19687803bf1dc0ed876a3b31d90ec475c3ad1d58ea872638e1c50e2470e3851c20e0870037e1bc8dd46e83721b80dbc6da36b19f8ce866c3351998cc466032e1960ca864a3211900c7863831b18c8c5c5b02d716b0b545a82d31518a7853429914b8a545282921480a385122851420a0850027f13e89ec47823b11d08e44702370a084f827813b09b04d026413009704b0252127093048423e11d08d84641ba0dc06c83601aa0d404a8250122090046823007603a01a80bc04a00b
def ridgeSupport578_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport578_code
def ridgeSupport578_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport578_code
def ridgeSupport578_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport578_code
def ridgeSupport578_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport578_code
def ridgeSupport578_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport578_code
def ridgeSupport578_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport578_code
def ridgeSupport578_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport578_code
def ridgeSupport578_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport578_code
def ridgeSupport578_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport578_code
def ridgeSupport578_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport578_code
def ridgeSupport578_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport578_code
def ridgeSupport578_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport578_code
def ridgeSupport578_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport578_code
def ridgeSupport578_suffix_012 : List Nat := []
def ridgeSupport578_suffix_011 : List Nat := ridgeSupport578_011 ++ ridgeSupport578_suffix_012
def ridgeSupport578_suffix_010 : List Nat := ridgeSupport578_010 ++ ridgeSupport578_suffix_011
def ridgeSupport578_suffix_009 : List Nat := ridgeSupport578_009 ++ ridgeSupport578_suffix_010
def ridgeSupport578_suffix_008 : List Nat := ridgeSupport578_008 ++ ridgeSupport578_suffix_009
def ridgeSupport578_suffix_007 : List Nat := ridgeSupport578_007 ++ ridgeSupport578_suffix_008
def ridgeSupport578_suffix_006 : List Nat := ridgeSupport578_006 ++ ridgeSupport578_suffix_007
def ridgeSupport578_suffix_005 : List Nat := ridgeSupport578_005 ++ ridgeSupport578_suffix_006
def ridgeSupport578_suffix_004 : List Nat := ridgeSupport578_004 ++ ridgeSupport578_suffix_005
def ridgeSupport578_suffix_003 : List Nat := ridgeSupport578_003 ++ ridgeSupport578_suffix_004
def ridgeSupport578_suffix_002 : List Nat := ridgeSupport578_002 ++ ridgeSupport578_suffix_003
def ridgeSupport578_suffix_001 : List Nat := ridgeSupport578_001 ++ ridgeSupport578_suffix_002
def ridgeSupport578_suffix_000 : List Nat := ridgeSupport578_000 ++ ridgeSupport578_suffix_001
theorem ridgeSupport578_source : candidateSupports 578 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport578_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
