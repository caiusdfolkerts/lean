module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport960_000 : List Nat := [512,513,514,865,866,867,974,975,976,1239,1240,1241,1348,1349,1350,1373,1374,1375,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497]
def ridgeSupport960_001 : List Nat := [1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529]
def ridgeSupport960_002 : List Nat := [1530,1531,1724,1725,1726,1727,1728,1729,1730,1731,1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753]
def ridgeSupport960_003 : List Nat := [1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,1764,1765,1766,1767,1768,1769,1770,1771,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977]
def ridgeSupport960_004 : List Nat := [1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009]
def ridgeSupport960_005 : List Nat := [2010,2011,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519,2520,2521]
def ridgeSupport960_006 : List Nat := [2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2537,2538,2539,2732,2733,2734,2735,2736,2737,2738,2739,2740,2741,2742,2743,2744,2745]
def ridgeSupport960_007 : List Nat := [2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757,2758,2759,2760,2761,2762,2763,2764,2765,2766,2767,2768,2769,2770,2771,2772,2773,2774,2775,2776,2777]
def ridgeSupport960_008 : List Nat := [2778,2779,3260,3261,3262,3263,3264,3265,3266,3267,3268,3269,3270,3271,3272,3273,3274,3275,3276,3277,3278,3279,3280,3281,3282,3283,3284,3285,3286,3287,3288,3289]
def ridgeSupport960_009 : List Nat := [3290,3291,3292,3293,3294,3295,3296,3297,3298,3299,3300,3301,3302,3303,3304,3305,3306,3307,3500,3501,3502,3503,3504,3505,3506,3507,3508,3509,3510,3511,3512,3513]
def ridgeSupport960_010 : List Nat := [3514,3515,3516,3517,3518,3519,3520,3521,3522,3523,3524,3525,3526,3527,3528,3529,3530,3531,3532,3533,3534,3535,3536,3537,3538,3539,3540,3541,3542,3543,3544,3545]
def ridgeSupport960_011 : List Nat := [3546,3547,3836,3837,3838,3839,3840,3841,3842,3843,3844,3845,3846,3847,3848,3849,3850,3851,3852,3853,3854,3855,3856,3857,3858,3859,3860,3861,3862,3863,3864,3865]
def ridgeSupport960_012 : List Nat := [3866,3867,3868,3869,3870,3871,3872,3873,3874,3875,3876,3877,3878,3879,3880,3881,3882,3883,4076,4077,4078,4079,4080,4081,4082,4083,4084,4085,4086,4087,4088,4089]
def ridgeSupport960_013 : List Nat := [4090,4091,4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,4106,4107,4108,4109,4110,4111,4112,4113,4114,4115,4116,4117,4118,4119,4120,4121]
def ridgeSupport960_014 : List Nat := [4122,4123,4604,4605,4606,4607,4608,4609,4610,4611,4612,4613,4614,4615,4616,4617,4618,4619,4620,4621,4622,4623,4624,4625,4626,4627,4628,4629,4630,4631,4632,4633]
def ridgeSupport960_015 : List Nat := [4634,4635,4636,4637,4638,4639,4640,4641,4642,4643,4644,4645,4646,4647,4648,4649,4650,4651,5372,5373,5374,5375,5376,5377,5378,5379,5380,5381,5382,5383,5408,5409]
def ridgeSupport960_016 : List Nat := [5410,5411,5412,5413,5414,5415,5416,5417,5418,5419,5444,5445,5446,5447,5448,5449,5450,5451,5452,5453,5454,5455,5504,5505,5506,5507,5508,5509,5510,5511,5512,5513]
def ridgeSupport960_017 : List Nat := [5514,5515,5540,5541,5542,5543,5544,5545,5546,5547,5548,5549,5550,5551,5600,5601,5602,5603,5604,5605,5606,5607,5608,5609,5610,5611,5636,5637,5638,5639,5640,5641]
def ridgeSupport960_018 : List Nat := [5642,5643,5644,5645,5646,5647,5696,5697,5698,5699,5700,5701,5702,5703,5704,5705,5706,5707,5732,5733,5734,5735,5736,5737,5738,5739,5740,5741,5742,5743,5792,5793]
def ridgeSupport960_019 : List Nat := [5794,5795,5796,5797,5798,5799,5800,5801,5802,5803]
def ridgeSupport960_code : Nat := 0x2d576aab54daa2d4f6a6b52da92d476a2b50da82cdf66eb36d9b2cd766ab34d9a2ccf666b32d992c9764ab24d922c8f646b22d912c87642b20d902c1f60eb06d832c1760ab04d822c0f606b02d812bd75eaaf4d7a2bcf5e6af2d792bc75e2af0d782b5f5aead6d6b2b575aaad4d6a2b4f5a6ad2d692b1758aac4d622b0f586ac2d612b07582ac0d602a9f54eaa6d532a9754aaa4d522a8f546aa2d512a5752aa94d4a2a4f526a92d492a47522a90d482a0f506a82d412a07502a80d4029ff4fea7ed3f245722a914c8a244f226912c892447222910c88243f21e90ec87243721a90cc86242f21690ac852427212908c84241f20e906c83241720a904c82240f206902c812407202900c8023ff1fe8fec7f203701a80cc06202f01680ac052027012808c04201f00e806c03201700a804c02200f006802c012007002800c001ffeffe7febff1ff6ffa7fcbfe1feeff67fabfd1fe6ff27f8bfc1fdefee7f6bfb1e56f2a794bca1e4ef26792bc91e46f22790bc81e3ef1e78ebc71e36f1a78cbc61e2ef1678abc51e26f12788bc41e1ef0e786bc31e16f0a784bc21e0ef06782bc11e06f02780bc01dfeefe77ebbf1bb6dda6ecb761baedd66eab751ba6dd26e8b741b9edce6e6b731b96dca6e4b721b8edc66e2b711b86dc26e0b701b7edbe6deb6f1b76dba6dcb6e1b6edb66dab6d1b66db26d8b6c1b5edae6d6b6b19d6cea674b3a19cece6672b3919c6ce2670b3819becde66eb3719b6cda66cb3619aecd666ab3519a6cd2668b34199ecce666b331996cca664b32198ecc6662b311986cc2660b30197ecbe65eb2f15b6ada56cab615aead656aab515a6ad2568ab4159eace566ab31596aca564ab2158eac6562ab11586ac2560ab0157eabe55eaaf1576aba55caae156eab655aaad1566ab2558aac155eaae556aab13d69ea4f4a7a13ce9e64f2a7913c69e24f0a7813be9de4eea7713b69da4eca7613ae9d64eaa7513a69d24e8a74139e9ce4e6a7313969ca4e4a72138e9c64e2a7113869c24e0a70137e9be4dea6f0fb67da3ec9f60fae7d63ea9f50fa67d23e89f40f9e7ce3e69f30f967ca3e49f20f8e7c63e29f10f867c23e09f00f7e7be3de9ef0f767ba3dc9ee0f6e7b63da9ed0f667b23d89ec0f5e7ae3d69eb0dd66ea3749ba0dce6e63729b90dc66e23709b80dbe6de36e9b70db66da36c9b60dae6d636a9b50da66d23689b40d9e6ce3669b30d966ca3649b20d8e6c63629b10d866c23609b00d7e6be35e9af0bf65fa2fc97e0bee5f62fa97d0be65f22f897c0bde5ee2f697b0bd65ea2f497a0bce5e62f29790bc65e22f09780bbe5de2ee9770bb65da2ec9760bae5d62ea9750ba65d22e89740b9e5ce2e69730abe55e2ae9518a8a54426c93609ae3d01e78f386c63621b08808402200
def ridgeSupport960_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport960_code
def ridgeSupport960_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport960_code
def ridgeSupport960_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport960_code
def ridgeSupport960_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport960_code
def ridgeSupport960_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport960_code
def ridgeSupport960_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport960_code
def ridgeSupport960_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport960_code
def ridgeSupport960_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport960_code
def ridgeSupport960_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport960_code
def ridgeSupport960_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport960_code
def ridgeSupport960_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport960_code
def ridgeSupport960_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport960_code
def ridgeSupport960_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport960_code
def ridgeSupport960_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport960_code
def ridgeSupport960_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport960_code
def ridgeSupport960_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport960_code
def ridgeSupport960_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport960_code
def ridgeSupport960_rest_017 : Nat := PackedRawNatGrowth.drop 7072 ridgeSupport960_code
def ridgeSupport960_rest_018 : Nat := PackedRawNatGrowth.drop 7488 ridgeSupport960_code
def ridgeSupport960_rest_019 : Nat := PackedRawNatGrowth.drop 7904 ridgeSupport960_code
def ridgeSupport960_rest_020 : Nat := PackedRawNatGrowth.drop 8034 ridgeSupport960_code
def ridgeSupport960_suffix_020 : List Nat := []
def ridgeSupport960_suffix_019 : List Nat := ridgeSupport960_019 ++ ridgeSupport960_suffix_020
def ridgeSupport960_suffix_018 : List Nat := ridgeSupport960_018 ++ ridgeSupport960_suffix_019
def ridgeSupport960_suffix_017 : List Nat := ridgeSupport960_017 ++ ridgeSupport960_suffix_018
def ridgeSupport960_suffix_016 : List Nat := ridgeSupport960_016 ++ ridgeSupport960_suffix_017
def ridgeSupport960_suffix_015 : List Nat := ridgeSupport960_015 ++ ridgeSupport960_suffix_016
def ridgeSupport960_suffix_014 : List Nat := ridgeSupport960_014 ++ ridgeSupport960_suffix_015
def ridgeSupport960_suffix_013 : List Nat := ridgeSupport960_013 ++ ridgeSupport960_suffix_014
def ridgeSupport960_suffix_012 : List Nat := ridgeSupport960_012 ++ ridgeSupport960_suffix_013
def ridgeSupport960_suffix_011 : List Nat := ridgeSupport960_011 ++ ridgeSupport960_suffix_012
def ridgeSupport960_suffix_010 : List Nat := ridgeSupport960_010 ++ ridgeSupport960_suffix_011
def ridgeSupport960_suffix_009 : List Nat := ridgeSupport960_009 ++ ridgeSupport960_suffix_010
def ridgeSupport960_suffix_008 : List Nat := ridgeSupport960_008 ++ ridgeSupport960_suffix_009
def ridgeSupport960_suffix_007 : List Nat := ridgeSupport960_007 ++ ridgeSupport960_suffix_008
def ridgeSupport960_suffix_006 : List Nat := ridgeSupport960_006 ++ ridgeSupport960_suffix_007
def ridgeSupport960_suffix_005 : List Nat := ridgeSupport960_005 ++ ridgeSupport960_suffix_006
def ridgeSupport960_suffix_004 : List Nat := ridgeSupport960_004 ++ ridgeSupport960_suffix_005
def ridgeSupport960_suffix_003 : List Nat := ridgeSupport960_003 ++ ridgeSupport960_suffix_004
def ridgeSupport960_suffix_002 : List Nat := ridgeSupport960_002 ++ ridgeSupport960_suffix_003
def ridgeSupport960_suffix_001 : List Nat := ridgeSupport960_001 ++ ridgeSupport960_suffix_002
def ridgeSupport960_suffix_000 : List Nat := ridgeSupport960_000 ++ ridgeSupport960_suffix_001
theorem ridgeSupport960_source : candidateSupports 960 =
    (PackedRawNatGrowth.readList 13 618 ridgeSupport960_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
