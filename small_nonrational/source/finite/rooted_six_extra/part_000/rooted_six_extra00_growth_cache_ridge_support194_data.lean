module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport194_000 : List Nat := [9,39,49,55,61,62,130,131,134,135,138,139,202,203,206,207,210,211,274,275,279,281,282,286,288,289,291,295,296,300,302,303]
def ridgeSupport194_001 : List Nat := [307,309,310,312,625,626,627,628,629,630,697,698,699,702,703,704,706,711,713,718,719,720,723,724,725,727,732,734,781,782,783,784]
def ridgeSupport194_002 : List Nat := [785,786,853,854,855,858,859,860,862,867,869,874,875,876,879,880,881,883,888,890,937,938,939,942,943,944,946,951,953,958,959,960]
def ridgeSupport194_003 : List Nat := [963,964,965,967,972,974,1021,1022,1024,1025,1026,1027,1029,1030,1032,1033,1035,1036,1877,1879,1883,1885,1936,1937,1942,1943,1963,1965,1969,1971,1976,1977]
def ridgeSupport194_004 : List Nat := [1982,1983,1984,1985,1990,1991,2032,2033,2038,2039,2045,2047,2051,2053,2072,2073,2078,2079,2096,2097,2102,2103,2381,2383,2387,2389,2392,2393,2398,2399,2440,2441]
def ridgeSupport194_005 : List Nat := [2446,2447,2467,2469,2473,2475,2480,2481,2486,2487,2488,2489,2494,2495,2501,2503,2507,2509,2536,2537,2542,2543,2560,2561,2566,2567,2585,2587,2615,2617,2630,2631]
def ridgeSupport194_006 : List Nat := [2648,2649,2657,2659,2687,2689,2702,2703,2720,2721,3149,3151,3155,3157,3160,3161,3166,3167,3208,3209,3214,3215,3235,3237,3241,3243,3248,3249,3254,3255,3256,3257]
def ridgeSupport194_007 : List Nat := [3262,3263,3269,3271,3275,3277,3304,3305,3310,3311,3328,3329,3334,3335,3353,3355,3383,3385,3398,3399,3416,3417,3425,3427,3455,3457,3470,3471,3488,3489,4205,4207]
def ridgeSupport194_008 : List Nat := [4211,4213,4216,4217,4222,4223,4264,4265,4270,4271,4291,4293,4297,4299,4304,4305,4310,4311,4312,4313,4318,4319,4325,4327,4331,4333,4360,4361,4366,4367,4384,4385]
def ridgeSupport194_009 : List Nat := [4390,4391,4661,4663,4673,4675,4706,4707,4718,4719,4733,4735,4745,4747,4778,4779,4790,4791,5189,5191,5201,5203,5234,5235,5246,5247,5261,5263,5273,5275,5306,5307]
def ridgeSupport194_010 : List Nat := [5318,5319,7082,7083,7144,7145,7240,7241,7360,7361,7672,7673,7678,7679,7696,7697,7702,7703,7706,7707,7771,7773,7777,7779,7804,7805,7810,7811,7814,7815,7822,7824]
def ridgeSupport194_011 : List Nat := [7826,7827,7840,7842,7844,7845,7939,7941,7945,7947,7972,7973,7978,7979,7982,7983,7990,7992,7994,7995,8008,8010,8012,8013,8179,8181,8185,8187,8212,8213,8218,8219]
def ridgeSupport194_012 : List Nat := [8222,8223,8284,8286,8288,8289,8302,8304,8306,8307,8404,8406,8408,8409,8422,8424,8426,8427]
def ridgeSupport194_code : Nat := 0x83ae0ea83a20e683660d8835a0d481ce07281c206e8186060817a05c807e01e806e01a80560147fedff97fd5ff37d35f4c7d29f487cedf3a7ce1f367cbdf2e7cadf2a7c95f247c2df097c15f037a95ea47a89ea07a4de927a41e8e7a1de867a0de8279f5e7c798de617975e5b786de1a785de167845e1077fddfe77e5df87305cc07125c486fa5be86eadbaa531d4c652ed4ba526d499523d48d51fd47e51cd472514d451511d4454add2b64aad2aa4a2d28949fd27d49bd26e498d262490d24148dd235449d1264485120443d10e442510843b50eb439d0e5437d0de43650d8435d0d643450d0432d0c943150c342bd0ae42a50a841fd07e41e507841d507341bd06d3684da0363cd8e3604d7f358cd613564d58351cd4634e4d37346cd19341cd063404d0033bccee33a4ce83334ccb331ccc532fccbe32e4cb832dccb632c4cb032acca93294ca3323cc8e3224c88317cc5e3164c583154c53313cc4d2a84aa02a3ca8e2a04a7f298ca612964a58291ca4628e4a37286ca19281ca062804a0027bc9ee27a49e827349cb271c9c526fc9be26e49b826dc9b626c49b026ac9a926949a3263c98e2624988257c95e25649582554953253c94d20dc83620c4830207c81e206481820148031ffc7fd1fdc7f61fc47f01f1c7c61f047c01efc7be1ee47b81ecc7b11eb47ab1e5c7961e447901d7475b1d5c755103040b10244081018405100c40210044000ff83fd0f383cc0f1c3c50f103c30f003bf0ef83b90edc3b20ec03af0eb83ab0ea83a90de83780dcc3710dc036f0db036b0da83650d8c35e0d7035b0d683570d583550c483110c4030f0c3830d0b782dc0b5c2d50b502d30b402cf0b382c90b1c2c20b002bf0af82bb0ae82b909d827509d027309c827104e013604d413304bc12e04b0128049c1230484120047811a0464117044c112034c0d2033c0ce032c0ca022c08a021c086020c08200f803d00dc031009c009
def ridgeSupport194_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport194_code
def ridgeSupport194_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport194_code
def ridgeSupport194_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport194_code
def ridgeSupport194_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport194_code
def ridgeSupport194_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport194_code
def ridgeSupport194_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport194_code
def ridgeSupport194_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport194_code
def ridgeSupport194_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport194_code
def ridgeSupport194_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport194_code
def ridgeSupport194_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport194_code
def ridgeSupport194_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport194_code
def ridgeSupport194_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport194_code
def ridgeSupport194_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport194_code
def ridgeSupport194_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport194_code
def ridgeSupport194_suffix_013 : List Nat := []
def ridgeSupport194_suffix_012 : List Nat := ridgeSupport194_012 ++ ridgeSupport194_suffix_013
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
    (PackedRawNatGrowth.readList 14 402 ridgeSupport194_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
