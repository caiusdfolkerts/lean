module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport70_000 : List Nat := [1,35,39,40,41,116,119,121,124,126,128,131,133,136,138,140,143,145,148,150,610,612,613,616,618,622,624,625,628,630,634,636]
def ridgeSupport70_001 : List Nat := [637,640,642,682,683,685,686,687,688,690,691,693,694,696,697,703,704,706,707,708,709,711,712,714,715,717,718,724,725,727,728,729]
def ridgeSupport70_002 : List Nat := [730,732,733,735,736,738,739,2154,2155,2156,2157,2158,2159,2160,2161,2166,2167,2172,2173,2178,2179,2180,2181,2182,2183,2184,2185,2190,2191,2196,2197,2202]
def ridgeSupport70_003 : List Nat := [2203,2204,2205,2206,2207,2214,2215,2216,2217,2218,2219,2226,2227,2228,2229,2230,2231,2234,2236,2240,2242,2246,2248,2250,2251,2252,2253,2254,2255,2258,2260,2264]
def ridgeSupport70_004 : List Nat := [2266,2270,2272,2274,2275,2276,2277,2278,2279,2304,2305,2310,2311,2316,2317,2328,2329,2334,2335,2340,2341,2352,2353,2355,2357,2358,2359,2361,2363,2364,2365,2367]
def ridgeSupport70_005 : List Nat := [2369,2376,2377,2379,2381,2382,2383,2385,2387,2388,2389,2391,2393,2402,2404,2408,2410,2414,2416,2420,2422,2426,2428,2430,2431,2436,2437,2442,2443,2448,2449,2460]
def ridgeSupport70_006 : List Nat := [2461,2466,2467,2475,2477,2481,2483,2490,2491,2502,2503,2517,2519,2523,2525,2528,2530,2534,2536,2538,2539,2544,2545,2550,2551,2556,2557,2568,2569,2574,2575,2583]
def ridgeSupport70_007 : List Nat := [2585,2589,2591,2598,2599,2610,2611,2625,2627,2631,2633,2636,2638,2642,2644,2646,2647,2652,2653,2658,2659,2664,2665,2676,2677,2682,2683,2691,2693,2697,2699,2706]
def ridgeSupport70_008 : List Nat := [2707,2718,2719,2733,2735,2739,2741,5034,5035,5040,5041,5046,5047,5052,5053,5060,5062,5066,5068,5070,5071,5076,5077,5088,5089,5100,5101,5115,5117,5121,5123,5126]
def ridgeSupport70_009 : List Nat := [5128,5132,5134,5142,5143,5148,5149,5154,5155,5160,5161,5168,5170,5174,5176,5178,5179,5184,5185,5196,5197,5208,5209,5223,5225,5229,5231,5234,5236,5240,5242,5250]
def ridgeSupport70_010 : List Nat := [5251,5256,5257,5262,5263,5268,5269,5276,5278,5282,5284,5286,5287,5292,5293,5304,5305,5316,5317,5331,5333,5337,5339,5342,5344,5348,5350,7650,7651,7652,7653,7654]
def ridgeSupport70_011 : List Nat := [7655,7656,7657,7662,7663,7668,7669,7674,7675,7676,7677,7678,7679,7680,7681,7686,7687,7692,7693,7698,7699,7700,7701,7702,7703,7722,7723,7724,7725,7726,7727,7746]
def ridgeSupport70_012 : List Nat := [7747,7748,7749,7750,7751,7770,7771,7772,7773,7774,7775,7794,7795,7796,7797,7798,7799,7818,7819,7820,7821,7822,7823,7842,7843,7844,7845,7846,7847,7851,7853,7857]
def ridgeSupport70_013 : List Nat := [7859,7863,7865,7908,7909,7920,7921,7929,7931,7935,7937,7944,7945,7956,7957,7980,7981,7992,7993,8001,8003,8007,8009,8016,8017,8028,8029,8052,8053,8064,8065,8073]
def ridgeSupport70_014 : List Nat := [8075,8079,8081,8088,8089,8100,8101,9954,9955,9966,9967,9990,9991,10002,10003,10017,10019,10023,10025,10026,10027,10038,10039,10062,10063,10074,10075,10089,10091,10095,10097,10098]
def ridgeSupport70_015 : List Nat := [10099,10110,10111,10134,10135,10146,10147,10161,10163,10167,10169,11898,11899,11900,11901,11902,11903,11910,11911,11912,11913,11914,11915,11922,11923,11924,11925,11926,11927,11946,11947,11948]
def ridgeSupport70_016 : List Nat := [11949,11950,11951,11970,11971,11972,11973,11974,11975,11979,11981,11985,11987,11991,11993,11994,11995,11996,11997,11998,11999,12003,12005,12009,12011,12015,12017,12021,12022,12024,12025,12027]
def ridgeSupport70_017 : List Nat := [12028,12033,12035,12039,12041,12048,12049,12060,12061,12069,12071,12075,12077,12080,12082,12087,12089,12093,12095,12102,12103,12114,12115,12123,12125,12129,12131,12134,12136,12141,12143,12147]
def ridgeSupport70_018 : List Nat := [12149,12156,12157,12168,12169,12177,12179,12183,12185,12188,12190,13338,13339,13350,13351,13365,13367,13371,13373,13374,13375,13382,13384,13386,13387,13392,13393,13404,13405,13419,13421,13425]
def ridgeSupport70_019 : List Nat := [13427,13428,13429,13436,13438,13440,13441,13446,13447,13458,13459,13473,13475,13479,13481,13482,13483,13490,13492,13494,13495,14430,14431,14432,14433,14434,14435,14445,14447,14451,14453,14457]
def ridgeSupport70_020 : List Nat := [14459,14574,14575,14580,14581,14586,14587,14754,14755,14756,14757,14758,14759]
def ridgeSupport70_code : Nat := 0x39a7e69b9a5e6939a3e68b8fbe3eb8f5e3d38efe3bb87be1e7875e1cf86fe1b7863e18b861e18385fe17b4b7d2db4b4d2cb4abd2ab4a9d29f4a3d287493d24b487d21b481d20347ed1f3475d1d3473d1c746dd1af45dd173451d14344bd12b448d11b43fd0fb43dd0ef437d0d7427d09b41bd06af9ebe72f99be5ef93be46f89be22f7dbdf2f75bdcef6fbdb6f68bd9af63bd86f5dbd6ef53bd4af47bd1af3fbcf6f39bcdef32bcc2f2dbcaef27bc96f1dbc72f11bc42f09bc1ef03bc06efcbbeeef9bbe2ef6bbd6ef1bbbeeebbba6ee5bb8eedfbb7aeddbb72edbbb6aed9bb5eed3bb46ecdbb2eec7bb1aec5bb12ec3bb0aeafbabaeadbab2eabbaaae97ba5ae95ba52e93ba4ae8bba2ae89ba22e87ba1ae7fb9fae7db9f2e7bb9ea7b99ede7b39ec67a39e8a7979e5a77f9dfa7739dca7719dbe76b9da675b9d6a74f9d3a7379cda72b9caa7299c9e7239c867139c4a7079c1a6ef9bba6e39b89fa57e91f997e61f917e3df8b7e25f817e01f757dd1f5d7d71f517d41f497d1df437d05f397ce1f2d7cb1f157c51f097c21f017bfdefb7be5ef17bc1ee57b91eb97addeb37ac5ead7aadea77a99ea57a91ea37a89e8f7a39e8d7a31e8b7a29e7779d9e7579d1e7379c9e5f7979e5d7971e5b7969e477919e457911e437909e2f78b9e2d78b1e2b78a9e177859e157851e137849e0d7831e077819e017801dff77f9dfd77f1dfb77e9df577d1def77b9de977a1de77799de57791de377894e653914e053794db53654d5534d4c553114b952e14ad52b14a752994a4528949e5271495525148f52394895221483520947a51e147451c946f51b5469519d459516144d5131441510143b50e943850d943250c142950a1423508941d5071417505940e5031408501940350053fd4fed3ed4fb13e14f813d54f513cf4f393cc4f293c64f113bd4ef13b74ed93b14ec13ab4ea8ab52accaaf2ab4a9f2a78a932a48a8b2a24a852a0ca7b29e8a7529d0a6929a0a632988a5d2970a572958a542948a4e2930a49291ca432904a3328c8a272898a1f2874a19285ca0f2838a0928209fd27f09f727d89f127c09eb27a89e827989e227809dd276c9d727549c727189bb26e89b326c49ad26ac9a3268899d2670991264098b2628985261097f25f897c25e897625d097025b896a25a09642588959255c9552550953254494f253894d252c949252094124fc93d24f093b24e493724d893524cc93124c0925249091f2478919246090d2430907241890124008e723988e523908e323888e023788da23608d423488cf23388cd23308cb23288c823188c223008bc22e88b722d88b522d08b322c88ab22a88a922a08a7229889f227889d227089b2268895225088f2238889222088722188852210883220887d21f087721d887121c086f21b886d21b086b21a82e30b882e00b7c2dd0b702da0b642d80b5c2d50b502ce0b342cb0b282c80b1c2c50b102c30b082c00afc2b90ae02b60ad42b30ac82b00abc2ae0ab42ab0aa82820a0027d09f027a09d827409c427009b826a09a026509902620258094024408f023008a0220085020c08001f807c01e407701d002900a0027008c001
def ridgeSupport70_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport70_code
def ridgeSupport70_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport70_code
def ridgeSupport70_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport70_code
def ridgeSupport70_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport70_code
def ridgeSupport70_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport70_code
def ridgeSupport70_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport70_code
def ridgeSupport70_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport70_code
def ridgeSupport70_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport70_code
def ridgeSupport70_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport70_code
def ridgeSupport70_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport70_code
def ridgeSupport70_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport70_code
def ridgeSupport70_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport70_code
def ridgeSupport70_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport70_code
def ridgeSupport70_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport70_code
def ridgeSupport70_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport70_code
def ridgeSupport70_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport70_code
def ridgeSupport70_rest_016 : Nat := PackedRawNatGrowth.drop 7168 ridgeSupport70_code
def ridgeSupport70_rest_017 : Nat := PackedRawNatGrowth.drop 7616 ridgeSupport70_code
def ridgeSupport70_rest_018 : Nat := PackedRawNatGrowth.drop 8064 ridgeSupport70_code
def ridgeSupport70_rest_019 : Nat := PackedRawNatGrowth.drop 8512 ridgeSupport70_code
def ridgeSupport70_rest_020 : Nat := PackedRawNatGrowth.drop 8960 ridgeSupport70_code
def ridgeSupport70_rest_021 : Nat := PackedRawNatGrowth.drop 9142 ridgeSupport70_code
def ridgeSupport70_suffix_021 : List Nat := []
def ridgeSupport70_suffix_020 : List Nat := ridgeSupport70_020 ++ ridgeSupport70_suffix_021
def ridgeSupport70_suffix_019 : List Nat := ridgeSupport70_019 ++ ridgeSupport70_suffix_020
def ridgeSupport70_suffix_018 : List Nat := ridgeSupport70_018 ++ ridgeSupport70_suffix_019
def ridgeSupport70_suffix_017 : List Nat := ridgeSupport70_017 ++ ridgeSupport70_suffix_018
def ridgeSupport70_suffix_016 : List Nat := ridgeSupport70_016 ++ ridgeSupport70_suffix_017
def ridgeSupport70_suffix_015 : List Nat := ridgeSupport70_015 ++ ridgeSupport70_suffix_016
def ridgeSupport70_suffix_014 : List Nat := ridgeSupport70_014 ++ ridgeSupport70_suffix_015
def ridgeSupport70_suffix_013 : List Nat := ridgeSupport70_013 ++ ridgeSupport70_suffix_014
def ridgeSupport70_suffix_012 : List Nat := ridgeSupport70_012 ++ ridgeSupport70_suffix_013
def ridgeSupport70_suffix_011 : List Nat := ridgeSupport70_011 ++ ridgeSupport70_suffix_012
def ridgeSupport70_suffix_010 : List Nat := ridgeSupport70_010 ++ ridgeSupport70_suffix_011
def ridgeSupport70_suffix_009 : List Nat := ridgeSupport70_009 ++ ridgeSupport70_suffix_010
def ridgeSupport70_suffix_008 : List Nat := ridgeSupport70_008 ++ ridgeSupport70_suffix_009
def ridgeSupport70_suffix_007 : List Nat := ridgeSupport70_007 ++ ridgeSupport70_suffix_008
def ridgeSupport70_suffix_006 : List Nat := ridgeSupport70_006 ++ ridgeSupport70_suffix_007
def ridgeSupport70_suffix_005 : List Nat := ridgeSupport70_005 ++ ridgeSupport70_suffix_006
def ridgeSupport70_suffix_004 : List Nat := ridgeSupport70_004 ++ ridgeSupport70_suffix_005
def ridgeSupport70_suffix_003 : List Nat := ridgeSupport70_003 ++ ridgeSupport70_suffix_004
def ridgeSupport70_suffix_002 : List Nat := ridgeSupport70_002 ++ ridgeSupport70_suffix_003
def ridgeSupport70_suffix_001 : List Nat := ridgeSupport70_001 ++ ridgeSupport70_suffix_002
def ridgeSupport70_suffix_000 : List Nat := ridgeSupport70_000 ++ ridgeSupport70_suffix_001
theorem ridgeSupport70_source : candidateRows 70 =
    (PackedRawNatGrowth.readList 14 653 ridgeSupport70_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
