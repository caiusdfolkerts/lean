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
def ridgeSupport960_000 : List Nat := [608,609,610,1029,1030,1031,1450,1451,1452,1715,1716,1717,1824,1825,1826,1849,1850,1851,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973]
def ridgeSupport960_001 : List Nat := [1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005]
def ridgeSupport960_002 : List Nat := [2006,2007,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212,2213,2214,2215,2216,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,2227,2228,2229]
def ridgeSupport960_003 : List Nat := [2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2440,2441,2442,2443,2444,2445,2446,2447,2448,2449,2450,2451,2452,2453]
def ridgeSupport960_004 : List Nat := [2454,2455,2456,2457,2458,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468,2469,2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,2480,2481,2482,2483,2484,2485]
def ridgeSupport960_005 : List Nat := [2486,2487,2968,2969,2970,2971,2972,2973,2974,2975,2976,2977,2978,2979,2980,2981,2982,2983,2984,2985,2986,2987,2988,2989,2990,2991,2992,2993,2994,2995,2996,2997]
def ridgeSupport960_006 : List Nat := [2998,2999,3000,3001,3002,3003,3004,3005,3006,3007,3008,3009,3010,3011,3012,3013,3014,3015,3208,3209,3210,3211,3212,3213,3214,3215,3216,3217,3218,3219,3220,3221]
def ridgeSupport960_007 : List Nat := [3222,3223,3224,3225,3226,3227,3228,3229,3230,3231,3232,3233,3234,3235,3236,3237,3238,3239,3240,3241,3242,3243,3244,3245,3246,3247,3248,3249,3250,3251,3252,3253]
def ridgeSupport960_008 : List Nat := [3254,3255,3736,3737,3738,3739,3740,3741,3742,3743,3744,3745,3746,3747,3748,3749,3750,3751,3752,3753,3754,3755,3756,3757,3758,3759,3760,3761,3762,3763,3764,3765]
def ridgeSupport960_009 : List Nat := [3766,3767,3768,3769,3770,3771,3772,3773,3774,3775,3776,3777,3778,3779,3780,3781,3782,3783,4264,4265,4266,4267,4268,4269,4270,4271,4272,4273,4274,4275,4276,4277]
def ridgeSupport960_010 : List Nat := [4278,4279,4280,4281,4282,4283,4284,4285,4286,4287,4288,4289,4290,4291,4292,4293,4294,4295,4296,4297,4298,4299,4300,4301,4302,4303,4304,4305,4306,4307,4308,4309]
def ridgeSupport960_011 : List Nat := [4310,4311,4504,4505,4506,4507,4508,4509,4510,4511,4512,4513,4514,4515,4516,4517,4518,4519,4520,4521,4522,4523,4524,4525,4526,4527,4528,4529,4530,4531,4532,4533]
def ridgeSupport960_012 : List Nat := [4534,4535,4536,4537,4538,4539,4540,4541,4542,4543,4544,4545,4546,4547,4548,4549,4550,4551,5032,5033,5034,5035,5036,5037,5038,5039,5040,5041,5042,5043,5044,5045]
def ridgeSupport960_013 : List Nat := [5046,5047,5048,5049,5050,5051,5052,5053,5054,5055,5056,5057,5058,5059,5060,5061,5062,5063,5064,5065,5066,5067,5068,5069,5070,5071,5072,5073,5074,5075,5076,5077]
def ridgeSupport960_014 : List Nat := [5078,5079,5560,5561,5562,5563,5564,5565,5566,5567,5568,5569,5570,5571,5572,5573,5574,5575,5576,5577,5578,5579,5580,5581,5582,5583,5584,5585,5586,5587,5588,5589]
def ridgeSupport960_015 : List Nat := [5590,5591,5592,5593,5594,5595,5596,5597,5598,5599,5600,5601,5602,5603,5604,5605,5606,5607,5800,5801,5802,5803,5804,5805,5806,5807,5808,5809,5810,5811,5812,5813]
def ridgeSupport960_016 : List Nat := [5814,5815,5816,5817,5818,5819,5820,5821,5822,5823,5824,5825,5826,5827,5828,5829,5830,5831,5832,5833,5834,5835,5836,5837,5838,5839,5840,5841,5842,5843,5844,5845]
def ridgeSupport960_017 : List Nat := [5846,5847,6328,6329,6330,6331,6332,6333,6334,6335,6336,6337,6338,6339,6340,6341,6342,6343,6344,6345,6346,6347,6348,6349,6350,6351,6352,6353,6354,6355,6356,6357]
def ridgeSupport960_018 : List Nat := [6358,6359,6360,6361,6362,6363,6364,6365,6366,6367,6368,6369,6370,6371,6372,6373,6374,6375,7072,7073,7074,7075,7076,7077,7078,7079,7080,7081,7082,7083,7108,7109]
def ridgeSupport960_019 : List Nat := [7110,7111,7112,7113,7114,7115,7116,7117,7118,7119,7144,7145,7146,7147,7148,7149,7150,7151,7152,7153,7154,7155,7204,7205,7206,7207,7208,7209,7210,7211,7212,7213]
def ridgeSupport960_020 : List Nat := [7214,7215,7240,7241,7242,7243,7244,7245,7246,7247,7248,7249,7250,7251,7300,7301,7302,7303,7304,7305,7306,7307,7308,7309,7310,7311,7360,7361,7362,7363,7364,7365]
def ridgeSupport960_021 : List Nat := [7366,7367,7368,7369,7370,7371,7396,7397,7398,7399,7400,7401,7402,7403,7404,7405,7406,7407,7456,7457,7458,7459,7460,7461,7462,7463,7464,7465,7466,7467,7516,7517]
def ridgeSupport960_022 : List Nat := [7518,7519,7520,7521,7522,7523,7524,7525,7526,7527,7552,7553,7554,7555,7556,7557,7558,7559,7560,7561,7562,7563,7612,7613,7614,7615,7616,7617,7618,7619,7620,7621]
def ridgeSupport960_023 : List Nat := [7622,7623]
def ridgeSupport960_code : Nat := 0x771ddc67715dc4770ddc27705dc076fddbe76f5dbc762dd8a7625d88761dd867615d84760dd827605d80759dd667595d64758dd627585d60757dd5e7575d5c74add2a74a5d28749dd267495d24748dd227485d2073bdcee73b5cec73adcea73a5ce8739dce67395ce4732dcca7325cc8731dcc67315cc4730dcc27305cc0723dc8e7235c8c722dc8a7225c88721dc867215c84714dc527145c50713dc4e7135c4c712dc4a7125c4870bdc2e70b5c2c70adc2a70a5c28709dc267095c246fcdbf26fc5bf06fbdbee6fb5bec6fadbea6fa5be86f3dbce6f35bcc6f2dbca6f25bc86f1dbc66f15bc46eadbaa6ea5ba86e9dba66e95ba46e8dba26e85ba0639d8e663958e4638d8e263858e0637d8de63758dc636d8da63658d8635d8d663558d4634d8d263458d0633d8ce63358cc632d8ca63258c8631d8c663158c4630d8c263058c062fd8be62f58bc62ed8ba62e58b85b5d6d65b556d45b4d6d25b456d05b3d6ce5b356cc5b2d6ca5b256c85b1d6c65b156c45b0d6c25b056c05afd6be5af56bc5aed6ba5ae56b85add6b65ad56b45acd6b25ac56b05abd6ae5ab56ac5aad6aa5aa56a8579d5e657955e4578d5e257855e0577d5de57755dc576d5da57655d8575d5d657555d4574d5d257455d0573d5ce57355cc572d5ca57255c8571d5c657155c4570d5c257055c056fd5be56f55bc56ed5ba56e55b84f5d3d64f553d44f4d3d24f453d04f3d3ce4f353cc4f2d3ca4f253c84f1d3c64f153c44f0d3c24f053c04efd3be4ef53bc4eed3ba4ee53b84edd3b64ed53b44ecd3b24ec53b04ebd3ae4eb53ac4ead3aa4ea53a8471d1c647151c4470d1c247051c046fd1be46f51bc46ed1ba46e51b846dd1b646d51b446cd1b246c51b046bd1ae46b51ac46ad1aa46a51a8469d1a646951a4468d1a246851a0467d19e467519c466d19a4665198435d0d643550d4434d0d243450d0433d0ce43350cc432d0ca43250c8431d0c643150c4430d0c243050c042fd0be42f50bc42ed0ba42e50b842dd0b642d50b442cd0b242c50b042bd0ae42b50ac42ad0aa42a50a83b1cec63b14ec43b0cec23b04ec03afcebe3af4ebc3aeceba3ae4eb83adceb63ad4eb43acceb23ac4eb03abceae3ab4eac3aaceaa3aa4ea83a9cea63a94ea43a8cea23a84ea03a7ce9e3a74e9c3a6ce9a3a64e9832dccb632d4cb432cccb232c4cb032bccae32b4cac32accaa32a4ca8329cca63294ca4328cca23284ca0327cc9e3274c9c326cc9a3264c98325cc963254c94324cc923244c90323cc8e3234c8c322cc8a3224c882f1cbc62f14bc42f0cbc22f04bc02efcbbe2ef4bbc2eecbba2ee4bb82edcbb62ed4bb42eccbb22ec4bb02ebcbae2eb4bac2eacbaa2ea4ba82e9cba62e94ba42e8cba22e84ba02e7cb9e2e74b9c2e6cb9a2e64b9826dc9b626d49b426cc9b226c49b026bc9ae26b49ac26ac9aa26a49a8269c9a626949a4268c9a226849a0267c99e267499c266c99a2664998265c9962654994264c9922644990263c98e263498c262c98a2624988231c8c623148c4230c8c223048c022fc8be22f48bc22ec8ba22e48b822dc8b622d48b422cc8b222c48b022bc8ae22b48ac22ac8aa22a48a8229c8a622948a4228c8a222848a0227c89e227489c226c89a22648981f5c7d61f547d41f4c7d21f447d01f3c7ce1f347cc1f2c7ca1f247c81f1c7c61f147c41f0c7c21f047c01efc7be1ef47bc1eec7ba1ee47b81edc7b61ed47b41ecc7b21ec47b01ebc7ae1eb47ac1eac7aa1ea47a81cec73a1ce47221c847201ad46b41acc5ac16ac5aa101c40610142620984260
def ridgeSupport960_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport960_code
def ridgeSupport960_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport960_code
def ridgeSupport960_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport960_code
def ridgeSupport960_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport960_code
def ridgeSupport960_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport960_code
def ridgeSupport960_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport960_code
def ridgeSupport960_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport960_code
def ridgeSupport960_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport960_code
def ridgeSupport960_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport960_code
def ridgeSupport960_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport960_code
def ridgeSupport960_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport960_code
def ridgeSupport960_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport960_code
def ridgeSupport960_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport960_code
def ridgeSupport960_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport960_code
def ridgeSupport960_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport960_code
def ridgeSupport960_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport960_code
def ridgeSupport960_rest_016 : Nat := PackedRawNatGrowth.drop 7168 ridgeSupport960_code
def ridgeSupport960_rest_017 : Nat := PackedRawNatGrowth.drop 7616 ridgeSupport960_code
def ridgeSupport960_rest_018 : Nat := PackedRawNatGrowth.drop 8064 ridgeSupport960_code
def ridgeSupport960_rest_019 : Nat := PackedRawNatGrowth.drop 8512 ridgeSupport960_code
def ridgeSupport960_rest_020 : Nat := PackedRawNatGrowth.drop 8960 ridgeSupport960_code
def ridgeSupport960_rest_021 : Nat := PackedRawNatGrowth.drop 9408 ridgeSupport960_code
def ridgeSupport960_rest_022 : Nat := PackedRawNatGrowth.drop 9856 ridgeSupport960_code
def ridgeSupport960_rest_023 : Nat := PackedRawNatGrowth.drop 10304 ridgeSupport960_code
def ridgeSupport960_rest_024 : Nat := PackedRawNatGrowth.drop 10332 ridgeSupport960_code
def ridgeSupport960_suffix_024 : List Nat := []
def ridgeSupport960_suffix_023 : List Nat := ridgeSupport960_023 ++ ridgeSupport960_suffix_024
def ridgeSupport960_suffix_022 : List Nat := ridgeSupport960_022 ++ ridgeSupport960_suffix_023
def ridgeSupport960_suffix_021 : List Nat := ridgeSupport960_021 ++ ridgeSupport960_suffix_022
def ridgeSupport960_suffix_020 : List Nat := ridgeSupport960_020 ++ ridgeSupport960_suffix_021
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
    (PackedRawNatGrowth.readList 14 738 ridgeSupport960_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
