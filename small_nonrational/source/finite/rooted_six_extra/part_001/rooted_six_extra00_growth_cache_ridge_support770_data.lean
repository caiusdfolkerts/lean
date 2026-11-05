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
def ridgeSupport770_000 : List Nat := [14,44,54,60,63,64,190,191,194,195,198,199,262,263,266,267,270,271,317,318,319,322,323,328,329,334,336,338,339,340,343,344]
def ridgeSupport770_001 : List Nat := [349,350,355,357,685,686,687,688,689,690,737,741,742,743,744,746,747,754,756,758,762,763,764,765,767,768,775,777,841,842,843,844]
def ridgeSupport770_002 : List Nat := [845,846,893,897,898,899,900,902,903,910,912,914,918,919,920,921,923,924,931,933,977,981,982,983,984,986,987,994,996,998,1002,1003]
def ridgeSupport770_003 : List Nat := [1004,1005,1007,1008,1015,1017,1019,1020,1024,1025,1026,1027,1029,1030,1038,1040,1041,1043,1866,1868,1872,1874,1952,1953,1958,1959,1960,1961,1966,1967,1972,1974]
def ridgeSupport770_004 : List Nat := [1978,1980,2000,2001,2006,2007,2034,2036,2040,2042,2048,2049,2054,2055,2056,2057,2062,2063,2080,2081,2086,2087,2370,2372,2376,2378,2408,2409,2414,2415,2456,2457]
def ridgeSupport770_005 : List Nat := [2462,2463,2464,2465,2470,2471,2476,2478,2482,2484,2490,2492,2496,2498,2504,2505,2510,2511,2552,2553,2558,2559,2576,2577,2582,2583,2730,2732,2760,2762,2770,2771]
def ridgeSupport770_006 : List Nat := [2788,2789,2802,2804,2832,2834,2842,2843,2860,2861,3138,3140,3144,3146,3176,3177,3182,3183,3224,3225,3230,3231,3232,3233,3238,3239,3244,3246,3250,3252,3258,3260]
def ridgeSupport770_007 : List Nat := [3264,3266,3272,3273,3278,3279,3320,3321,3326,3327,3344,3345,3350,3351,3498,3500,3528,3530,3538,3539,3556,3557,3570,3572,3600,3602,3610,3611,3628,3629,4194,4196]
def ridgeSupport770_008 : List Nat := [4200,4202,4232,4233,4238,4239,4280,4281,4286,4287,4288,4289,4294,4295,4300,4302,4306,4308,4314,4316,4320,4322,4328,4329,4334,4335,4376,4377,4382,4383,4400,4401]
def ridgeSupport770_009 : List Nat := [4406,4407,4806,4808,4818,4820,4846,4847,4858,4859,4878,4880,4890,4892,4918,4919,4930,4931,5334,5336,5346,5348,5374,5375,5386,5387,5406,5408,5418,5420,5446,5447]
def ridgeSupport770_010 : List Nat := [5458,5459,7072,7073,7154,7155,7250,7251,7370,7371,7688,7689,7694,7695,7696,7697,7699,7701,7702,7703,7780,7782,7786,7788,7804,7805,7807,7809,7810,7811,7858,7859]
def ridgeSupport770_011 : List Nat := [7861,7863,7876,7877,7879,7881,7948,7950,7954,7956,7972,7973,7975,7977,7978,7979,8026,8027,8029,8031,8044,8045,8047,8049,8188,8190,8194,8196,8212,8213,8215,8217]
def ridgeSupport770_012 : List Nat := [8218,8219,8320,8321,8323,8325,8338,8339,8341,8343,8440,8441,8443,8445,8458,8459,8461,8463]
def ridgeSupport770_code : Nat := 0x843e10d842e10a83f60fb83e60f8825e095824e09282160838206080806e01a8066017805601480120027ff9ffc7dc5f6f7db5f6c7d7df5d7d6df5a7cadf2a7ca5f277c95f247c51f127c39f0c7b25ec77b15ec47addeb57acdeb27a0de827a05e7f79f5e7c79b1e6a7999e64785de167855e137845e10783de0e7825e08732dcca714dc526fcdbf26e85ba0554d552551d54654b152a548151e542d50a53fd4fe53914e253614d64d0d3424cdd3364c7131a4c4130e4bed2fa4bbd2ee4b512d24b212c644dd13644c5130447d11e446511843bd0ee43a50e843890e043710da43510d243390cc431d0c643050c042fd0be42e50b8423d08e422508841a9068419106238b4e2c386ce1a3848e1037d0df23794de4374cdd23728dc836b0daa345cd163444d1033fccfe33e4cf8333ccce3324cc83308cc032f0cba32d0cb232b8cac329cca63284ca0327cc9e3264c9831bcc6e31a4c683128c483110c422cb4b2c2c6cb1a2c48b102bd0af22b94ae42b4cad22b28ac82ab0aaa285ca162844a1027fc9fe27e49f8273c9ce27249c827089c026f09ba26d09b226b89ac269c9a626849a0267c99e266499825bc96e25a496825289482510942209c8262084820203c80e2024808201c80620048001fe87f81fd07f21f5c7d61f447d01ef07ba1ed87b41ebc7ae1ea47a81e9c7a61e847a01d487501d3074a104c411104040e1018405100c40210044000ff03fb0fe43f70fc03ef0fb43ec0fac3ea0f983e40f883db0f683d80f5c3d60f543d10e943a30e7039b0e643980e5c3960e483900e383870e183840e0c3820e0437d0d3834d0d3034b0d283490c243070c002ff0bf42fc0bec2fa0bd82f40bc82eb0ba82e80b9c2e60b942e10ac82b10ac02af0ab82ad0594163057815d05601570550153054815005381490520143050813f04f813d043c10e042c10a041c106031c0c6030c0c202fc0be010003f00f003600b000e
def ridgeSupport770_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport770_code
def ridgeSupport770_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport770_code
def ridgeSupport770_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport770_code
def ridgeSupport770_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport770_code
def ridgeSupport770_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport770_code
def ridgeSupport770_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport770_code
def ridgeSupport770_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport770_code
def ridgeSupport770_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport770_code
def ridgeSupport770_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport770_code
def ridgeSupport770_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport770_code
def ridgeSupport770_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport770_code
def ridgeSupport770_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport770_code
def ridgeSupport770_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport770_code
def ridgeSupport770_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport770_code
def ridgeSupport770_suffix_013 : List Nat := []
def ridgeSupport770_suffix_012 : List Nat := ridgeSupport770_012 ++ ridgeSupport770_suffix_013
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
    (PackedRawNatGrowth.readList 14 402 ridgeSupport770_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
