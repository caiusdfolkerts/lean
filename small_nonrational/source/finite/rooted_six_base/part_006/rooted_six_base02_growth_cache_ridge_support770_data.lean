module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport770_000 : List Nat := [14,36,46,52,55,56,162,163,166,167,170,171,234,235,238,239,242,243,289,290,291,294,295,300,301,306,308,310,311,312,315,316]
def ridgeSupport770_001 : List Nat := [321,322,327,329,573,577,578,579,580,582,583,590,592,594,598,599,600,601,603,604,611,613,677,678,679,680,681,682,729,733,734,735]
def ridgeSupport770_002 : List Nat := [736,738,739,746,748,750,754,755,756,757,759,760,767,769,813,817,818,819,820,822,823,830,832,834,838,839,840,841,843,844,851,853]
def ridgeSupport770_003 : List Nat := [855,856,860,861,862,863,865,866,874,876,877,879,1390,1392,1396,1398,1476,1477,1482,1483,1484,1485,1490,1491,1496,1498,1502,1504,1524,1525,1530,1531]
def ridgeSupport770_004 : List Nat := [1558,1560,1564,1566,1572,1573,1578,1579,1580,1581,1586,1587,1604,1605,1610,1611,1894,1896,1900,1902,1932,1933,1938,1939,1980,1981,1986,1987,1988,1989,1994,1995]
def ridgeSupport770_005 : List Nat := [2000,2002,2006,2008,2014,2016,2020,2022,2028,2029,2034,2035,2076,2077,2082,2083,2100,2101,2106,2107,2254,2256,2284,2286,2294,2295,2312,2313,2326,2328,2356,2358]
def ridgeSupport770_006 : List Nat := [2366,2367,2384,2385,2662,2664,2668,2670,2700,2701,2706,2707,2748,2749,2754,2755,2756,2757,2762,2763,2768,2770,2774,2776,2782,2784,2788,2790,2796,2797,2802,2803]
def ridgeSupport770_007 : List Nat := [2844,2845,2850,2851,2868,2869,2874,2875,3022,3024,3052,3054,3062,3063,3080,3081,3094,3096,3124,3126,3134,3135,3152,3153,3766,3768,3772,3774,3804,3805,3810,3811]
def ridgeSupport770_008 : List Nat := [3852,3853,3858,3859,3860,3861,3866,3867,3872,3874,3878,3880,3886,3888,3892,3894,3900,3901,3906,3907,3948,3949,3954,3955,3972,3973,3978,3979,4378,4380,4390,4392]
def ridgeSupport770_009 : List Nat := [4418,4419,4430,4431,4450,4452,4462,4464,4490,4491,4502,4503,4834,4835,4842,4843,5134,5136,5138,5140,5156,5157,5162,5163,5168,5170,5174,5176,5196,5197,5202,5203]
def ridgeSupport770_010 : List Nat := [5204,5205,5210,5211,5230,5232,5236,5238,5244,5245,5250,5251,5252,5253,5255,5256,5410,5412,5414,5416,5436,5437,5442,5443,5444,5445,5450,5451,5456,5458,5462,5464]
def ridgeSupport770_011 : List Nat := [5470,5472,5476,5478,5484,5485,5490,5491,5492,5493,5498,5499,5523,5524,5526,5527,5638,5640,5642,5643,5660,5661,5668,5670,5678,5679,5687,5689,5692,5694,5696,5697]
def ridgeSupport770_012 : List Nat := [5714,5715,5722,5724,5732,5733,5741,5743,5890,5892,5894,5896,5916,5917,5922,5923,5924,5925,5930,5931,5936,5938,5942,5944,5950,5952,5956,5958,5964,5965,5970,5971]
def ridgeSupport770_013 : List Nat := [5972,5973,5978,5979,6003,6004,6006,6007,6118,6120,6122,6123,6140,6141,6148,6150,6158,6159,6167,6169,6172,6174,6176,6177,6194,6195,6202,6204,6212,6213,6221,6223]
def ridgeSupport770_014 : List Nat := [6526,6528,6530,6532,6552,6553,6558,6559,6560,6561,6566,6567,6572,6574,6578,6580,6586,6588,6592,6594,6600,6601,6606,6607,6608,6609,6614,6615,6639,6640,6642,6643]
def ridgeSupport770_015 : List Nat := [6898,6900,6902,6903,6910,6912,6914,6915,6923,6925,6929,6931,6952,6954,6956,6957,6964,6966,6968,6969,6977,6979,6983,6985,7146,7147,7366,7368,7370,7372,7391,7393]
def ridgeSupport770_016 : List Nat := [7395,7397,7414,7416,7420,7422,7439,7441,7443,7445,7462,7464,7468,7470,7499,7501,7503,7505,7535,7537,7541,7543,7604,7605,7686,7687,7782,7783,7938,7939]
def ridgeSupport770_code : Nat := 0x3e07f02f33f99bc0fe06edaf6d3aefd75eb8f5bfaa3d4fea6f52fa5dd2ce94749ba2bd13e88f43f9fdcfce7c73db9cbce3e70f37f999ccae64731b7d7beada4ed1f687b41d9cece366db34d96ecb3655b28d89ec4761bb0bd81ec0b601afed7bebdb5e9af2cf9e7cb3e19efcebe75b3a39d0ce7e73b3939c8ce167033799bacda66cb35d9accd3e69b3439a0ccfe67b333998cc2660b30197ec27e13708b844c1e60eb067832c10e08303d81cc0ce05f01f80ec036012ffb7fcbf5dfaafd17e6bbbdddaee9773baddd6aeab754ba9dd4ae9b74cba35d12e8173eb9c5cdae65730b95dcaae4b724b91dc8ae3b71cb845c1ae09702b37d9b6ccb664b2e596aca7652b20d902c7d63cb1cd8dec5f62eb135892c3b61cb05d82ac11606acbd65ab29593abdd5eaaeb574ab9d5caadb56cab35592ac155eaac555aaa5550aa5d52aa8b544aa1d50aa7b53ca94549aa49522a44521e90b484a41d20a8fb47ca3b51d28e146ea2dd16a8ab454a29d14a89b44ca1c50da865430a15d0aa84b424a0a504a82140e975cbaa5c72e28cbc65a31718a8b845ba2c91628a7c53a287142894449a23911a7c5be29f0af847b9bdc9edaf6c7a1bd09e7af3c79b3cd1e60f2e7943c99e44f2078dbc69e2af14789bc49e1af0c771bb89dbaedc75f3af1d70eb6628b14187ec3e61b30d1830c16604b0217eebf65f72fb17a0bce59dace966ab34591ac8963ab1c579abc95daaec5732b915c0ade56c2b595a4ad0565ab2958aac4561ab0957aabc549aa4951aa8c53729b14d0a664a8a54127e93e49b24d1230916484a4211ee8f647723b11a08ce41da0e906a834411a08903a81c3f99fc8fda7ec3f31f90fc07de3ec1f58fa47d03e59f28f8a7c43e19f08f7a7bc3c99e48f1a78c3b71db0ed07663259928c8a64431998c8c5a62c31598a8c4a62430f1870c306162fd97e8bea5f42f01778bb45d82e99748b9a5cc2e59728b8a5c42bb15d0ae056e1b78db46d836a1b10d846be35e1ae8d706b03571aa8d4c69834b1a48d2068e3461a10d0067c33719b0cd06663321988cb46022ff17c0bdc5ea2f41798bc85dc2ec1750b8c5c42e016f8b785ba2d91550aa45502a71530a944ca26312e096c4b225812b89584a4250127091c48c244121890848223d0a4851c28414109e04ec27013709b04d026412d096049c24c12309104841e60f207783b81d60ea05582a814e0a6051828807003701a00b804800e
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
def ridgeSupport770_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport770_code
def ridgeSupport770_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport770_code
def ridgeSupport770_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport770_code
def ridgeSupport770_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport770_code
def ridgeSupport770_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport770_code
def ridgeSupport770_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport770_code
def ridgeSupport770_suffix_017 : List Nat := []
def ridgeSupport770_suffix_016 : List Nat := ridgeSupport770_016 ++ ridgeSupport770_suffix_017
def ridgeSupport770_suffix_015 : List Nat := ridgeSupport770_015 ++ ridgeSupport770_suffix_016
def ridgeSupport770_suffix_014 : List Nat := ridgeSupport770_014 ++ ridgeSupport770_suffix_015
def ridgeSupport770_suffix_013 : List Nat := ridgeSupport770_013 ++ ridgeSupport770_suffix_014
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
    (PackedRawNatGrowth.readList 13 542 ridgeSupport770_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
