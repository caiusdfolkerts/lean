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
def ridgeSupport770_000 : List Nat := [14,36,46,52,55,56,162,163,166,167,170,171,234,235,238,239,242,243,289,290,291,294,295,300,301,306,308,310,311,312,315,316]
def ridgeSupport770_001 : List Nat := [321,322,327,329,573,577,578,579,580,582,583,590,592,594,598,599,600,601,603,604,611,613,677,678,679,680,681,682,729,733,734,735]
def ridgeSupport770_002 : List Nat := [736,738,739,746,748,750,754,755,756,757,759,760,767,769,813,817,818,819,820,822,823,830,832,834,838,839,840,841,843,844,851,853]
def ridgeSupport770_003 : List Nat := [855,856,860,861,862,863,865,866,874,876,877,879,1390,1392,1396,1398,1476,1477,1482,1483,1484,1485,1490,1491,1496,1498,1502,1504,1524,1525,1530,1531]
def ridgeSupport770_004 : List Nat := [1558,1560,1564,1566,1572,1573,1578,1579,1580,1581,1586,1587,1604,1605,1610,1611,1894,1896,1900,1902,1932,1933,1938,1939,1980,1981,1986,1987,1988,1989,1994,1995]
def ridgeSupport770_005 : List Nat := [2000,2002,2006,2008,2014,2016,2020,2022,2028,2029,2034,2035,2076,2077,2082,2083,2100,2101,2106,2107,2254,2256,2284,2286,2294,2295,2312,2313,2326,2328,2356,2358]
def ridgeSupport770_006 : List Nat := [2366,2367,2384,2385,2662,2664,2668,2670,2700,2701,2706,2707,2748,2749,2754,2755,2756,2757,2762,2763,2768,2770,2774,2776,2782,2784,2788,2790,2796,2797,2802,2803]
def ridgeSupport770_007 : List Nat := [2844,2845,2850,2851,2868,2869,2874,2875,3022,3024,3052,3054,3062,3063,3080,3081,3094,3096,3124,3126,3134,3135,3152,3153,3766,3768,3772,3774,3804,3805,3810,3811]
def ridgeSupport770_008 : List Nat := [3852,3853,3858,3859,3860,3861,3866,3867,3872,3874,3878,3880,3886,3888,3892,3894,3900,3901,3906,3907,3948,3949,3954,3955,3972,3973,3978,3979,4378,4380,4390,4392]
def ridgeSupport770_009 : List Nat := [4418,4419,4430,4431,4450,4452,4462,4464,4490,4491,4502,4503,4834,4835,4842,4843,5134,5136,5138,5140,5159,5161,5163,5165,5182,5184,5188,5190,5207,5209,5211,5213]
def ridgeSupport770_010 : List Nat := [5230,5232,5236,5238,5267,5269,5271,5273,5303,5305,5309,5311,5372,5373,5454,5455,5550,5551,5706,5707,5868,5869,5874,5875,5876,5877,5879,5881,5882,5883,5960,5962]
def ridgeSupport770_011 : List Nat := [5966,5968,5984,5985,5987,5989,5990,5991,6038,6039,6041,6043,6056,6057,6059,6061,6128,6130,6134,6136,6152,6153,6155,6157,6158,6159,6206,6207,6209,6211,6224,6225]
def ridgeSupport770_012 : List Nat := [6227,6229,6344,6346,6350,6352,6368,6369,6371,6373,6374,6375,6476,6477,6479,6481,6494,6495,6497,6499]
def ridgeSupport770_code : Nat := 0xcb1e5872bf95eca8e53f29b94cc73e39b1cb8e3c70e3831a18cec6563230ab853c28e143087841c1fe0fb01f80ec06e02f013808bfc5fdafe57f0bd6deaef537a8bcdde66f2f796bb3dd9aecb763bb0dd82ea174eba55d22df76fab7cdbdedeb6f4b79dbcaddb6ecb25d92ab5f5aeaa7d53a9fb4fca5fd2f69734b7a4cd25e92b493a3b51d28e146ea2ed16e8b3457a23511288143ea16d0ae853427a0a504a82140e975cbaa5c72e28cbc65a31718a8b845ba2c91628a7c53a287142894449a23911a7c5be29f0af847b9bdc9edaf6c7a1bd09e7af3c79b3cd1e60f2e7943c99e44f2078dbc69e2af14789bc49e1af0c771bb89dbaedc75f3af1d70eb6628b14187ec3e61b30d1830c16604b0217eebf65f72fb17a0bce59dace966ab34591ac8963ab1c579abc95daaec5732b915c0ade56c2b595a4ad0565ab2958aac4561ab0957aabc549aa4951aa8c53729b14d0a664a8a54127e93e49b24d1230916484a4211ee8f647723b11a08ce41da0e906a834411a08903a81c3f99fc8fda7ec3f31f90fc07de3ec1f58fa47d03e59f28f8a7c43e19f08f7a7bc3c99e48f1a78c3b71db0ed07663259928c8a64431998c8c5a62c31598a8c4a62430f1870c306162fd97e8bea5f42f01778bb45d82e99748b9a5cc2e59728b8a5c42bb15d0ae056e1b78db46d836a1b10d846be35e1ae8d706b03571aa8d4c69834b1a48d2068e3461a10d0067c33719b0cd06663321988cb46022ff17c0bdc5ea2f41798bc85dc2ec1750b8c5c42e016f8b785ba2d91550aa45502a71530a944ca26312e096c4b225812b89584a4250127091c48c244121890848223d0a4851c28414109e04ec27013709b04d026412d096049c24c12309104841e60f207783b81d60ea05582a814e0a6051828807003701a00b804800e
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
def ridgeSupport770_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport770_code
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport770_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
