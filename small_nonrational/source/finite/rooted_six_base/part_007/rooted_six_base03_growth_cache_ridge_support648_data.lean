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
def ridgeSupport648_000 : List Nat := [25,49,89,95,98,100,236,237,238,239,246,247,454,455,456,459,460,465,466,471,473,495,497,499,501,503,508,509,511,514,745,746]
def ridgeSupport648_001 : List Nat := [749,750,753,754,791,792,793,796,797,802,803,808,810,832,834,836,838,840,845,846,848,851,1277,1278,1279,1280,1281,1282,1320,1324,1325,1326]
def ridgeSupport648_002 : List Nat := [1327,1329,1330,1337,1339,1363,1365,1367,1368,1370,1372,1373,1377,1382,1404,1408,1409,1410,1411,1413,1414,1421,1423,1447,1449,1451,1452,1454,1456,1457,1461,1466]
def ridgeSupport648_003 : List Nat := [1467,1469,1471,1473,1474,1476,1478,1479,1483,1485,1490,1491,2238,2243,2244,2248,2264,2265,2268,2270,2274,2275,2281,2284,2296,2297,2306,2307,2312,2313,2322,2323]
def ridgeSupport648_004 : List Nat := [2334,2339,2344,2345,2348,2350,2354,2355,2358,2360,2364,2365,2370,2375,2376,2380,2396,2397,2400,2402,2406,2407,2413,2416,2428,2429,2438,2439,2444,2445,2454,2455]
def ridgeSupport648_005 : List Nat := [2466,2471,2476,2477,2480,2482,2486,2487,2490,2492,2496,2497,2556,2557,2564,2566,2568,2569,2576,2578,2592,2593,2604,2605,2666,2667,2670,2675,2678,2679,2682,2687]
def ridgeSupport648_006 : List Nat := [2702,2703,2714,2715,2862,2867,2868,2872,2884,2885,2894,2895,2900,2901,2904,2906,2910,2911,2917,2920,2922,2927,2932,2933,2936,2938,2942,2943,2948,2949,2958,2959]
def ridgeSupport648_007 : List Nat := [2974,2975,2979,2981,2998,2999,3498,3503,3504,3508,3520,3521,3530,3531,3536,3537,3540,3542,3546,3547,3553,3556,3558,3563,3568,3569,3572,3574,3578,3579,3584,3585]
def ridgeSupport648_008 : List Nat := [3594,3595,3610,3611,3615,3617,3674,3676,3678,3679,3696,3697,3704,3706,3714,3715,3723,3725,3780,3785,3788,3789,3806,3807,3810,3815,3824,3825,3829,3832,4250,4252]
def ridgeSupport648_009 : List Nat := [4254,4255,4262,4264,4266,4267,4275,4277,4281,4283,4356,4361,4364,4365,4368,4373,4376,4377,4381,4384,4387,4390,4458,4463,4464,4468,4470,4475,4476,4480,4488,4489]
def ridgeSupport648_010 : List Nat := [4502,4503,4519,4522,4525,4529,4579,4582,4585,4589,4598,4600,4608,4613,4659,4661,4669,4672,4832,4833,4868,4869,4970,4971,5126,5127]
def ridgeSupport648_code : Nat := 0x280f4069b5cdaa60b304970cb8248123d91ac8ce40b2008fc47da3db1e98f3478e3631ad8d5469e32f1968c4c62230117c8bdc5da2e91708b7c5aa24d123890447623311888ac44221b10c884c4121770b985ac2ce1570aa854429a13f09e84e4269df0ef5778bbc1dceee276fbb79d9aecc764bb11d1ae8b741ba09cf4e78738b9c1cbee5e72e3969c42e1f70db869c16e0a700b801bf6dfa6fb37d1be2df06f5b799bc8de16edb769bacdd46e8b741b96dca6e0b701b68db06d7b6a976ebb65d2ae8d73eb9e5c7ae3970ab845bfadf96f4b785baadd16deb6a5b42d956beb5e5ad2d616aab545a7ad3968ab4459c2cd1666b2e54daa6951ea8e53fa9e94eea76539a9b94d6a6a516a8b1442a205092841412a0850328113fa9fc4e0a7013789ba4dba6d93649b04d6a6b134e9a24cba65931a98c4c3a6192fa97c4b825b52ce9664b125812ba95c4a6252128e94249ea4f1270936499a4c925c92c494a4a124691e489a449212908481a4091f28f847623a51c68e246f23711b28d846423111868be2e99748b9a5cb2e39718b885c22e096fcb7a5bb2dd16d4b625b02d716b0b565a92d3963cb1a5862c2960cb045812c015f0acc5612ae9570ab45582ab9554aa653b29c94c8a6252f29714b4a585282811404a004ff27f13f46a63501a70d346903461a20d0868032a1940c8c64431d18e0c646303171790bc45dc2ed1750ba44041ff0fe87f03ee1f50f987c43de1d90eb87483a21cc0e5872038e1c607b83d81de0ee07683b00c806202f8164062019
def ridgeSupport648_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport648_code
def ridgeSupport648_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport648_code
def ridgeSupport648_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport648_code
def ridgeSupport648_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport648_code
def ridgeSupport648_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport648_code
def ridgeSupport648_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport648_code
def ridgeSupport648_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport648_code
def ridgeSupport648_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport648_code
def ridgeSupport648_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport648_code
def ridgeSupport648_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport648_code
def ridgeSupport648_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport648_code
def ridgeSupport648_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport648_code
def ridgeSupport648_suffix_011 : List Nat := []
def ridgeSupport648_suffix_010 : List Nat := ridgeSupport648_010 ++ ridgeSupport648_suffix_011
def ridgeSupport648_suffix_009 : List Nat := ridgeSupport648_009 ++ ridgeSupport648_suffix_010
def ridgeSupport648_suffix_008 : List Nat := ridgeSupport648_008 ++ ridgeSupport648_suffix_009
def ridgeSupport648_suffix_007 : List Nat := ridgeSupport648_007 ++ ridgeSupport648_suffix_008
def ridgeSupport648_suffix_006 : List Nat := ridgeSupport648_006 ++ ridgeSupport648_suffix_007
def ridgeSupport648_suffix_005 : List Nat := ridgeSupport648_005 ++ ridgeSupport648_suffix_006
def ridgeSupport648_suffix_004 : List Nat := ridgeSupport648_004 ++ ridgeSupport648_suffix_005
def ridgeSupport648_suffix_003 : List Nat := ridgeSupport648_003 ++ ridgeSupport648_suffix_004
def ridgeSupport648_suffix_002 : List Nat := ridgeSupport648_002 ++ ridgeSupport648_suffix_003
def ridgeSupport648_suffix_001 : List Nat := ridgeSupport648_001 ++ ridgeSupport648_suffix_002
def ridgeSupport648_suffix_000 : List Nat := ridgeSupport648_000 ++ ridgeSupport648_suffix_001
theorem ridgeSupport648_source : candidateSupports 648 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport648_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
