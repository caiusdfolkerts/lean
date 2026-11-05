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
def ridgeSupport769_000 : List Nat := [14,20,26,29,30,164,165,166,167,168,169,236,237,238,239,240,241,288,292,293,294,295,297,298,305,307,309,313,314,315,316,318]
def ridgeSupport769_001 : List Nat := [319,326,328,376,380,381,382,383,385,386,393,395,397,401,402,403,404,406,407,414,416,460,464,465,466,467,469,470,477,479,481,485]
def ridgeSupport769_002 : List Nat := [486,487,488,490,491,498,500,502,503,507,508,509,510,512,513,521,523,524,526,1414,1416,1420,1422,1452,1453,1458,1459,1500,1501,1506,1507,1508]
def ridgeSupport769_003 : List Nat := [1509,1514,1515,1520,1522,1526,1528,1534,1536,1540,1542,1548,1549,1554,1555,1596,1597,1602,1603,1620,1621,1626,1627,1654,1656,1660,1662,1692,1693,1698,1699,1740]
def ridgeSupport769_004 : List Nat := [1741,1746,1747,1748,1749,1754,1755,1760,1762,1766,1768,1774,1776,1780,1782,1788,1789,1794,1795,1836,1837,1842,1843,1860,1861,1866,1867,2266,2268,2278,2280,2306]
def ridgeSupport769_005 : List Nat := [2307,2318,2319,2338,2340,2350,2352,2378,2379,2390,2391,2422,2424,2428,2430,2460,2461,2466,2467,2508,2509,2514,2515,2516,2517,2522,2523,2528,2530,2534,2536,2542]
def ridgeSupport769_006 : List Nat := [2544,2548,2550,2556,2557,2562,2563,2604,2605,2610,2611,2628,2629,2634,2635,3034,3036,3046,3048,3074,3075,3086,3087,3106,3108,3118,3120,3146,3147,3158,3159,3730]
def ridgeSupport769_007 : List Nat := [3731,3734,3735,5146,5148,5150,5152,5172,5173,5178,5179,5180,5181,5186,5187,5192,5194,5198,5200,5206,5208,5212,5214,5220,5221,5226,5227,5228,5229,5234,5235,5259]
def ridgeSupport769_008 : List Nat := [5260,5262,5263,5278,5280,5282,5284,5304,5305,5310,5311,5312,5313,5318,5319,5324,5326,5330,5332,5338,5340,5344,5346,5352,5353,5358,5359,5360,5361,5366,5367,5391]
def ridgeSupport769_009 : List Nat := [5392,5394,5395,5650,5652,5654,5655,5662,5664,5666,5667,5675,5677,5681,5683,5704,5706,5708,5709,5716,5718,5720,5721,5729,5731,5735,5737,5758,5760,5762,5764,5784]
def ridgeSupport769_010 : List Nat := [5785,5790,5791,5792,5793,5798,5799,5804,5806,5810,5812,5818,5820,5824,5826,5832,5833,5838,5839,5840,5841,5846,5847,5871,5872,5874,5875,6130,6132,6134,6135,6142]
def ridgeSupport769_011 : List Nat := [6144,6146,6147,6155,6157,6161,6163,6184,6186,6188,6189,6196,6198,6200,6201,6209,6211,6215,6217,6510,6511,7367,7369,7371,7373,7379,7381,7383,7385,7415,7417,7421]
def ridgeSupport769_012 : List Nat := [7423,7427,7429,7431,7433,7463,7465,7469,7471,7614,7615,7650,7651,7746,7747]
def ridgeSupport769_code : Nat := 0x790fc85de3ef176ffb7dd2fe96f4a7a4fd09e83f417a07cffe7ef3e79efcd9e6bf3579a7ccde65f32798f96fcb7612708f843c20e0e7071836c1a60b705982ac14604f02380dc05e00f005800bff5fdefed7f4bf95bcede56f0b77db5edad6d1b685b3ed9d6c9b645b0ad816bcb5d5ad2d656aeb565a9ed4d6a1b505a7ed3d699b4c5a12d05680b3f59a6ccf663b30d966cb1656b2a5936c9964ab2458cec6362db15d88ec45620b0f585ec2d614b09544ea25510a87d3de9ed4f1a7853be9dd4e9a74538a9c14dca6d53529a54cea66531e98d4c1a6052fe97d4b9a5c52929454a0a4f523e91d48ca45d1ce8e546da3651ae8d5465a32517a8b9458a2b514289d44aa24510e88543da1e50ee875435a1a508283d41ca0d3a5dd2ce93749315d8acc4b62530c185cc24611303d81cc036012fa17ccbdc5ed292d494a4552228cd464a2d516280d4049fd4fe27d93e89f04f727a13cc9e24f0276d3b49d54ea274d3a49cd4e6268d34499d4ce25f92f89784bb255d2ac94b4a524c125c924491243d21c90348123a11cc8dc46d1d2ce947453a21ccce6472d3961c0ce046fd37e1bd8de86f03771ba0dcc6e23701b6cdb46d536a1b4cda46cd3661a8cd4469d34e19f8cf867833b196ccb465532a190cc8463d31e184cc2460d3061818c086002ff17e0bec5f22f817acbd45e52f2178cbc45dd2ee16ccb645ad2d61638b185882c3083841820b10488044001fe0fe87f03f61f70fb07d03e41eb0f507a03ce1e60f287843be1dd0eb07543a61d20e887403981a00cf065c32c1940c9864832218d0c586243041810bf85f82fa17c0bc052028c13f09f04f027613a09c84d426613109504a424e12609284902400f107803bc1dc0ed07602a41500a7053029414801e00e806802800e
def ridgeSupport769_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport769_code
def ridgeSupport769_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport769_code
def ridgeSupport769_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport769_code
def ridgeSupport769_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport769_code
def ridgeSupport769_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport769_code
def ridgeSupport769_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport769_code
def ridgeSupport769_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport769_code
def ridgeSupport769_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport769_code
def ridgeSupport769_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport769_code
def ridgeSupport769_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport769_code
def ridgeSupport769_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport769_code
def ridgeSupport769_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport769_code
def ridgeSupport769_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport769_code
def ridgeSupport769_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport769_code
def ridgeSupport769_suffix_013 : List Nat := []
def ridgeSupport769_suffix_012 : List Nat := ridgeSupport769_012 ++ ridgeSupport769_suffix_013
def ridgeSupport769_suffix_011 : List Nat := ridgeSupport769_011 ++ ridgeSupport769_suffix_012
def ridgeSupport769_suffix_010 : List Nat := ridgeSupport769_010 ++ ridgeSupport769_suffix_011
def ridgeSupport769_suffix_009 : List Nat := ridgeSupport769_009 ++ ridgeSupport769_suffix_010
def ridgeSupport769_suffix_008 : List Nat := ridgeSupport769_008 ++ ridgeSupport769_suffix_009
def ridgeSupport769_suffix_007 : List Nat := ridgeSupport769_007 ++ ridgeSupport769_suffix_008
def ridgeSupport769_suffix_006 : List Nat := ridgeSupport769_006 ++ ridgeSupport769_suffix_007
def ridgeSupport769_suffix_005 : List Nat := ridgeSupport769_005 ++ ridgeSupport769_suffix_006
def ridgeSupport769_suffix_004 : List Nat := ridgeSupport769_004 ++ ridgeSupport769_suffix_005
def ridgeSupport769_suffix_003 : List Nat := ridgeSupport769_003 ++ ridgeSupport769_suffix_004
def ridgeSupport769_suffix_002 : List Nat := ridgeSupport769_002 ++ ridgeSupport769_suffix_003
def ridgeSupport769_suffix_001 : List Nat := ridgeSupport769_001 ++ ridgeSupport769_suffix_002
def ridgeSupport769_suffix_000 : List Nat := ridgeSupport769_000 ++ ridgeSupport769_suffix_001
theorem ridgeSupport769_source : candidateSupports 769 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport769_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
