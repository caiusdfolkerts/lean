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
def ridgeSupport577_000 : List Nat := [11,17,23,28,29,128,129,130,131,132,133,200,201,202,203,204,205,268,270,272,273,275,277,278,282,287,289,291,293,294,296,298]
def ridgeSupport577_001 : List Nat := [299,303,308,356,358,360,361,363,365,366,370,375,377,379,381,382,384,386,387,391,396,440,442,444,445,447,449,450,454,459,461,463]
def ridgeSupport577_002 : List Nat := [465,466,468,470,471,475,480,503,504,506,507,510,511,512,514,515,517,524,525,1418,1423,1424,1429,1440,1441,1454,1455,1488,1489,1502,1503,1508]
def ridgeSupport577_003 : List Nat := [1510,1516,1517,1522,1523,1529,1531,1536,1537,1538,1543,1544,1549,1550,1551,1584,1585,1598,1599,1608,1609,1622,1623,1658,1663,1664,1669,1680,1681,1694,1695,1728]
def ridgeSupport577_004 : List Nat := [1729,1742,1743,1748,1750,1756,1757,1762,1763,1769,1771,1776,1777,1778,1783,1784,1789,1790,1791,1824,1825,1838,1839,1848,1849,1862,1863,2192,2197,2204,2209,2236]
def ridgeSupport577_005 : List Nat := [2237,2248,2249,2264,2269,2276,2281,2308,2309,2320,2321,2426,2431,2432,2437,2448,2449,2462,2463,2496,2497,2510,2511,2516,2518,2524,2525,2530,2531,2537,2539,2544]
def ridgeSupport577_006 : List Nat := [2545,2546,2551,2552,2557,2558,2559,2592,2593,2606,2607,2616,2617,2630,2631,2960,2965,2972,2977,3004,3005,3016,3017,3032,3037,3044,3049,3076,3077,3088,3089,3682]
def ridgeSupport577_007 : List Nat := [3683,3686,3687,5144,5146,5153,5155,5160,5161,5174,5175,5180,5182,5188,5189,5194,5195,5201,5203,5208,5209,5210,5215,5216,5221,5222,5223,5236,5237,5242,5243,5253]
def ridgeSupport577_008 : List Nat := [5254,5261,5262,5276,5278,5285,5287,5292,5293,5306,5307,5312,5314,5320,5321,5326,5327,5333,5335,5340,5341,5342,5347,5348,5353,5354,5355,5368,5369,5374,5375,5385]
def ridgeSupport577_009 : List Nat := [5386,5393,5394,5594,5599,5602,5603,5606,5611,5614,5615,5619,5622,5625,5628,5648,5653,5656,5657,5660,5665,5668,5669,5673,5676,5679,5682,5756,5758,5765,5767,5772]
def ridgeSupport577_010 : List Nat := [5773,5786,5787,5792,5794,5800,5801,5806,5807,5813,5815,5820,5821,5822,5827,5828,5833,5834,5835,5848,5849,5854,5855,5865,5866,5873,5874,6074,6079,6082,6083,6086]
def ridgeSupport577_011 : List Nat := [6091,6094,6095,6099,6102,6105,6108,6128,6133,6136,6137,6140,6145,6148,6149,6153,6156,6159,6162,6498,6499,7365,7367,7372,7374,7377,7379,7384,7386,7407,7410,7413]
def ridgeSupport577_012 : List Nat := [7416,7425,7427,7432,7434,7455,7458,7461,7464,7608,7609,7644,7645,7740,7741]
def ridgeSupport577_code : Nat := 0x78f7c79dddeee76e7b71d28e92f48ba3fd0ae84740fa03cf8e7af3cb9dfcdae6c734f9a3ccee66731f98b963cb1604b01f80cc04e017009801bfe5fe6ff17f5bf85f72fb37d6be9df3ef9d7cbbe35f0ef857bfbdd5bcade36eab74db7edbd6d9b6c5b2ed956c9b625b0ed7d6bdb5e5aded6b6afb575aa6d516a2b505a6ed3568db465a1ed0b67eb3e58cac5f62cb14d896c49621b0e5866c31615b0857f2bf35f6af9d7bebdd5ebaf3578ebc55dfaed544aa2350aa84d3fe9fd4f9a7c53ae9d54e9a72538e9bd4dda6e535e9ab4cfa6753269914c2a6052ee9754ada56529e94b49ea4e523a91b486a42d1ee8f5475a3a519e8cd465a30517e8b5459a2c514e8a344ba25511688943ea1e50de86d429a14508e84341aa0c399dccce637313045820c056022fa57c8bdd5ec2f25790bbd5de2e85738b955c8291d48ca3951c28bd45ca2151027fd3fc9fd4fc27dd3e49f14f827ad3d29e34f127753b89d64ea273d39c9c14e0267d33c9914c8261530097f4bd244522090548223a51c88dd46c23251908bd45e22851388954481d1ce8c73939c1cbce5c7213901bfcdfc6fd37c1bdcde46f13781bacdd26e33711b74db86d636a1b3cd9c6c13601a7cd3c6913481a14d0067f33d195ccac64932418fcc7c631318183cc1c60d304181cc0460130017ecbf25f32f917b4bd85e62f2177cbbc5d12e816bcb5c5a12d01654b2058f2c5083441820510188084001ff0ff07ec3f41f80fb87803b61d70eb07503a41d10e787343961c60e1070437e1bd0de06e837018c0c3860c3041800bf05f42f61790bb85c82dc16d0b585a42d01660b204d025e12b09504a024c125091848423e11a08b045422611108804382180cd066032c1940c90640214108083041020410001d00e005c02200b
def ridgeSupport577_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport577_code
def ridgeSupport577_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport577_code
def ridgeSupport577_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport577_code
def ridgeSupport577_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport577_code
def ridgeSupport577_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport577_code
def ridgeSupport577_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport577_code
def ridgeSupport577_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport577_code
def ridgeSupport577_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport577_code
def ridgeSupport577_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport577_code
def ridgeSupport577_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport577_code
def ridgeSupport577_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport577_code
def ridgeSupport577_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport577_code
def ridgeSupport577_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport577_code
def ridgeSupport577_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport577_code
def ridgeSupport577_suffix_013 : List Nat := []
def ridgeSupport577_suffix_012 : List Nat := ridgeSupport577_012 ++ ridgeSupport577_suffix_013
def ridgeSupport577_suffix_011 : List Nat := ridgeSupport577_011 ++ ridgeSupport577_suffix_012
def ridgeSupport577_suffix_010 : List Nat := ridgeSupport577_010 ++ ridgeSupport577_suffix_011
def ridgeSupport577_suffix_009 : List Nat := ridgeSupport577_009 ++ ridgeSupport577_suffix_010
def ridgeSupport577_suffix_008 : List Nat := ridgeSupport577_008 ++ ridgeSupport577_suffix_009
def ridgeSupport577_suffix_007 : List Nat := ridgeSupport577_007 ++ ridgeSupport577_suffix_008
def ridgeSupport577_suffix_006 : List Nat := ridgeSupport577_006 ++ ridgeSupport577_suffix_007
def ridgeSupport577_suffix_005 : List Nat := ridgeSupport577_005 ++ ridgeSupport577_suffix_006
def ridgeSupport577_suffix_004 : List Nat := ridgeSupport577_004 ++ ridgeSupport577_suffix_005
def ridgeSupport577_suffix_003 : List Nat := ridgeSupport577_003 ++ ridgeSupport577_suffix_004
def ridgeSupport577_suffix_002 : List Nat := ridgeSupport577_002 ++ ridgeSupport577_suffix_003
def ridgeSupport577_suffix_001 : List Nat := ridgeSupport577_001 ++ ridgeSupport577_suffix_002
def ridgeSupport577_suffix_000 : List Nat := ridgeSupport577_000 ++ ridgeSupport577_suffix_001
theorem ridgeSupport577_source : candidateSupports 577 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport577_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
