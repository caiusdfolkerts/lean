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
def ridgeSupport577_000 : List Nat := [11,17,23,28,29,128,129,130,131,132,133,200,201,202,203,204,205,268,270,272,273,275,277,278,282,287,289,291,293,294,296,298]
def ridgeSupport577_001 : List Nat := [299,303,308,356,358,360,361,363,365,366,370,375,377,379,381,382,384,386,387,391,396,440,442,444,445,447,449,450,454,459,461,463]
def ridgeSupport577_002 : List Nat := [465,466,468,470,471,475,480,503,504,506,507,510,511,512,514,515,517,524,525,1418,1423,1424,1429,1440,1441,1454,1455,1488,1489,1502,1503,1508]
def ridgeSupport577_003 : List Nat := [1510,1516,1517,1522,1523,1529,1531,1536,1537,1538,1543,1544,1549,1550,1551,1584,1585,1598,1599,1608,1609,1622,1623,1658,1663,1664,1669,1680,1681,1694,1695,1728]
def ridgeSupport577_004 : List Nat := [1729,1742,1743,1748,1750,1756,1757,1762,1763,1769,1771,1776,1777,1778,1783,1784,1789,1790,1791,1824,1825,1838,1839,1848,1849,1862,1863,2192,2197,2204,2209,2236]
def ridgeSupport577_005 : List Nat := [2237,2248,2249,2264,2269,2276,2281,2308,2309,2320,2321,2426,2431,2432,2437,2448,2449,2462,2463,2496,2497,2510,2511,2516,2518,2524,2525,2530,2531,2537,2539,2544]
def ridgeSupport577_006 : List Nat := [2545,2546,2551,2552,2557,2558,2559,2592,2593,2606,2607,2616,2617,2630,2631,2960,2965,2972,2977,3004,3005,3016,3017,3032,3037,3044,3049,3076,3077,3088,3089,3682]
def ridgeSupport577_007 : List Nat := [3683,3686,3687,5133,5135,5140,5142,5145,5147,5152,5154,5175,5178,5181,5184,5193,5195,5200,5202,5223,5226,5229,5232,5376,5377,5412,5413,5508,5509,5852,5854,5873]
def ridgeSupport577_008 : List Nat := [5875,5892,5893,5895,5896,5897,5899,5900,5902,5921,5923,5940,5941,5943,5944,5945,5947,6027,6028,6029,6030,6045,6046,6047,6048,6068,6070,6089,6091,6108,6109,6111]
def ridgeSupport577_009 : List Nat := [6112,6113,6115,6195,6196,6197,6198,6213,6214,6215,6216]
def ridgeSupport577_code : Nat := 0x612308f846c22e0db06b834c19df8efc37e0befdf76fb97cbbe4dedaf697a0bcfde7af3b78ebc6de32f1773bb9cdce2e6f735b9a5c8ee4370eb865c2ee13708b83dc16e096f3b78db7adb9585ac25496a49501a8051c28db46aa33d14a8a144ba24d10287b43aa1bd08a84141ba0cd05a82940fa06b99dccce637313045820c056022fa57c8bdd5ec2f25790bbd5de2e85738b955c8291d48ca3951c28bd45ca2151027fd3fc9fd4fc27dd3e49f14f827ad3d29e34f127753b89d64ea273d39c9c14e0267d33c9914c8261530097f4bd244522090548223a51c88dd46c23251908bd45e22851388954481d1ce8c73939c1cbce5c7213901bfcdfc6fd37c1bdcde46f13781bacdd26e33711b74db86d636a1b3cd9c6c13601a7cd3c6913481a14d0067f33d195ccac64932418fcc7c631318183cc1c60d304181cc0460130017ecbf25f32f917b4bd85e62f2177cbbc5d12e816bcb5c5a12d01654b2058f2c5083441820510188084001ff0ff07ec3f41f80fb87803b61d70eb07503a41d10e787343961c60e1070437e1bd0de06e837018c0c3860c3041800bf05f42f61790bb85c82dc16d0b585a42d01660b204d025e12b09504a024c125091848423e11a08b045422611108804382180cd066032c1940c90640214108083041020410001d00e005c02200b
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
def ridgeSupport577_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport577_code
def ridgeSupport577_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport577_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
