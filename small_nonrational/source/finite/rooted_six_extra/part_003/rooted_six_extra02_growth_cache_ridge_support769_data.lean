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
def ridgeSupport769_000 : List Nat := [14,20,26,29,30,164,165,166,167,168,169,236,237,238,239,240,241,288,292,293,294,295,297,298,305,307,309,313,314,315,316,318]
def ridgeSupport769_001 : List Nat := [319,326,328,376,380,381,382,383,385,386,393,395,397,401,402,403,404,406,407,414,416,460,464,465,466,467,469,470,477,479,481,485]
def ridgeSupport769_002 : List Nat := [486,487,488,490,491,498,500,502,503,507,508,509,510,512,513,521,523,524,526,1414,1416,1420,1422,1452,1453,1458,1459,1500,1501,1506,1507,1508]
def ridgeSupport769_003 : List Nat := [1509,1514,1515,1520,1522,1526,1528,1534,1536,1540,1542,1548,1549,1554,1555,1596,1597,1602,1603,1620,1621,1626,1627,1654,1656,1660,1662,1692,1693,1698,1699,1740]
def ridgeSupport769_004 : List Nat := [1741,1746,1747,1748,1749,1754,1755,1760,1762,1766,1768,1774,1776,1780,1782,1788,1789,1794,1795,1836,1837,1842,1843,1860,1861,1866,1867,2266,2268,2278,2280,2306]
def ridgeSupport769_005 : List Nat := [2307,2318,2319,2338,2340,2350,2352,2378,2379,2390,2391,2422,2424,2428,2430,2460,2461,2466,2467,2508,2509,2514,2515,2516,2517,2522,2523,2528,2530,2534,2536,2542]
def ridgeSupport769_006 : List Nat := [2544,2548,2550,2556,2557,2562,2563,2604,2605,2610,2611,2628,2629,2634,2635,3034,3036,3046,3048,3074,3075,3086,3087,3106,3108,3118,3120,3146,3147,3158,3159,3730]
def ridgeSupport769_007 : List Nat := [3731,3734,3735,5135,5137,5139,5141,5147,5149,5151,5153,5183,5185,5189,5191,5195,5197,5199,5201,5231,5233,5237,5239,5382,5383,5418,5419,5514,5515,5864,5866,5870]
def ridgeSupport769_008 : List Nat := [5872,5888,5889,5891,5893,5894,5895,5912,5914,5918,5920,5936,5937,5939,5941,5942,5943,6044,6045,6047,6049,6062,6063,6065,6067,6080,6082,6086,6088,6104,6105,6107]
def ridgeSupport769_009 : List Nat := [6109,6110,6111,6212,6213,6215,6217,6230,6231,6233,6235]
def ridgeSupport769_code : Nat := 0x616f0b3857c2b612708f845c225f7efbd7ddbeddf66fb17c8be35f0af817b3bd8debef5d7a1bcfde76f39737b9b5cd6e67731b985c82e3d71ab8c5c1ee0d705b81dc06e016f0b775baadd158bac554aea55507a8351de8eb471a37d14689f44da25d11e88b441a1fd08683f41da0dd056827411a07ba5dd2ce93749315d8acc4b62530c185cc24611303d81cc036012fa17ccbdc5ed292d494a4552228cd464a2d516280d4049fd4fe27d93e89f04f727a13cc9e24f0276d3b49d54ea274d3a49cd4e6268d34499d4ce25f92f89784bb255d2ac94b4a524c125c924491243d21c90348123a11cc8dc46d1d2ce947453a21ccce6472d3961c0ce046fd37e1bd8de86f03771ba0dcc6e23701b6cdb46d536a1b4cda46cd3661a8cd4469d34e19f8cf867833b196ccb465532a190cc8463d31e184cc2460d3061818c086002ff17e0bec5f22f817acbd45e52f2178cbc45dd2ee16ccb645ad2d61638b185882c3083841820b10488044001fe0fe87f03f61f70fb07d03e41eb0f507a03ce1e60f287843be1dd0eb07543a61d20e887403981a00cf065c32c1940c9864832218d0c586243041810bf85f82fa17c0bc052028c13f09f04f027613a09c84d426613109504a424e12609284902400f107803bc1dc0ed07602a41500a7053029414801e00e806802800e
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
def ridgeSupport769_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport769_code
def ridgeSupport769_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport769_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
