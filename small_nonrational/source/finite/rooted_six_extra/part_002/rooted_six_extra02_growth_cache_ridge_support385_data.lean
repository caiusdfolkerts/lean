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
def ridgeSupport385_000 : List Nat := [12,18,24,27,30,140,141,142,143,144,145,212,213,214,215,216,217,246,250,251,252,253,255,256,263,265,311,312,313,316,317,318]
def ridgeSupport385_001 : List Nat := [320,325,327,334,338,339,340,341,343,344,351,353,399,400,401,404,405,406,408,413,415,418,422,423,424,425,427,428,435,437,483,484]
def ridgeSupport385_002 : List Nat := [485,488,489,490,492,497,499,502,505,506,507,510,511,512,514,519,520,522,523,1413,1415,1432,1434,1444,1445,1450,1451,1492,1493,1498,1499,1512]
def ridgeSupport385_003 : List Nat := [1513,1515,1518,1521,1524,1526,1527,1533,1535,1540,1541,1546,1547,1552,1554,1588,1589,1594,1595,1612,1613,1618,1619,1653,1655,1672,1674,1684,1685,1690,1691,1732]
def ridgeSupport385_004 : List Nat := [1733,1738,1739,1752,1753,1755,1758,1761,1764,1766,1767,1773,1775,1780,1781,1786,1787,1792,1794,1828,1829,1834,1835,1852,1853,1858,1859,2122,2124,2134,2136,2162]
def ridgeSupport385_005 : List Nat := [2163,2174,2175,2337,2339,2349,2351,2382,2383,2394,2395,2421,2423,2440,2442,2452,2453,2458,2459,2500,2501,2506,2507,2520,2521,2523,2526,2529,2532,2534,2535,2541]
def ridgeSupport385_006 : List Nat := [2543,2548,2549,2554,2555,2560,2562,2596,2597,2602,2603,2620,2621,2626,2627,2890,2892,2902,2904,2930,2931,2942,2943,3105,3107,3117,3119,3150,3151,3162,3163,3698]
def ridgeSupport385_007 : List Nat := [3699,3702,3703,5132,5134,5141,5143,5144,5146,5153,5155,5171,5173,5186,5188,5192,5194,5201,5203,5219,5221,5234,5236,5378,5379,5414,5415,5510,5511,5859,5862,5865]
def ridgeSupport385_008 : List Nat := [5868,5888,5890,5892,5893,5896,5899,5907,5910,5913,5916,5936,5938,5940,5941,5944,5947,6008,6009,6011,6013,6062,6064,6066,6067,6075,6078,6081,6084,6104,6106,6108]
def ridgeSupport385_009 : List Nat := [6109,6112,6115,6176,6177,6179,6181,6230,6232,6234,6235]
def ridgeSupport385_code : Nat := 0x616f0b5858c2b6097047821c105f8efc17ddbee5f6afb17c4be0defaf777b3bd95ec2f5d77dbbddde6ef173bb9c5cd6e69732b985c72e33716b89dc2ee11705b825c0ae016ecb74db9adc7587ac3549ea4d503a8151d28e5465a31d14e8a344aa245112885435a19d08e84341aa0c505e82b40ea0639ddcece73739316d8b4c4f62730bd85ac23610adfd6fcb735b92d616acb4c5a5290d484a3d51e28ad454a2551228094009fb4fd27d53e89ef4f6a79d3cc9e44f0a7793b69d94ec272d3949c54e2266d3349954ca26293109774baa56d2b494f4a724bd25a923490a1fd0fc87343921610ac84c4251d0ce8473d39e1cace547253921c08e006fb37d1bd4de86ef3769b9cdcc6e43709b78db66d936c1b2cd946c53621a6cd3469534a1a28d1067733a994cca464d32618ecc7463531a1848c2060b3051814c085ff2fe97dcbec5f42f897b8bd65e92f4176cbb45d52ea16acb545a52d21668b305872c2882c41420810388084001ff0ff07ec3f41f90fb07cc3e21ec0f507a43d01e50f2078c36a1b30d606ac3521a80d3869834419f0ce866032c1950ca064432018f0b0857c2b01570aa85502a61520a7051c28a14009f04f427813909c04dc21210708003fc1fa0fc07d83e81ec0d906c035c1ac0d506a024412008f047023411801e00d806002400c
def ridgeSupport385_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport385_code
def ridgeSupport385_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport385_code
def ridgeSupport385_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport385_code
def ridgeSupport385_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport385_code
def ridgeSupport385_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport385_code
def ridgeSupport385_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport385_code
def ridgeSupport385_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport385_code
def ridgeSupport385_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport385_code
def ridgeSupport385_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport385_code
def ridgeSupport385_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport385_code
def ridgeSupport385_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport385_code
def ridgeSupport385_suffix_010 : List Nat := []
def ridgeSupport385_suffix_009 : List Nat := ridgeSupport385_009 ++ ridgeSupport385_suffix_010
def ridgeSupport385_suffix_008 : List Nat := ridgeSupport385_008 ++ ridgeSupport385_suffix_009
def ridgeSupport385_suffix_007 : List Nat := ridgeSupport385_007 ++ ridgeSupport385_suffix_008
def ridgeSupport385_suffix_006 : List Nat := ridgeSupport385_006 ++ ridgeSupport385_suffix_007
def ridgeSupport385_suffix_005 : List Nat := ridgeSupport385_005 ++ ridgeSupport385_suffix_006
def ridgeSupport385_suffix_004 : List Nat := ridgeSupport385_004 ++ ridgeSupport385_suffix_005
def ridgeSupport385_suffix_003 : List Nat := ridgeSupport385_003 ++ ridgeSupport385_suffix_004
def ridgeSupport385_suffix_002 : List Nat := ridgeSupport385_002 ++ ridgeSupport385_suffix_003
def ridgeSupport385_suffix_001 : List Nat := ridgeSupport385_001 ++ ridgeSupport385_suffix_002
def ridgeSupport385_suffix_000 : List Nat := ridgeSupport385_000 ++ ridgeSupport385_suffix_001
theorem ridgeSupport385_source : candidateSupports 385 =
    (PackedRawNatGrowth.readList 13 299 ridgeSupport385_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
