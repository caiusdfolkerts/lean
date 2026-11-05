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
def ridgeSupport385_000 : List Nat := [12,18,24,27,30,140,141,142,143,144,145,212,213,214,215,216,217,246,250,251,252,253,255,256,263,265,311,312,313,316,317,318]
def ridgeSupport385_001 : List Nat := [320,325,327,334,338,339,340,341,343,344,351,353,399,400,401,404,405,406,408,413,415,418,422,423,424,425,427,428,435,437,483,484]
def ridgeSupport385_002 : List Nat := [485,488,489,490,492,497,499,502,505,506,507,510,511,512,514,519,520,522,523,1413,1415,1432,1434,1444,1445,1450,1451,1492,1493,1498,1499,1512]
def ridgeSupport385_003 : List Nat := [1513,1515,1518,1521,1524,1526,1527,1533,1535,1540,1541,1546,1547,1552,1554,1588,1589,1594,1595,1612,1613,1618,1619,1653,1655,1672,1674,1684,1685,1690,1691,1732]
def ridgeSupport385_004 : List Nat := [1733,1738,1739,1752,1753,1755,1758,1761,1764,1766,1767,1773,1775,1780,1781,1786,1787,1792,1794,1828,1829,1834,1835,1852,1853,1858,1859,2122,2124,2134,2136,2162]
def ridgeSupport385_005 : List Nat := [2163,2174,2175,2337,2339,2349,2351,2382,2383,2394,2395,2421,2423,2440,2442,2452,2453,2458,2459,2500,2501,2506,2507,2520,2521,2523,2526,2529,2532,2534,2535,2541]
def ridgeSupport385_006 : List Nat := [2543,2548,2549,2554,2555,2560,2562,2596,2597,2602,2603,2620,2621,2626,2627,2890,2892,2902,2904,2930,2931,2942,2943,3105,3107,3117,3119,3150,3151,3162,3163,3698]
def ridgeSupport385_007 : List Nat := [3699,3702,3703,5145,5147,5152,5154,5164,5165,5170,5171,5184,5185,5187,5190,5193,5196,5198,5199,5205,5207,5212,5213,5218,5219,5224,5226,5232,5233,5246,5247,5255]
def ridgeSupport385_008 : List Nat := [5257,5258,5260,5277,5279,5284,5286,5296,5297,5302,5303,5316,5317,5319,5322,5325,5328,5330,5331,5337,5339,5344,5345,5350,5351,5356,5358,5364,5365,5378,5379,5387]
def ridgeSupport385_009 : List Nat := [5389,5390,5392,5542,5544,5546,5547,5554,5556,5558,5559,5567,5569,5573,5575,5703,5705,5712,5713,5715,5717,5724,5725,5726,5728,5732,5734,5757,5759,5764,5766,5776]
def ridgeSupport385_010 : List Nat := [5777,5782,5783,5796,5797,5799,5802,5805,5808,5810,5811,5817,5819,5824,5825,5830,5831,5836,5838,5844,5845,5858,5859,5867,5869,5870,5872,6022,6024,6026,6027,6034]
def ridgeSupport385_011 : List Nat := [6036,6038,6039,6047,6049,6053,6055,6183,6185,6192,6193,6195,6197,6204,6205,6206,6208,6212,6214,6502,6503,7364,7366,7373,7375,7376,7378,7385,7387,7403,7405,7418]
def ridgeSupport385_012 : List Nat := [7420,7424,7426,7433,7435,7451,7453,7466,7468,7610,7611,7646,7647,7742,7743]
def ridgeSupport385_code : Nat := 0x78ffc7dddfeef76efb75d2ce957477a37d0be84f40ba01cfce7d73b79d7cdbe6cf34b9a1ccfe66f31b989967cb3611b089840c1f60f7079835c19e0c7061829c13de9ef4b7a1bcfde5ef2d794bc95e2ef15788bc35bc2ddd6edb75db8edc56d5b6a5b3ad996c7b635b06d816bbb5cdaced656b0b56daaad4f6a5b525a5ed2d691b485a1ad0967fb3ed99acc9660b2f5976cb9655b29d946ca1649b23d71eb8b5c1adfd6deb6d5b4ad956aeb555a8ad35442a1d50da85d40ea054f5a7a53ba9d94e7a7353869c14dba6cd34e9a54d0a66d32a98f4c5a6252de96d4b1a58529a94949fa4ed232915489a43d1fe8fd471a3851aa8d1463a3151768b9457a2ad13e89d44ca24d11a887441a2050ce86542da16508a84141ba0cb9ddcece73739316d8b4c4f62730bd85ac23610adfd6fcb735b92d616acb4c5a5290d484a3d51e28ad454a2551228094009fb4fd27d53e89ef4f6a79d3cc9e44f0a7793b69d94ec272d3949c54e2266d3349954ca26293109774baa56d2b494f4a724bd25a923490a1fd0fc87343921610ac84c4251d0ce8473d39e1cace547253921c08e006fb37d1bd4de86ef3769b9cdcc6e43709b78db66d936c1b2cd946c53621a6cd3469534a1a28d1067733a994cca464d32618ecc7463531a1848c2060b3051814c085ff2fe97dcbec5f42f897b8bd65e92f4176cbb45d52ea16acb545a52d21668b305872c2882c41420810388084001ff0ff07ec3f41f90fb07cc3e21ec0f507a43d01e50f2078c36a1b30d606ac3521a80d3869834419f0ce866032c1950ca064432018f0b0857c2b01570aa85502a61520a7051c28a14009f04f427813909c04dc21210708003fc1fa0fc07d83e81ec0d906c035c1ac0d506a024412008f047023411801e00d806002400c
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
def ridgeSupport385_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport385_code
def ridgeSupport385_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport385_code
def ridgeSupport385_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport385_code
def ridgeSupport385_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport385_code
def ridgeSupport385_suffix_013 : List Nat := []
def ridgeSupport385_suffix_012 : List Nat := ridgeSupport385_012 ++ ridgeSupport385_suffix_013
def ridgeSupport385_suffix_011 : List Nat := ridgeSupport385_011 ++ ridgeSupport385_suffix_012
def ridgeSupport385_suffix_010 : List Nat := ridgeSupport385_010 ++ ridgeSupport385_suffix_011
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
    (PackedRawNatGrowth.readList 13 399 ridgeSupport385_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
