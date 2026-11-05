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
def ridgeSupport321_000 : List Nat := [10,16,22,27,29,116,117,118,119,120,121,188,189,190,191,192,193,247,249,251,252,254,256,257,261,266,290,291,292,295,296,297]
def ridgeSupport321_001 : List Nat := [299,304,306,335,337,339,340,342,344,345,349,354,378,379,380,383,384,385,387,392,394,419,421,423,424,426,428,429,433,438,462,463]
def ridgeSupport321_002 : List Nat := [464,467,468,469,471,476,478,503,505,506,508,509,511,513,514,516,517,521,522,1419,1421,1430,1435,1438,1439,1448,1449,1486,1487,1496,1497,1509]
def ridgeSupport321_003 : List Nat := [1512,1518,1519,1523,1525,1528,1529,1534,1535,1539,1541,1544,1545,1550,1555,1582,1583,1592,1593,1606,1607,1616,1617,1659,1661,1670,1675,1678,1679,1688,1689,1726]
def ridgeSupport321_004 : List Nat := [1727,1736,1737,1749,1752,1758,1759,1763,1765,1768,1769,1774,1775,1779,1781,1784,1785,1790,1795,1822,1823,1832,1833,1846,1847,1856,1857,2120,2125,2132,2137,2164]
def ridgeSupport321_005 : List Nat := [2165,2176,2177,2265,2267,2277,2279,2310,2311,2322,2323,2427,2429,2438,2443,2446,2447,2456,2457,2494,2495,2504,2505,2517,2520,2526,2527,2531,2533,2536,2537,2542]
def ridgeSupport321_006 : List Nat := [2543,2547,2549,2552,2553,2558,2563,2590,2591,2600,2601,2614,2615,2624,2625,2888,2893,2900,2905,2932,2933,2944,2945,3033,3035,3045,3047,3078,3079,3090,3091,3666]
def ridgeSupport321_007 : List Nat := [3667,3670,3671,5145,5148,5151,5155,5158,5159,5168,5169,5181,5184,5190,5191,5195,5197,5200,5201,5206,5207,5211,5213,5216,5217,5222,5227,5238,5239,5248,5249,5252]
def ridgeSupport321_008 : List Nat := [5254,5258,5259,5277,5280,5283,5287,5290,5291,5300,5301,5313,5316,5322,5323,5327,5329,5332,5333,5338,5339,5343,5345,5348,5349,5354,5359,5370,5371,5380,5381,5384]
def ridgeSupport321_009 : List Nat := [5386,5390,5391,5540,5545,5548,5549,5552,5557,5560,5561,5565,5568,5571,5574,5649,5651,5658,5659,5661,5663,5670,5671,5672,5674,5678,5680,5757,5760,5763,5767,5770]
def ridgeSupport321_010 : List Nat := [5771,5780,5781,5793,5796,5802,5803,5807,5809,5812,5813,5818,5819,5823,5825,5828,5829,5834,5839,5850,5851,5860,5861,5864,5866,5870,5871,6020,6025,6028,6029,6032]
def ridgeSupport321_011 : List Nat := [6037,6040,6041,6045,6048,6051,6054,6129,6131,6138,6139,6141,6143,6150,6151,6152,6154,6158,6160,6494,6495,7364,7369,7370,7374,7376,7381,7382,7386,7401,7404,7412]
def ridgeSupport321_012 : List Nat := [7414,7424,7429,7430,7434,7449,7452,7460,7462,7606,7607,7642,7643,7738,7739]
def ridgeSupport321_code : Nat := 0x78efc75ddbeed76dfb6dd26e927473a33d0ae837417a01cf6e7a73b39d3cdae6b73579a1ccee65732798995fcaf604301d80ac04601f00d7ffbfedfeeff57f3bf8de9af477a0bcede66f31795bc85e36f19789bc25bbeddd6eab745b96dc96dbb6d5b3ed956c5b625b06d7f6bbb5d5ad6d696b1b57daaed556a4b50da56d2968bb455a1ed07680b3ed8c2c5d62ab14589ec4d61fb0ed86ec35613b08d71ab875c0aded6e6b715b5ad856b6b595a9ad2543ea1d50aa845416a094fba7d53be9d54e5a7253869bf4dba6d53569a94d1a67d32e9954c4a60d2d69694aba55529e9474a0a4ed22e915486a425206901477a3b51ae8cd461a3051768b7457a2b51468a144da25d11e88d440a1ed0c6861427a13508e83f41ca0cb95dcace53729304d824c076032f9d7cabdb5ecae05700b755ba2d656a8b4d5a42905480a3751b28a5450a1f50f280d3fc9f94fc27d53e69ef4f727a53d09e54f1a77d3bc9d84eaa7253909bf4df266533098f4c7262d30c97d4bda44d224907483239d1ca8db46ca20510087543a21650a884d4241d04e8073739b1ca4e5071f38f1c0cdfc6f937c1bd4de66ef3771ba4dd06e53719b7cdbc6d836a9b24d906bf35f1a64d3068f3471a2cd0c67d33d9944ca064732318e4c7062f317184cc1c6093041814c065ff2ff17e4bf05f52f997bcbdc5e82f29764bb05cf2e716a4b5059f2cf166cb2c58d2c5882841220510208084021ff0fe87f03f41f90fb87783b81d70ea87503a61d00e7873836c1b10d686b03541a80d3869434618a0c4060c3021800bf85f02f617a0b105742b21580ab05502a61510a784c826012b09484a024e124091848821410508084001fc0fc07d83e41ee0c106002fc17c0bd05e01e40f007703b01d40e801d00d805802000a
def ridgeSupport321_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport321_code
def ridgeSupport321_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport321_code
def ridgeSupport321_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport321_code
def ridgeSupport321_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport321_code
def ridgeSupport321_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport321_code
def ridgeSupport321_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport321_code
def ridgeSupport321_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport321_code
def ridgeSupport321_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport321_code
def ridgeSupport321_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport321_code
def ridgeSupport321_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport321_code
def ridgeSupport321_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport321_code
def ridgeSupport321_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport321_code
def ridgeSupport321_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport321_code
def ridgeSupport321_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport321_code
def ridgeSupport321_suffix_013 : List Nat := []
def ridgeSupport321_suffix_012 : List Nat := ridgeSupport321_012 ++ ridgeSupport321_suffix_013
def ridgeSupport321_suffix_011 : List Nat := ridgeSupport321_011 ++ ridgeSupport321_suffix_012
def ridgeSupport321_suffix_010 : List Nat := ridgeSupport321_010 ++ ridgeSupport321_suffix_011
def ridgeSupport321_suffix_009 : List Nat := ridgeSupport321_009 ++ ridgeSupport321_suffix_010
def ridgeSupport321_suffix_008 : List Nat := ridgeSupport321_008 ++ ridgeSupport321_suffix_009
def ridgeSupport321_suffix_007 : List Nat := ridgeSupport321_007 ++ ridgeSupport321_suffix_008
def ridgeSupport321_suffix_006 : List Nat := ridgeSupport321_006 ++ ridgeSupport321_suffix_007
def ridgeSupport321_suffix_005 : List Nat := ridgeSupport321_005 ++ ridgeSupport321_suffix_006
def ridgeSupport321_suffix_004 : List Nat := ridgeSupport321_004 ++ ridgeSupport321_suffix_005
def ridgeSupport321_suffix_003 : List Nat := ridgeSupport321_003 ++ ridgeSupport321_suffix_004
def ridgeSupport321_suffix_002 : List Nat := ridgeSupport321_002 ++ ridgeSupport321_suffix_003
def ridgeSupport321_suffix_001 : List Nat := ridgeSupport321_001 ++ ridgeSupport321_suffix_002
def ridgeSupport321_suffix_000 : List Nat := ridgeSupport321_000 ++ ridgeSupport321_suffix_001
theorem ridgeSupport321_source : candidateSupports 321 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport321_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
