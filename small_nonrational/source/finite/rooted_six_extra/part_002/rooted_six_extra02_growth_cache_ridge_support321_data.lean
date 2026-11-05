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
def ridgeSupport321_000 : List Nat := [10,16,22,27,29,116,117,118,119,120,121,188,189,190,191,192,193,247,249,251,252,254,256,257,261,266,290,291,292,295,296,297]
def ridgeSupport321_001 : List Nat := [299,304,306,335,337,339,340,342,344,345,349,354,378,379,380,383,384,385,387,392,394,419,421,423,424,426,428,429,433,438,462,463]
def ridgeSupport321_002 : List Nat := [464,467,468,469,471,476,478,503,505,506,508,509,511,513,514,516,517,521,522,1419,1421,1430,1435,1438,1439,1448,1449,1486,1487,1496,1497,1509]
def ridgeSupport321_003 : List Nat := [1512,1518,1519,1523,1525,1528,1529,1534,1535,1539,1541,1544,1545,1550,1555,1582,1583,1592,1593,1606,1607,1616,1617,1659,1661,1670,1675,1678,1679,1688,1689,1726]
def ridgeSupport321_004 : List Nat := [1727,1736,1737,1749,1752,1758,1759,1763,1765,1768,1769,1774,1775,1779,1781,1784,1785,1790,1795,1822,1823,1832,1833,1846,1847,1856,1857,2120,2125,2132,2137,2164]
def ridgeSupport321_005 : List Nat := [2165,2176,2177,2265,2267,2277,2279,2310,2311,2322,2323,2427,2429,2438,2443,2446,2447,2456,2457,2494,2495,2504,2505,2517,2520,2526,2527,2531,2533,2536,2537,2542]
def ridgeSupport321_006 : List Nat := [2543,2547,2549,2552,2553,2558,2563,2590,2591,2600,2601,2614,2615,2624,2625,2888,2893,2900,2905,2932,2933,2944,2945,3033,3035,3045,3047,3078,3079,3090,3091,3666]
def ridgeSupport321_007 : List Nat := [3667,3670,3671,5132,5137,5138,5142,5144,5149,5150,5154,5169,5172,5180,5182,5192,5197,5198,5202,5217,5220,5228,5230,5374,5375,5410,5411,5506,5507,5853,5856,5867]
def ridgeSupport321_008 : List Nat := [5869,5890,5891,5894,5896,5897,5898,5901,5904,5915,5917,5938,5939,5942,5944,5945,5946,6009,6010,6011,6012,6044,6046,6048,6049,6069,6072,6083,6085,6106,6107,6110]
def ridgeSupport321_009 : List Nat := [6112,6113,6114,6177,6178,6179,6180,6212,6214,6216,6217]
def ridgeSupport321_code : Nat := 0x6127091846c226093047822c10df8afc37e0bef5f6efb57c5be1dee2f6b7a1bd05e7af3977cbbdddeaef373ab9cdce2e6d733b995c76e37710b86dc2ae13708b835c0ee056edb75db82dbb583ac1548ea454ffa7f51ba8d9464a30d14a89d44da2450fa879434a18d08a83d41da0c505a825411a06395dcace53729304d824c076032f9d7cabdb5ecae05700b755ba2d656a8b4d5a42905480a3751b28a5450a1f50f280d3fc9f94fc27d53e69ef4f727a53d09e54f1a77d3bc9d84eaa7253909bf4df266533098f4c7262d30c97d4bda44d224907483239d1ca8db46ca20510087543a21650a884d4241d04e8073739b1ca4e5071f38f1c0cdfc6f937c1bd4de66ef3771ba4dd06e53719b7cdbc6d836a9b24d906bf35f1a64d3068f3471a2cd0c67d33d9944ca064732318e4c7062f317184cc1c6093041814c065ff2ff17e4bf05f52f997bcbdc5e82f29764bb05cf2e716a4b5059f2cf166cb2c58d2c5882841220510208084021ff0fe87f03f41f90fb87783b81d70ea87503a61d00e7873836c1b10d686b03541a80d3869434618a0c4060c3021800bf85f02f617a0b105742b21580ab05502a61510a784c826012b09484a024e124091848821410508084001fc0fc07d83e41ee0c106002fc17c0bd05e01e40f007703b01d40e801d00d805802000a
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
def ridgeSupport321_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport321_code
def ridgeSupport321_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport321_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
