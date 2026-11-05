module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport88_000 : List Nat := [45,95,99,100,101,779,782,784,787,789,791,794,796,799,801,803,806,808,811,813,1466,1468,1469,1472,1474,1478,1480,1481,1484,1486,1490,1492]
def ridgeSupport88_001 : List Nat := [1493,1496,1498,1538,1539,1541,1542,1543,1544,1546,1547,1549,1550,1552,1553,1559,1560,1562,1563,1564,1565,1567,1568,1570,1571,1573,1574,1580,1581,1583,1584,1585]
def ridgeSupport88_002 : List Nat := [1586,1588,1589,1591,1592,1594,1595,4936,4937,4938,4939,4940,4941,4942,4943,4948,4949,4954,4955,4960,4961,4962,4963,4964,4965,4966,4967,4972,4973,4978,4979,4984]
def ridgeSupport88_003 : List Nat := [4985,4986,4987,4988,4989,5008,5009,5010,5011,5012,5013,5032,5033,5034,5035,5036,5037,5056,5057,5058,5059,5060,5061,5080,5081,5082,5083,5084,5085,5104,5105,5106]
def ridgeSupport88_004 : List Nat := [5107,5108,5109,5128,5129,5130,5131,5132,5133,5137,5139,5143,5145,5149,5151,5194,5195,5206,5207,5215,5217,5221,5223,5230,5231,5242,5243,5266,5267,5278,5279,5287]
def ridgeSupport88_005 : List Nat := [5289,5293,5295,5302,5303,5314,5315,5338,5339,5350,5351,5359,5361,5365,5367,5374,5375,5386,5387,6760,6761,6772,6773,6796,6797,6808,6809,6823,6825,6829,6831,6832]
def ridgeSupport88_006 : List Nat := [6833,6844,6845,6868,6869,6880,6881,6895,6897,6901,6903,6904,6905,6916,6917,6940,6941,6952,6953,6967,6969,6973,6975,7432,7433,7434,7435,7436,7437,8344,8345,8346]
def ridgeSupport88_007 : List Nat := [8347,8348,8349,8368,8369,8370,8371,8372,8373,8380,8381,8382,8383,8384,8385,8392,8393,8398,8399,8410,8411,8416,8417,8428,8429,8434,8435,8761,8763,8767,8769,8779]
def ridgeSupport88_008 : List Nat := [8781,8785,8787,8797,8799,8803,8805]
def ridgeSupport88_code : Nat := 0x2265898e25f8976253894624d892e24188fe23b88e60f383ca0ed83b20e183820db836a0cf833a0c983220c183020bf82fa0bd82f20b582d20b382ca0b182c209d827209b826a0998261d0d7431d0b7429d097421b3f6cf5b396cddb296ca1b1d6c71b056c11af96be1af76bd5af16bbdae16b81ad56b51abd6af1ab16ac1aaf6ab5aa96a9da996a61a8d6a31a7569d1a6969a150b54294ff53f94f753d54f153bd4e753994db53694c353094b752d94af52b54a9529d49f5279493524947b51e946f51b94675195461517d457515944b512941f5075419505d413504540d503140b502940950213f54fd13f34fc93f14fc13dd4f713db4f693d94f613c54f113c34f093c14f013ad4eb13ab4ea93a94ea13954e513934e493914e4137d4df137b4de93794de13734dc936d4db13674d993654d913634d893614d8135b4d693554d5134f4d3934d4d3134b4d293494d2063b18e863818dc63518d063218c463018bc62d18b062618946231888620187c61d187061b1868618185c611184060e183460b1828608181c606181460318085da17605d517505d217385cc17245c817185c217005bd16f05ba0cb432b0ca03260c8c3210c7c31c0c683170c543130c4030e0c2c0650190063017c02d
def ridgeSupport88_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport88_code
def ridgeSupport88_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport88_code
def ridgeSupport88_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport88_code
def ridgeSupport88_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport88_code
def ridgeSupport88_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport88_code
def ridgeSupport88_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport88_code
def ridgeSupport88_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport88_code
def ridgeSupport88_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport88_code
def ridgeSupport88_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport88_code
def ridgeSupport88_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport88_code
def ridgeSupport88_suffix_009 : List Nat := []
def ridgeSupport88_suffix_008 : List Nat := ridgeSupport88_008 ++ ridgeSupport88_suffix_009
def ridgeSupport88_suffix_007 : List Nat := ridgeSupport88_007 ++ ridgeSupport88_suffix_008
def ridgeSupport88_suffix_006 : List Nat := ridgeSupport88_006 ++ ridgeSupport88_suffix_007
def ridgeSupport88_suffix_005 : List Nat := ridgeSupport88_005 ++ ridgeSupport88_suffix_006
def ridgeSupport88_suffix_004 : List Nat := ridgeSupport88_004 ++ ridgeSupport88_suffix_005
def ridgeSupport88_suffix_003 : List Nat := ridgeSupport88_003 ++ ridgeSupport88_suffix_004
def ridgeSupport88_suffix_002 : List Nat := ridgeSupport88_002 ++ ridgeSupport88_suffix_003
def ridgeSupport88_suffix_001 : List Nat := ridgeSupport88_001 ++ ridgeSupport88_suffix_002
def ridgeSupport88_suffix_000 : List Nat := ridgeSupport88_000 ++ ridgeSupport88_suffix_001
theorem ridgeSupport88_source : candidateSupports 88 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport88_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
