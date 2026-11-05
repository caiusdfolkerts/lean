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
def ridgeSupport296_000 : List Nat := [67,97,106,108,110,1057,1058,1060,1065,1067,1081,1082,1084,1089,1091,1104,1107,1109,1112,1114,1477,1480,1481,1484,1487,1501,1504,1505,1508,1511,1526,1527]
def ridgeSupport296_001 : List Nat := [1530,1531,1536,1621,1622,1624,1625,1628,1629,1630,1632,1633,1635,1640,1641,1663,1665,1666,1668,1669,1671,1673,1674,1676,1677,1680,1681,1684,1686,1687,1689,1690]
def ridgeSupport296_002 : List Nat := [1692,1694,1695,1697,1698,1701,1702,5706,5707,5712,5713,5716,5717,5718,5719,5720,5721,5726,5727,5730,5731,5736,5737,5740,5741,5742,5743,5744,5745,5750,5751,5764]
def ridgeSupport296_003 : List Nat := [5765,5766,5767,5768,5769,5788,5789,5790,5791,5792,5793,5812,5813,5814,5815,5816,5817,5836,5837,5838,5839,5840,5841,5860,5861,5862,5863,5864,5865,5884,5885,5886]
def ridgeSupport296_004 : List Nat := [5887,5888,5889,5897,5900,5903,5906,5908,5909,5910,5911,5912,5913,5914,5916,5966,5967,5978,5979,5980,5982,5986,5988,6002,6003,6014,6015,6108,6109,6120,6121,6125]
def ridgeSupport296_005 : List Nat := [6128,6131,6134,6144,6145,6156,6157,6180,6181,6192,6193,6197,6200,6203,6206,6216,6217,6228,6229,6770,6771,6788,6789,6806,6807,6808,6810,6814,6816,6824,6825,6912]
def ridgeSupport296_006 : List Nat := [6913,6930,6931,6948,6949,6953,6956,6959,6962,6966,6967,6984,6985,7002,7003,7020,7021,7025,7028,7031,7034,7038,7039,7540,7541,7542,7543,7544,7545,8524,8525,8526]
def ridgeSupport296_007 : List Nat := [8527,8528,8529,8537,8540,8543,8545,8546,8547,8549,8552,8555,8557,8558,8559,8564,8565,8570,8571,8598,8599,8604,8605,8616,8617,8622,8623,8752,8754,8768,8769,8789]
def ridgeSupport296_008 : List Nat := [8792,8802,8803,8807,8810,8820,8821]
def ridgeSupport296_code : Nat := 0x227589d226a899e263898a2588956241890223288c21af86ba1a986a219d8672197865a17b85ea17585d216f85ba16d85ae1688596163858a161857e15c8566151854214f853a14d8531d7975e1d7775d9d7575d1b7f6df9b7a6dddb746dc5b6d6db1b5b6d69b496d21b376cd9b326cbdb2c6ca5b256c91b136c49b016c01aa96aa1aa06a79a9a6a61a976a59a856a11a7369c98556151849612183e60ed83860d583160c1825609180d603180160017f65fcd7f05fb57e95fa17dd5f7177f5df97735dc97645d8975e5d7175b5d6974f5d3971c5c697195c617175c597155c517125c3d70c5c257015c016ff5bf96fd5bf16e95ba16e75b996e55b916d15b416cf5b396cd5b316b95ae16b75ad96b55ad16a15a8169f5a7969d5a716895a216875a196855a1167759d967159c166f59b966d59b166959a1663598965f5979659596165759596555951651594164b59286a61a946a21a8469f1a7869c1a686991a5c6961a506911a4068d1a3068a1a246871a146841a0868119fc66919a06631984660197865d19706591960656195460017ec5fa17dc5f6179c5e417845e017745cf17305c917205c5116845811544531140443110443c10e843910ac4291090422108406e01b006a0184043
def ridgeSupport296_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport296_code
def ridgeSupport296_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport296_code
def ridgeSupport296_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport296_code
def ridgeSupport296_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport296_code
def ridgeSupport296_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport296_code
def ridgeSupport296_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport296_code
def ridgeSupport296_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport296_code
def ridgeSupport296_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport296_code
def ridgeSupport296_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport296_code
def ridgeSupport296_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport296_code
def ridgeSupport296_suffix_009 : List Nat := []
def ridgeSupport296_suffix_008 : List Nat := ridgeSupport296_008 ++ ridgeSupport296_suffix_009
def ridgeSupport296_suffix_007 : List Nat := ridgeSupport296_007 ++ ridgeSupport296_suffix_008
def ridgeSupport296_suffix_006 : List Nat := ridgeSupport296_006 ++ ridgeSupport296_suffix_007
def ridgeSupport296_suffix_005 : List Nat := ridgeSupport296_005 ++ ridgeSupport296_suffix_006
def ridgeSupport296_suffix_004 : List Nat := ridgeSupport296_004 ++ ridgeSupport296_suffix_005
def ridgeSupport296_suffix_003 : List Nat := ridgeSupport296_003 ++ ridgeSupport296_suffix_004
def ridgeSupport296_suffix_002 : List Nat := ridgeSupport296_002 ++ ridgeSupport296_suffix_003
def ridgeSupport296_suffix_001 : List Nat := ridgeSupport296_001 ++ ridgeSupport296_suffix_002
def ridgeSupport296_suffix_000 : List Nat := ridgeSupport296_000 ++ ridgeSupport296_suffix_001
theorem ridgeSupport296_source : candidateSupports 296 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport296_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
