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
def ridgeSupport352_000 : List Nat := [86,106,116,125,127,1056,1057,1058,1059,1066,1067,1212,1213,1214,1215,1222,1223,1356,1358,1360,1362,1364,1369,1370,1372,1375,1398,1399,1403,1405,1406,1410]
def ridgeSupport352_001 : List Nat := [1412,1413,1415,1477,1478,1479,1480,1487,1488,1621,1623,1625,1627,1629,1634,1635,1637,1640,1663,1664,1668,1670,1671,1675,1677,1678,1680,1730,1732,1734,1736,1738]
def ridgeSupport352_002 : List Nat := [1743,1744,1746,1749,1772,1773,1777,1779,1780,1784,1786,1787,1789,1840,1842,1843,1845,1846,1848,1850,1851,1853,1854,1858,1859,5471,5473,5482,5487,5538,5539,5548]
def ridgeSupport352_003 : List Nat := [5549,5561,5564,5570,5571,5575,5577,5580,5581,5586,5587,5596,5597,5634,5635,5639,5641,5644,5645,5650,5655,5666,5667,5676,5677,5690,5691,5700,5701,5711,5713,5722]
def ridgeSupport352_004 : List Nat := [5727,5778,5779,5788,5789,5801,5804,5810,5811,5815,5817,5820,5821,5826,5827,5836,5837,5874,5875,5879,5881,5884,5885,5890,5895,5906,5907,5916,5917,5930,5931,5940]
def ridgeSupport352_005 : List Nat := [5941,5950,5955,5962,5967,5982,5983,5994,5995,6095,6097,6107,6109,6128,6129,6140,6141,6239,6241,6250,6255,6306,6307,6316,6317,6329,6332,6338,6339,6343,6345,6348]
def ridgeSupport352_006 : List Nat := [6349,6354,6355,6364,6365,6402,6403,6407,6409,6412,6413,6418,6423,6434,6435,6444,6445,6458,6459,6468,6469,6478,6483,6490,6495,6510,6511,6522,6523,6623,6625,6635]
def ridgeSupport352_007 : List Nat := [6637,6656,6657,6668,6669,6766,6771,6778,6783,6798,6799,6810,6811,6911,6913,6923,6925,6944,6945,6956,6957,7524,7525,7560,7561,7620,7621,8466,8467,8476,8477,8490]
def ridgeSupport352_008 : List Nat := [8491,8494,8496,8497,8498,8514,8515,8524,8525,8538,8539,8542,8544,8545,8546,8561,8562,8563,8564,8596,8598,8600,8601,8634,8635,8644,8645,8658,8659,8662,8664,8665]
def ridgeSupport352_009 : List Nat := [8666,8681,8682,8683,8684,8716,8718,8720,8721,8753,8754,8755,8756,8788,8790,8792,8793]
def ridgeSupport352_code : Nat := 0x22598962256895223488ce23288c6211884220e88321ec87ae1ea87a61da87661d8875a1d3874a1c587121bb86ea1998662196865217485ce17285c61628586160857a15b856a14d8532143850a13284c613084ba12b84aa11d84721138449dc57711d897621d657591b2d6cb1b216c81b0d6c2db016bfda9b6a69a8f6a39a7f69e9a7369b9a0d6831a0168019ed67ad9e1677d97b65e996f65b995f65699536539945651193b64e992d64b19236489917644990d6431909641d90364098dd63718d363498cd63318c9631d8c363098bc62e58ad62b18a3628986f61a9861617d7fd5ff17f15fc17dd5f6d7d15f3d76b5da975f5d7974f5d297435cf97355cd172b5ca971d5c717135c497075c096fd5bf16f95bdd6f35bc96cd5b316c35b096bd5af16b95add6b35ac96ac5aa569d5a716935a4965f5969651593d645591163b58e962d58b16235889617584960d5831609581d60358095dd57715d357495cd57315c9571d5c357095bc56e55ad56b15a3568956f55a9561557c7431d0873e1cf473b1ce87381cd87351ccc7321cc06fd1bec6fa1be06f41bcc6f11bb46ec1b546d21b406cf1b286c81b186c41b086901a3868d1a2c6871a186841a0067f19a0665198c662197465b196465719545d0173c5c8171c5c617145871614584160857e15f457b15dc576157c55c15685591550552154054e15304c713184bf12f84bd12f042b10a84231088421108007f01f407401a8056
def ridgeSupport352_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport352_code
def ridgeSupport352_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport352_code
def ridgeSupport352_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport352_code
def ridgeSupport352_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport352_code
def ridgeSupport352_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport352_code
def ridgeSupport352_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport352_code
def ridgeSupport352_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport352_code
def ridgeSupport352_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport352_code
def ridgeSupport352_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport352_code
def ridgeSupport352_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport352_code
def ridgeSupport352_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport352_code
def ridgeSupport352_suffix_010 : List Nat := []
def ridgeSupport352_suffix_009 : List Nat := ridgeSupport352_009 ++ ridgeSupport352_suffix_010
def ridgeSupport352_suffix_008 : List Nat := ridgeSupport352_008 ++ ridgeSupport352_suffix_009
def ridgeSupport352_suffix_007 : List Nat := ridgeSupport352_007 ++ ridgeSupport352_suffix_008
def ridgeSupport352_suffix_006 : List Nat := ridgeSupport352_006 ++ ridgeSupport352_suffix_007
def ridgeSupport352_suffix_005 : List Nat := ridgeSupport352_005 ++ ridgeSupport352_suffix_006
def ridgeSupport352_suffix_004 : List Nat := ridgeSupport352_004 ++ ridgeSupport352_suffix_005
def ridgeSupport352_suffix_003 : List Nat := ridgeSupport352_003 ++ ridgeSupport352_suffix_004
def ridgeSupport352_suffix_002 : List Nat := ridgeSupport352_002 ++ ridgeSupport352_suffix_003
def ridgeSupport352_suffix_001 : List Nat := ridgeSupport352_001 ++ ridgeSupport352_suffix_002
def ridgeSupport352_suffix_000 : List Nat := ridgeSupport352_000 ++ ridgeSupport352_suffix_001
theorem ridgeSupport352_source : candidateSupports 352 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport352_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
