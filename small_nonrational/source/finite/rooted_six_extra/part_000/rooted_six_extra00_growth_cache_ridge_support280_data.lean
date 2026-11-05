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
def ridgeSupport280_000 : List Nat := [47,97,100,102,104,792,793,795,800,802,816,817,819,824,826,839,842,844,847,849,1477,1479,1482,1483,1485,1501,1503,1506,1507,1509,1526,1528]
def ridgeSupport280_001 : List Nat := [1529,1532,1534,1537,1538,1540,1541,1544,1545,1546,1548,1549,1551,1556,1557,1579,1581,1582,1584,1585,1587,1589,1590,1592,1593,1596,1597,1600,1602,1603,1605,1606]
def ridgeSupport280_002 : List Nat := [1608,1610,1611,1613,1614,1617,1618,4938,4939,4944,4945,4948,4949,4950,4951,4952,4953,4958,4959,4962,4963,4968,4969,4972,4973,4974,4975,4976,4977,4982,4983,4996]
def ridgeSupport280_003 : List Nat := [4997,4998,4999,5000,5001,5020,5021,5022,5023,5024,5025,5044,5045,5046,5047,5048,5049,5068,5069,5070,5071,5072,5073,5092,5093,5094,5095,5096,5097,5116,5117,5118]
def ridgeSupport280_004 : List Nat := [5119,5120,5121,5129,5132,5135,5138,5140,5141,5142,5143,5144,5145,5146,5148,5198,5199,5210,5211,5212,5214,5218,5220,5234,5235,5246,5247,5340,5341,5352,5353,5357]
def ridgeSupport280_005 : List Nat := [5360,5363,5366,5376,5377,5388,5389,5412,5413,5424,5425,5429,5432,5435,5438,5448,5449,5460,5461,6764,6765,6776,6777,6800,6801,6812,6813,6820,6822,6826,6828,6906]
def ridgeSupport280_006 : List Nat := [6907,6918,6919,6942,6943,6954,6955,6965,6968,6971,6974,6978,6979,6990,6991,7014,7015,7026,7027,7037,7040,7043,7046,7444,7445,7446,7447,7448,7449,8356,8357,8358]
def ridgeSupport280_007 : List Nat := [8359,8360,8361,8369,8372,8375,8377,8378,8379,8381,8384,8387,8389,8390,8391,8396,8397,8402,8403,8430,8431,8436,8437,8448,8449,8454,8455,8758,8760,8764,8766,8795]
def ridgeSupport280_008 : List Nat := [8798,8801,8804,8813,8816,8819,8822]
def ridgeSupport280_code : Nat := 0x227689ce27089b6264898625e896e23e88f223888da107841a10184020f583d20ef83ba0d3834a0cd83320c7831a0c5830e0c082f60bb82ea0b982de0b482c60a982a20a7829a0a58291d197461d177459d157451b866e0db806df5b736dc9b676d99b4f6d39b436d09b3e6cedb386cd5b2b6ca9b1f6c79b076c19afb6be9aac6aa9aa66a91a9d6a71a916a41a7969e1a6d69b15555551549552153e54ed53854d553154c1525549150d543150154014f653cd4f053b54e953a14dd537147f51f947351c9464518945e517145b516944f513941c5069419506141750594155051412503d40c502540150013ff4ff93fd4ff13e94fa13e74f993e54f913d14f413cf4f393cd4f313b94ee13b74ed93b54ed13a14e8139f4e7939d4e713894e213874e193854e113774dd93714dc136f4db936d4db13694da13634d8935f4d793594d613574d593554d513514d4134b4d28652194464e193464b19286481918645190c642190063d18f063918e063618d463318c463018b862d18ac615185060f183460c18286091820605181060218045fe17f05f917e05f617945e317885df17745cd172c5ca171c5c50d4434f0d3034a0d1c33a0ce03330cc43300c883200c6c3190c600680198064018402f
def ridgeSupport280_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport280_code
def ridgeSupport280_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport280_code
def ridgeSupport280_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport280_code
def ridgeSupport280_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport280_code
def ridgeSupport280_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport280_code
def ridgeSupport280_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport280_code
def ridgeSupport280_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport280_code
def ridgeSupport280_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport280_code
def ridgeSupport280_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport280_code
def ridgeSupport280_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport280_code
def ridgeSupport280_suffix_009 : List Nat := []
def ridgeSupport280_suffix_008 : List Nat := ridgeSupport280_008 ++ ridgeSupport280_suffix_009
def ridgeSupport280_suffix_007 : List Nat := ridgeSupport280_007 ++ ridgeSupport280_suffix_008
def ridgeSupport280_suffix_006 : List Nat := ridgeSupport280_006 ++ ridgeSupport280_suffix_007
def ridgeSupport280_suffix_005 : List Nat := ridgeSupport280_005 ++ ridgeSupport280_suffix_006
def ridgeSupport280_suffix_004 : List Nat := ridgeSupport280_004 ++ ridgeSupport280_suffix_005
def ridgeSupport280_suffix_003 : List Nat := ridgeSupport280_003 ++ ridgeSupport280_suffix_004
def ridgeSupport280_suffix_002 : List Nat := ridgeSupport280_002 ++ ridgeSupport280_suffix_003
def ridgeSupport280_suffix_001 : List Nat := ridgeSupport280_001 ++ ridgeSupport280_suffix_002
def ridgeSupport280_suffix_000 : List Nat := ridgeSupport280_000 ++ ridgeSupport280_suffix_001
theorem ridgeSupport280_source : candidateSupports 280 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport280_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
