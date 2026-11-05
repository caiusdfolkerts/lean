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
def ridgeSupport608_000 : List Nat := [87,107,117,126,127,1068,1069,1070,1071,1078,1079,1224,1225,1226,1227,1234,1235,1377,1379,1381,1383,1385,1390,1391,1393,1396,1398,1400,1402,1404,1406,1411]
def ridgeSupport608_001 : List Nat := [1412,1414,1417,1489,1490,1491,1492,1499,1500,1642,1644,1646,1648,1650,1655,1656,1658,1661,1663,1665,1667,1669,1671,1676,1677,1679,1682,1751,1753,1755,1757,1759]
def ridgeSupport608_002 : List Nat := [1764,1765,1767,1770,1772,1774,1776,1778,1780,1785,1786,1788,1791,1840,1841,1843,1844,1847,1848,1849,1851,1852,1854,1861,1862,5470,5475,5476,5481,5540,5541,5554]
def ridgeSupport608_003 : List Nat := [5555,5560,5562,5568,5569,5574,5575,5581,5583,5588,5589,5602,5603,5636,5637,5638,5643,5644,5649,5650,5651,5664,5665,5670,5671,5688,5689,5694,5695,5710,5715,5716]
def ridgeSupport608_004 : List Nat := [5721,5780,5781,5794,5795,5800,5802,5808,5809,5814,5815,5821,5823,5828,5829,5842,5843,5876,5877,5878,5883,5884,5889,5890,5891,5904,5905,5910,5911,5928,5929,5934]
def ridgeSupport608_005 : List Nat := [5935,6022,6027,6034,6039,6054,6055,6066,6067,6094,6099,6106,6111,6126,6127,6138,6139,6238,6243,6244,6249,6308,6309,6322,6323,6328,6330,6336,6337,6342,6343,6349]
def ridgeSupport608_006 : List Nat := [6351,6356,6357,6370,6371,6404,6405,6406,6411,6412,6417,6418,6419,6432,6433,6438,6439,6456,6457,6462,6463,6550,6555,6562,6567,6582,6583,6594,6595,6622,6627,6634]
def ridgeSupport608_007 : List Nat := [6639,6654,6655,6666,6667,6838,6843,6850,6855,6870,6871,6882,6883,6910,6915,6922,6927,6942,6943,6954,6955,7522,7523,7558,7559,7618,7619,8468,8469,8482,8483,8492]
def ridgeSupport608_008 : List Nat := [8493,8495,8496,8497,8499,8516,8517,8530,8531,8540,8541,8543,8544,8545,8547,8579,8580,8581,8582,8597,8598,8599,8600,8636,8637,8650,8651,8660,8661,8663,8664,8665]
def ridgeSupport608_009 : List Nat := [8667,8699,8700,8701,8702,8717,8718,8719,8720,8771,8772,8773,8774,8789,8790,8791,8792]
def ridgeSupport608_code : Nat := 0x2258895e25689562468916244890e210883e20e88361fe87f61fc87ee1db87661d8875e1d587521cb872a1bd86f2198865e19686561868616184860e1638586160857e15d8572153854a145851213384c613084be12d84b2123848a1158451dc37709d877619d637589b2b6ca9b1f6c79b0f6c29b036bf9ae36b89ad76b59ac76b09abb6ad9a0b68299ff67f99ef67a99e367799c367099b766d99a7668999b665993f64f993964e1927649992164819136449911643190b641990564118e363898d563518cf63358c763198c163018ba62e18b362c98a56291869619186361797fb5fe97ef5fb97df5f697d35f397b35ec97a75e997975e4978b5e1972f5cb97295ca17175c597115c417035c097015bf16fb5bd96f55bd16d35b496c55b116bf5af56b75ad96b15ac16aa5aa16a35a896955a516595951653593963f58f963958e1627589962158816135849611583160b581960558115e357895d557515cf57355c757195c157015ba56e15b356c95a55691569559156355787461d1473e1cf073b1ce47381cdc7341ccc7311cc06ff1bf06fa1be46f41bc86f01bb86ec1ba86e71b946e41b7c6dd1b6c6d91b5c6921a3c68d1a306871a146831a0467f19f467a19e067719c867019b866c19a85dc176c5d4174c5d217445891618584160c57e15f057a15e057615d057115bc56e15a4567159456315844d313484cb13284c9132043710d842f10b842d10b007f01f807501ac057
def ridgeSupport608_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport608_code
def ridgeSupport608_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport608_code
def ridgeSupport608_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport608_code
def ridgeSupport608_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport608_code
def ridgeSupport608_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport608_code
def ridgeSupport608_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport608_code
def ridgeSupport608_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport608_code
def ridgeSupport608_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport608_code
def ridgeSupport608_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport608_code
def ridgeSupport608_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport608_code
def ridgeSupport608_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport608_code
def ridgeSupport608_suffix_010 : List Nat := []
def ridgeSupport608_suffix_009 : List Nat := ridgeSupport608_009 ++ ridgeSupport608_suffix_010
def ridgeSupport608_suffix_008 : List Nat := ridgeSupport608_008 ++ ridgeSupport608_suffix_009
def ridgeSupport608_suffix_007 : List Nat := ridgeSupport608_007 ++ ridgeSupport608_suffix_008
def ridgeSupport608_suffix_006 : List Nat := ridgeSupport608_006 ++ ridgeSupport608_suffix_007
def ridgeSupport608_suffix_005 : List Nat := ridgeSupport608_005 ++ ridgeSupport608_suffix_006
def ridgeSupport608_suffix_004 : List Nat := ridgeSupport608_004 ++ ridgeSupport608_suffix_005
def ridgeSupport608_suffix_003 : List Nat := ridgeSupport608_003 ++ ridgeSupport608_suffix_004
def ridgeSupport608_suffix_002 : List Nat := ridgeSupport608_002 ++ ridgeSupport608_suffix_003
def ridgeSupport608_suffix_001 : List Nat := ridgeSupport608_001 ++ ridgeSupport608_suffix_002
def ridgeSupport608_suffix_000 : List Nat := ridgeSupport608_000 ++ ridgeSupport608_suffix_001
theorem ridgeSupport608_source : candidateSupports 608 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport608_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
