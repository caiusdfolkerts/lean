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
def ridgeSupport152_000 : List Nat := [46,96,99,102,103,780,781,783,788,790,815,818,820,823,825,827,830,832,835,837,1465,1467,1470,1471,1473,1502,1504,1505,1508,1510,1514,1516]
def ridgeSupport152_001 : List Nat := [1517,1520,1522,1537,1539,1540,1542,1543,1545,1547,1548,1550,1551,1554,1555,1558,1560,1561,1563,1564,1566,1568,1569,1571,1572,1575,1576,1601,1602,1604,1605,1606]
def ridgeSupport152_002 : List Nat := [1607,1609,1610,1612,1613,1615,1616,4936,4937,4942,4943,4944,4945,4946,4947,4950,4951,4956,4957,4960,4961,4966,4967,4968,4969,4970,4971,4974,4975,4980,4981,4990]
def ridgeSupport152_003 : List Nat := [4991,4992,4993,4994,4995,5014,5015,5016,5017,5018,5019,5038,5039,5040,5041,5042,5043,5062,5063,5064,5065,5066,5067,5086,5087,5088,5089,5090,5091,5110,5111,5112]
def ridgeSupport152_004 : List Nat := [5113,5114,5115,5131,5133,5134,5135,5136,5137,5138,5139,5141,5144,5147,5150,5196,5197,5208,5209,5213,5216,5219,5222,5232,5233,5244,5245,5268,5269,5280,5281,5285]
def ridgeSupport152_005 : List Nat := [5288,5291,5294,5304,5305,5316,5317,5410,5411,5422,5423,5431,5433,5437,5439,5446,5447,5458,5459,6762,6763,6774,6775,6798,6799,6810,6811,6821,6824,6827,6830,6834]
def ridgeSupport152_006 : List Nat := [6835,6846,6847,6870,6871,6882,6883,6893,6896,6899,6902,6976,6977,6988,6989,7012,7013,7024,7025,7039,7041,7045,7047,7438,7439,7440,7441,7442,7443,8350,8351,8352]
def ridgeSupport152_007 : List Nat := [8353,8354,8355,8371,8373,8374,8375,8376,8377,8383,8385,8386,8387,8388,8389,8394,8395,8400,8401,8412,8413,8418,8419,8446,8447,8452,8453,8759,8762,8765,8768,8777]
def ridgeSupport152_008 : List Nat := [8780,8783,8786,8815,8817,8821,8823]
def ridgeSupport152_code : Nat := 0x227789d627189be252893e24c892624088f623a88de10584120ff83fa0e3838a0dd83720d183420cb832a0c583120c3830a0c182fe0b982e20b782da0b582ce0a3828a0a1828209f8279d137449d117441d0f7439b876e15b816dfdb716dc1b656d91b4d6d31b416d01af66bcdaf06bb5ae36b89ad76b59abf6af9ab36ac9aae6aadaa86a95a9b6a69a8f6a39a7769d9a6b69a95535549547551953f54f553954dd52f54b952354894c553114b952e14ae52ad4a852954a15281495525147d51f147151c1466518d4605175459516144d513141e506d41850554135049411504140f503940d502d3fb4fe93f94fe13f74fd93e34f893e14f813df4f793cb4f293c94f213c74f193b34ec93b14ec13af4eb939b4e693994e613974e593834e093814e0137f4df93754dd136f4db936b4da93694da13674d993614d8135d4d713574d593534d493514d4134f4d393494d20650193c64d193064a1924647191864519106421904628189c624188c621188061e187061b18646181858613184860f183860c182c609181c606181060318045f217c05ed17b05ea17985e417845e017785c116fc5be16ec5b90d143430d0033e0cec3390cdc3340cc832f0c583140c3c30d0c300670198063018002e
def ridgeSupport152_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport152_code
def ridgeSupport152_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport152_code
def ridgeSupport152_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport152_code
def ridgeSupport152_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport152_code
def ridgeSupport152_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport152_code
def ridgeSupport152_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport152_code
def ridgeSupport152_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport152_code
def ridgeSupport152_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport152_code
def ridgeSupport152_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport152_code
def ridgeSupport152_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport152_code
def ridgeSupport152_suffix_009 : List Nat := []
def ridgeSupport152_suffix_008 : List Nat := ridgeSupport152_008 ++ ridgeSupport152_suffix_009
def ridgeSupport152_suffix_007 : List Nat := ridgeSupport152_007 ++ ridgeSupport152_suffix_008
def ridgeSupport152_suffix_006 : List Nat := ridgeSupport152_006 ++ ridgeSupport152_suffix_007
def ridgeSupport152_suffix_005 : List Nat := ridgeSupport152_005 ++ ridgeSupport152_suffix_006
def ridgeSupport152_suffix_004 : List Nat := ridgeSupport152_004 ++ ridgeSupport152_suffix_005
def ridgeSupport152_suffix_003 : List Nat := ridgeSupport152_003 ++ ridgeSupport152_suffix_004
def ridgeSupport152_suffix_002 : List Nat := ridgeSupport152_002 ++ ridgeSupport152_suffix_003
def ridgeSupport152_suffix_001 : List Nat := ridgeSupport152_001 ++ ridgeSupport152_suffix_002
def ridgeSupport152_suffix_000 : List Nat := ridgeSupport152_000 ++ ridgeSupport152_suffix_001
theorem ridgeSupport152_source : candidateSupports 152 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport152_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
