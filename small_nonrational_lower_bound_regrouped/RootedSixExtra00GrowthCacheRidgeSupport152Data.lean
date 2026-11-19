module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_7 152 008 8780 8783 8786 8815 8817 8821 8823
cert_ridgeSupport_code_3 152
cert_ridgeSupport_rest_2 152 000 0
cert_ridgeSupport_rest_2 152 001 448
cert_ridgeSupport_rest_2 152 002 896
cert_ridgeSupport_rest_2 152 003 1344
cert_ridgeSupport_rest_2 152 004 1792
cert_ridgeSupport_rest_2 152 005 2240
cert_ridgeSupport_rest_2 152 006 2688
cert_ridgeSupport_rest_2 152 007 3136
cert_ridgeSupport_rest_2 152 008 3584
cert_ridgeSupport_rest_2 152 009 3682
cert_ridgeSupport_suffix_4 152 009
cert_ridgeSupport_suffix_3 152 008 009
cert_ridgeSupport_suffix_3 152 007 008
cert_ridgeSupport_suffix_3 152 006 007
cert_ridgeSupport_suffix_3 152 005 006
cert_ridgeSupport_suffix_3 152 004 005
cert_ridgeSupport_suffix_3 152 003 004
cert_ridgeSupport_suffix_3 152 002 003
cert_ridgeSupport_suffix_3 152 001 002
cert_ridgeSupport_suffix_3 152 000 001
cert_ridgeSupport_source_3 152 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
