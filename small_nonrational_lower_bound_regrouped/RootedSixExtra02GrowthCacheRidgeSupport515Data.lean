module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport515_000 : List Nat := [4,8,11,13,14,126,128,131,132,134,150,152,155,156,158,162,164,167,168,170,198,200,203,204,206,222,224,227,228,230,234,236]
def ridgeSupport515_001 : List Nat := [239,240,242,267,268,270,271,274,275,276,278,279,281,286,287,288,289,291,292,295,296,297,299,300,302,307,308,309,310,312,313,316]
def ridgeSupport515_002 : List Nat := [317,318,320,321,323,328,329,1392,1393,1398,1399,1404,1405,1406,1407,1408,1409,1410,1411,1416,1417,1422,1423,1428,1429,1430,1431,1432,1433,1434,1435,1454]
def ridgeSupport515_003 : List Nat := [1455,1456,1457,1458,1459,1478,1479,1480,1481,1482,1483,1502,1503,1504,1505,1506,1507,1526,1527,1528,1529,1530,1531,1550,1551,1552,1553,1554,1555,1574,1575,1576]
def ridgeSupport515_004 : List Nat := [1577,1578,1579,1580,1582,1586,1588,1592,1594,1598,1599,1600,1601,1602,1603,2184,2185,2196,2197,2220,2221,2232,2233,2240,2242,2246,2248,2256,2257,2268,2269,2292]
def ridgeSupport515_005 : List Nat := [2293,2304,2305,2312,2314,2318,2320,2328,2329,2340,2341,2364,2365,2376,2377,2384,2386,2390,2392,2952,2953,2964,2965,2988,2989,3000,3001,3008,3010,3014,3016,3024]
def ridgeSupport515_006 : List Nat := [3025,3036,3037,3060,3061,3072,3073,3080,3082,3086,3088,3096,3097,3108,3109,3132,3133,3144,3145,3152,3154,3158,3160,5136,5137,5140,5141,5142,5143,5178,5179,5184]
def ridgeSupport515_007 : List Nat := [5185,5190,5191,5226,5227,5232,5233,5238,5239,5366,5367,5368,5369,5370,5371,5870,5871,5872,5873,5874,5875,5876,5878,5882,5884,5886,5887,5888,5890,5894,5896,5898]
def ridgeSupport515_008 : List Nat := [5899,6020,6022,6026,6028,6038,6040,6044,6046,6056,6058,6062,6064,6188,6190,6194,6196,6206,6208,6212,6214,6224,6226,6230,6232]
cert_ridgeSupport_code_3 515
cert_ridgeSupport_rest_2 515 000 0
cert_ridgeSupport_rest_2 515 001 416
cert_ridgeSupport_rest_2 515 002 832
cert_ridgeSupport_rest_2 515 003 1248
cert_ridgeSupport_rest_2 515 004 1664
cert_ridgeSupport_rest_2 515 005 2080
cert_ridgeSupport_rest_2 515 006 2496
cert_ridgeSupport_rest_2 515 007 2912
cert_ridgeSupport_rest_2 515 008 3328
cert_ridgeSupport_rest_2 515 009 3653
cert_ridgeSupport_suffix_4 515 009
cert_ridgeSupport_suffix_3 515 008 009
cert_ridgeSupport_suffix_3 515 007 008
cert_ridgeSupport_suffix_3 515 006 007
cert_ridgeSupport_suffix_3 515 005 006
cert_ridgeSupport_suffix_3 515 004 005
cert_ridgeSupport_suffix_3 515 003 004
cert_ridgeSupport_suffix_3 515 002 003
cert_ridgeSupport_suffix_3 515 001 002
cert_ridgeSupport_suffix_3 515 000 001
cert_ridgeSupport_source_3 515 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
