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
def ridgeSupport769_000 : List Nat := [14,20,26,29,30,164,165,166,167,168,169,236,237,238,239,240,241,288,292,293,294,295,297,298,305,307,309,313,314,315,316,318]
def ridgeSupport769_001 : List Nat := [319,326,328,376,380,381,382,383,385,386,393,395,397,401,402,403,404,406,407,414,416,460,464,465,466,467,469,470,477,479,481,485]
def ridgeSupport769_002 : List Nat := [486,487,488,490,491,498,500,502,503,507,508,509,510,512,513,521,523,524,526,1414,1416,1420,1422,1452,1453,1458,1459,1500,1501,1506,1507,1508]
def ridgeSupport769_003 : List Nat := [1509,1514,1515,1520,1522,1526,1528,1534,1536,1540,1542,1548,1549,1554,1555,1596,1597,1602,1603,1620,1621,1626,1627,1654,1656,1660,1662,1692,1693,1698,1699,1740]
def ridgeSupport769_004 : List Nat := [1741,1746,1747,1748,1749,1754,1755,1760,1762,1766,1768,1774,1776,1780,1782,1788,1789,1794,1795,1836,1837,1842,1843,1860,1861,1866,1867,2266,2268,2278,2280,2306]
def ridgeSupport769_005 : List Nat := [2307,2318,2319,2338,2340,2350,2352,2378,2379,2390,2391,2422,2424,2428,2430,2460,2461,2466,2467,2508,2509,2514,2515,2516,2517,2522,2523,2528,2530,2534,2536,2542]
def ridgeSupport769_006 : List Nat := [2544,2548,2550,2556,2557,2562,2563,2604,2605,2610,2611,2628,2629,2634,2635,3034,3036,3046,3048,3074,3075,3086,3087,3106,3108,3118,3120,3146,3147,3158,3159,3730]
def ridgeSupport769_007 : List Nat := [3731,3734,3735,5135,5137,5139,5141,5147,5149,5151,5153,5183,5185,5189,5191,5195,5197,5199,5201,5231,5233,5237,5239,5382,5383,5418,5419,5514,5515,5864,5866,5870]
def ridgeSupport769_008 : List Nat := [5872,5888,5889,5891,5893,5894,5895,5912,5914,5918,5920,5936,5937,5939,5941,5942,5943,6044,6045,6047,6049,6062,6063,6065,6067,6080,6082,6086,6088,6104,6105,6107]
def ridgeSupport769_009 : List Nat := [6109,6110,6111,6212,6213,6215,6217,6230,6231,6233,6235]
cert_ridgeSupport_code_3 769
cert_ridgeSupport_rest_2 769 000 0
cert_ridgeSupport_rest_2 769 001 416
cert_ridgeSupport_rest_2 769 002 832
cert_ridgeSupport_rest_2 769 003 1248
cert_ridgeSupport_rest_2 769 004 1664
cert_ridgeSupport_rest_2 769 005 2080
cert_ridgeSupport_rest_2 769 006 2496
cert_ridgeSupport_rest_2 769 007 2912
cert_ridgeSupport_rest_2 769 008 3328
cert_ridgeSupport_rest_2 769 009 3744
cert_ridgeSupport_rest_2 769 010 3887
cert_ridgeSupport_suffix_4 769 010
cert_ridgeSupport_suffix_3 769 009 010
cert_ridgeSupport_suffix_3 769 008 009
cert_ridgeSupport_suffix_3 769 007 008
cert_ridgeSupport_suffix_3 769 006 007
cert_ridgeSupport_suffix_3 769 005 006
cert_ridgeSupport_suffix_3 769 004 005
cert_ridgeSupport_suffix_3 769 003 004
cert_ridgeSupport_suffix_3 769 002 003
cert_ridgeSupport_suffix_3 769 001 002
cert_ridgeSupport_suffix_3 769 000 001
cert_ridgeSupport_source_3 769 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
