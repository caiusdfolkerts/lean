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
def ridgeSupport577_000 : List Nat := [11,17,23,28,29,128,129,130,131,132,133,200,201,202,203,204,205,268,270,272,273,275,277,278,282,287,289,291,293,294,296,298]
def ridgeSupport577_001 : List Nat := [299,303,308,356,358,360,361,363,365,366,370,375,377,379,381,382,384,386,387,391,396,440,442,444,445,447,449,450,454,459,461,463]
def ridgeSupport577_002 : List Nat := [465,466,468,470,471,475,480,503,504,506,507,510,511,512,514,515,517,524,525,1418,1423,1424,1429,1440,1441,1454,1455,1488,1489,1502,1503,1508]
def ridgeSupport577_003 : List Nat := [1510,1516,1517,1522,1523,1529,1531,1536,1537,1538,1543,1544,1549,1550,1551,1584,1585,1598,1599,1608,1609,1622,1623,1658,1663,1664,1669,1680,1681,1694,1695,1728]
def ridgeSupport577_004 : List Nat := [1729,1742,1743,1748,1750,1756,1757,1762,1763,1769,1771,1776,1777,1778,1783,1784,1789,1790,1791,1824,1825,1838,1839,1848,1849,1862,1863,2192,2197,2204,2209,2236]
def ridgeSupport577_005 : List Nat := [2237,2248,2249,2264,2269,2276,2281,2308,2309,2320,2321,2426,2431,2432,2437,2448,2449,2462,2463,2496,2497,2510,2511,2516,2518,2524,2525,2530,2531,2537,2539,2544]
def ridgeSupport577_006 : List Nat := [2545,2546,2551,2552,2557,2558,2559,2592,2593,2606,2607,2616,2617,2630,2631,2960,2965,2972,2977,3004,3005,3016,3017,3032,3037,3044,3049,3076,3077,3088,3089,3682]
def ridgeSupport577_007 : List Nat := [3683,3686,3687,5133,5135,5140,5142,5145,5147,5152,5154,5175,5178,5181,5184,5193,5195,5200,5202,5223,5226,5229,5232,5376,5377,5412,5413,5508,5509,5852,5854,5873]
def ridgeSupport577_008 : List Nat := [5875,5892,5893,5895,5896,5897,5899,5900,5902,5921,5923,5940,5941,5943,5944,5945,5947,6027,6028,6029,6030,6045,6046,6047,6048,6068,6070,6089,6091,6108,6109,6111]
def ridgeSupport577_009 : List Nat := [6112,6113,6115,6195,6196,6197,6198,6213,6214,6215,6216]
cert_ridgeSupport_code_3 577
cert_ridgeSupport_rest_2 577 000 0
cert_ridgeSupport_rest_2 577 001 416
cert_ridgeSupport_rest_2 577 002 832
cert_ridgeSupport_rest_2 577 003 1248
cert_ridgeSupport_rest_2 577 004 1664
cert_ridgeSupport_rest_2 577 005 2080
cert_ridgeSupport_rest_2 577 006 2496
cert_ridgeSupport_rest_2 577 007 2912
cert_ridgeSupport_rest_2 577 008 3328
cert_ridgeSupport_rest_2 577 009 3744
cert_ridgeSupport_rest_2 577 010 3887
cert_ridgeSupport_suffix_4 577 010
cert_ridgeSupport_suffix_3 577 009 010
cert_ridgeSupport_suffix_3 577 008 009
cert_ridgeSupport_suffix_3 577 007 008
cert_ridgeSupport_suffix_3 577 006 007
cert_ridgeSupport_suffix_3 577 005 006
cert_ridgeSupport_suffix_3 577 004 005
cert_ridgeSupport_suffix_3 577 003 004
cert_ridgeSupport_suffix_3 577 002 003
cert_ridgeSupport_suffix_3 577 001 002
cert_ridgeSupport_suffix_3 577 000 001
cert_ridgeSupport_source_3 577 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
