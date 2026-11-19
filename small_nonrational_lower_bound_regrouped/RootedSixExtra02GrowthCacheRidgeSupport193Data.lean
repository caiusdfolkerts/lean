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
def ridgeSupport193_000 : List Nat := [9,15,21,27,28,104,105,106,107,108,109,176,177,178,179,180,181,248,249,250,253,254,255,257,262,264,269,270,271,274,275,276]
def ridgeSupport193_001 : List Nat := [278,283,285,336,337,338,341,342,343,345,350,352,357,358,359,362,363,364,366,371,373,420,421,422,425,426,427,429,434,436,441,442]
def ridgeSupport193_002 : List Nat := [443,446,447,448,450,455,457,504,505,507,508,509,510,512,513,515,516,518,519,1425,1427,1431,1433,1436,1437,1442,1443,1484,1485,1490,1491,1511]
def ridgeSupport193_003 : List Nat := [1513,1517,1519,1524,1525,1530,1531,1532,1533,1538,1539,1545,1547,1551,1553,1580,1581,1586,1587,1604,1605,1610,1611,1665,1667,1671,1673,1676,1677,1682,1683,1724]
def ridgeSupport193_004 : List Nat := [1725,1730,1731,1751,1753,1757,1759,1764,1765,1770,1771,1772,1773,1778,1779,1785,1787,1791,1793,1820,1821,1826,1827,1844,1845,1850,1851,2121,2123,2133,2135,2166]
def ridgeSupport193_005 : List Nat := [2167,2178,2179,2193,2195,2205,2207,2238,2239,2250,2251,2433,2435,2439,2441,2444,2445,2450,2451,2492,2493,2498,2499,2519,2521,2525,2527,2532,2533,2538,2539,2540]
def ridgeSupport193_006 : List Nat := [2541,2546,2547,2553,2555,2559,2561,2588,2589,2594,2595,2612,2613,2618,2619,2889,2891,2901,2903,2934,2935,2946,2947,2961,2963,2973,2975,3006,3007,3018,3019,3650]
def ridgeSupport193_007 : List Nat := [3651,3654,3655,5134,5136,5138,5140,5146,5148,5150,5152,5168,5170,5174,5176,5194,5196,5198,5200,5216,5218,5222,5224,5372,5373,5408,5409,5504,5505,5855,5857,5861]
def ridgeSupport193_008 : List Nat := [5863,5888,5889,5894,5895,5898,5899,5903,5905,5909,5911,5936,5937,5942,5943,5946,5947,6008,6010,6012,6013,6026,6028,6030,6031,6071,6073,6077,6079,6104,6105,6110]
def ridgeSupport193_009 : List Nat := [6111,6114,6115,6176,6178,6180,6181,6194,6196,6198,6199]
cert_ridgeSupport_code_3 193
cert_ridgeSupport_rest_2 193 000 0
cert_ridgeSupport_rest_2 193 001 416
cert_ridgeSupport_rest_2 193 002 832
cert_ridgeSupport_rest_2 193 003 1248
cert_ridgeSupport_rest_2 193 004 1664
cert_ridgeSupport_rest_2 193 005 2080
cert_ridgeSupport_rest_2 193 006 2496
cert_ridgeSupport_rest_2 193 007 2912
cert_ridgeSupport_rest_2 193 008 3328
cert_ridgeSupport_rest_2 193 009 3744
cert_ridgeSupport_rest_2 193 010 3887
cert_ridgeSupport_suffix_4 193 010
cert_ridgeSupport_suffix_3 193 009 010
cert_ridgeSupport_suffix_3 193 008 009
cert_ridgeSupport_suffix_3 193 007 008
cert_ridgeSupport_suffix_3 193 006 007
cert_ridgeSupport_suffix_3 193 005 006
cert_ridgeSupport_suffix_3 193 004 005
cert_ridgeSupport_suffix_3 193 003 004
cert_ridgeSupport_suffix_3 193 002 003
cert_ridgeSupport_suffix_3 193 001 002
cert_ridgeSupport_suffix_3 193 000 001
cert_ridgeSupport_source_3 193 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
