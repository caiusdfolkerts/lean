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
def ridgeSupport641_000 : List Nat := [13,19,25,28,30,152,153,154,155,156,157,224,225,226,227,228,229,267,271,272,273,274,276,277,284,286,310,312,314,315,317,319]
def ridgeSupport641_001 : List Nat := [320,324,329,355,359,360,361,362,364,365,372,374,398,400,402,403,405,407,408,412,417,439,443,444,445,446,448,449,456,458,482,484]
def ridgeSupport641_002 : List Nat := [486,487,489,491,492,496,501,502,504,506,508,509,511,513,514,518,520,525,526,1412,1417,1426,1428,1446,1447,1456,1457,1494,1495,1504,1505,1510]
def ridgeSupport641_003 : List Nat := [1511,1514,1516,1520,1521,1527,1530,1532,1537,1542,1543,1546,1548,1552,1553,1590,1591,1600,1601,1614,1615,1624,1625,1652,1657,1666,1668,1686,1687,1696,1697,1734]
def ridgeSupport641_004 : List Nat := [1735,1744,1745,1750,1751,1754,1756,1760,1761,1767,1770,1772,1777,1782,1783,1786,1788,1792,1793,1830,1831,1840,1841,1854,1855,1864,1865,2194,2196,2206,2208,2234]
def ridgeSupport641_005 : List Nat := [2235,2246,2247,2336,2341,2348,2353,2380,2381,2392,2393,2420,2425,2434,2436,2454,2455,2464,2465,2502,2503,2512,2513,2518,2519,2522,2524,2528,2529,2535,2538,2540]
def ridgeSupport641_006 : List Nat := [2545,2550,2551,2554,2556,2560,2561,2598,2599,2608,2609,2622,2623,2632,2633,2962,2964,2974,2976,3002,3003,3014,3015,3104,3109,3116,3121,3148,3149,3160,3161,3714]
def ridgeSupport641_007 : List Nat := [3715,3718,3719,5133,5136,5139,5143,5145,5148,5151,5155,5177,5179,5187,5190,5193,5196,5199,5203,5225,5227,5235,5238,5380,5381,5416,5417,5512,5513,5858,5860,5871]
def ridgeSupport641_008 : List Nat := [5874,5889,5890,5891,5892,5897,5898,5906,5908,5919,5922,5937,5938,5939,5940,5945,5946,6026,6027,6029,6031,6063,6064,6065,6066,6074,6076,6087,6090,6105,6106,6107]
def ridgeSupport641_009 : List Nat := [6108,6113,6114,6194,6195,6197,6199,6231,6232,6233,6234]
cert_ridgeSupport_code_3 641
cert_ridgeSupport_rest_2 641 000 0
cert_ridgeSupport_rest_2 641 001 416
cert_ridgeSupport_rest_2 641 002 832
cert_ridgeSupport_rest_2 641 003 1248
cert_ridgeSupport_rest_2 641 004 1664
cert_ridgeSupport_rest_2 641 005 2080
cert_ridgeSupport_rest_2 641 006 2496
cert_ridgeSupport_rest_2 641 007 2912
cert_ridgeSupport_rest_2 641 008 3328
cert_ridgeSupport_rest_2 641 009 3744
cert_ridgeSupport_rest_2 641 010 3887
cert_ridgeSupport_suffix_4 641 010
cert_ridgeSupport_suffix_3 641 009 010
cert_ridgeSupport_suffix_3 641 008 009
cert_ridgeSupport_suffix_3 641 007 008
cert_ridgeSupport_suffix_3 641 006 007
cert_ridgeSupport_suffix_3 641 005 006
cert_ridgeSupport_suffix_3 641 004 005
cert_ridgeSupport_suffix_3 641 003 004
cert_ridgeSupport_suffix_3 641 002 003
cert_ridgeSupport_suffix_3 641 001 002
cert_ridgeSupport_suffix_3 641 000 001
cert_ridgeSupport_source_3 641 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
