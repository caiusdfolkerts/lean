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
def ridgeSupport67_000 : List Nat := [1,5,9,10,11,131,133,134,137,139,143,145,146,149,151,155,157,158,161,163,203,205,206,209,211,215,217,218,221,223,227,229]
def ridgeSupport67_001 : List Nat := [230,233,235,275,276,278,279,280,281,283,284,286,287,289,290,296,297,299,300,301,302,304,305,307,308,310,311,317,318,320,321,322]
def ridgeSupport67_002 : List Nat := [323,325,326,328,329,331,332,1864,1865,1866,1867,1868,1869,1870,1871,1876,1877,1882,1883,1888,1889,1890,1891,1892,1893,1894,1895,1900,1901,1906,1907,1912]
def ridgeSupport67_003 : List Nat := [1913,1914,1915,1916,1917,1936,1937,1938,1939,1940,1941,1960,1961,1962,1963,1964,1965,1984,1985,1986,1987,1988,1989,2008,2009,2010,2011,2012,2013,2032,2033,2034]
def ridgeSupport67_004 : List Nat := [2035,2036,2037,2056,2057,2058,2059,2060,2061,2065,2067,2071,2073,2077,2079,2584,2585,2596,2597,2620,2621,2632,2633,2647,2649,2653,2655,2656,2657,2668,2669,2692]
def ridgeSupport67_005 : List Nat := [2693,2704,2705,2719,2721,2725,2727,2728,2729,2740,2741,2764,2765,2776,2777,2791,2793,2797,2799,3352,3353,3364,3365,3388,3389,3400,3401,3415,3417,3421,3423,3424]
def ridgeSupport67_006 : List Nat := [3425,3436,3437,3460,3461,3472,3473,3487,3489,3493,3495,3496,3497,3508,3509,3532,3533,3544,3545,3559,3561,3565,3567,7048,7049,7050,7051,7052,7053,7672,7673,7674]
def ridgeSupport67_007 : List Nat := [7675,7676,7677,7696,7697,7698,7699,7700,7701,7708,7709,7710,7711,7712,7713,7825,7827,7831,7833,7843,7845,7849,7851,7861,7863,7867,7869,7993,7995,7999,8001,8011]
cert_ridgeSupport_7 67 008 8013 8017 8019 8029 8031 8035 8037
cert_ridgeSupport_code_3 67
cert_ridgeSupport_rest_2 67 000 0
cert_ridgeSupport_rest_2 67 001 448
cert_ridgeSupport_rest_2 67 002 896
cert_ridgeSupport_rest_2 67 003 1344
cert_ridgeSupport_rest_2 67 004 1792
cert_ridgeSupport_rest_2 67 005 2240
cert_ridgeSupport_rest_2 67 006 2688
cert_ridgeSupport_rest_2 67 007 3136
cert_ridgeSupport_rest_2 67 008 3584
cert_ridgeSupport_rest_2 67 009 3682
cert_ridgeSupport_suffix_4 67 009
cert_ridgeSupport_suffix_3 67 008 009
cert_ridgeSupport_suffix_3 67 007 008
cert_ridgeSupport_suffix_3 67 006 007
cert_ridgeSupport_suffix_3 67 005 006
cert_ridgeSupport_suffix_3 67 004 005
cert_ridgeSupport_suffix_3 67 003 004
cert_ridgeSupport_suffix_3 67 002 003
cert_ridgeSupport_suffix_3 67 001 002
cert_ridgeSupport_suffix_3 67 000 001
cert_ridgeSupport_source_3 67 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
