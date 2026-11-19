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
def ridgeSupport131_000 : List Nat := [2,6,9,12,13,130,132,135,136,138,167,169,170,173,175,179,181,182,185,187,202,204,207,208,210,239,241,242,245,247,251,253]
def ridgeSupport131_001 : List Nat := [254,257,259,274,276,277,279,280,282,284,285,287,288,291,292,295,297,298,300,301,303,305,306,308,309,312,313,338,339,341,342,343]
def ridgeSupport131_002 : List Nat := [344,346,347,349,350,352,353,1864,1865,1870,1871,1872,1873,1874,1875,1878,1879,1884,1885,1888,1889,1894,1895,1896,1897,1898,1899,1902,1903,1908,1909,1918]
def ridgeSupport131_003 : List Nat := [1919,1920,1921,1922,1923,1942,1943,1944,1945,1946,1947,1966,1967,1968,1969,1970,1971,1990,1991,1992,1993,1994,1995,2014,2015,2016,2017,2018,2019,2038,2039,2040]
def ridgeSupport131_004 : List Nat := [2041,2042,2043,2059,2061,2062,2063,2064,2065,2066,2067,2069,2072,2075,2078,2586,2587,2598,2599,2622,2623,2634,2635,2645,2648,2651,2654,2658,2659,2670,2671,2694]
def ridgeSupport131_005 : List Nat := [2695,2706,2707,2717,2720,2723,2726,2800,2801,2812,2813,2836,2837,2848,2849,2863,2865,2869,2871,3354,3355,3366,3367,3390,3391,3402,3403,3413,3416,3419,3422,3426]
def ridgeSupport131_006 : List Nat := [3427,3438,3439,3462,3463,3474,3475,3485,3488,3491,3494,3568,3569,3580,3581,3604,3605,3616,3617,3631,3633,3637,3639,7054,7055,7056,7057,7058,7059,7678,7679,7680]
def ridgeSupport131_007 : List Nat := [7681,7682,7683,7699,7701,7702,7703,7704,7705,7711,7713,7714,7715,7716,7717,7823,7826,7829,7832,7841,7844,7847,7850,7879,7881,7885,7887,7991,7994,7997,8000,8009]
cert_ridgeSupport_7 131 008 8012 8015 8018 8047 8049 8053 8055
cert_ridgeSupport_code_3 131
cert_ridgeSupport_rest_2 131 000 0
cert_ridgeSupport_rest_2 131 001 448
cert_ridgeSupport_rest_2 131 002 896
cert_ridgeSupport_rest_2 131 003 1344
cert_ridgeSupport_rest_2 131 004 1792
cert_ridgeSupport_rest_2 131 005 2240
cert_ridgeSupport_rest_2 131 006 2688
cert_ridgeSupport_rest_2 131 007 3136
cert_ridgeSupport_rest_2 131 008 3584
cert_ridgeSupport_rest_2 131 009 3682
cert_ridgeSupport_suffix_4 131 009
cert_ridgeSupport_suffix_3 131 008 009
cert_ridgeSupport_suffix_3 131 007 008
cert_ridgeSupport_suffix_3 131 006 007
cert_ridgeSupport_suffix_3 131 005 006
cert_ridgeSupport_suffix_3 131 004 005
cert_ridgeSupport_suffix_3 131 003 004
cert_ridgeSupport_suffix_3 131 002 003
cert_ridgeSupport_suffix_3 131 001 002
cert_ridgeSupport_suffix_3 131 000 001
cert_ridgeSupport_source_3 131 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
