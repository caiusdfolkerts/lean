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
def ridgeSupport193_000 : List Nat := [9,19,25,31,32,132,133,134,135,136,137,204,205,206,207,208,209,276,277,278,281,282,283,285,290,292,297,298,299,302,303,304]
def ridgeSupport193_001 : List Nat := [306,311,313,360,361,362,363,364,365,432,433,434,437,438,439,441,446,448,453,454,455,458,459,460,462,467,469,516,517,518,521,522]
def ridgeSupport193_002 : List Nat := [523,525,530,532,537,538,539,542,543,544,546,551,553,600,601,603,604,605,606,608,609,611,612,614,615,1901,1903,1907,1909,1912,1913,1918]
def ridgeSupport193_003 : List Nat := [1919,1960,1961,1966,1967,1987,1989,1993,1995,2000,2001,2006,2007,2008,2009,2014,2015,2021,2023,2027,2029,2056,2057,2062,2063,2080,2081,2086,2087,2141,2143,2147]
def ridgeSupport193_004 : List Nat := [2149,2152,2153,2158,2159,2200,2201,2206,2207,2227,2229,2233,2235,2240,2241,2246,2247,2248,2249,2254,2255,2261,2263,2267,2269,2296,2297,2302,2303,2320,2321,2326]
def ridgeSupport193_005 : List Nat := [2327,2597,2599,2609,2611,2642,2643,2654,2655,2669,2671,2681,2683,2714,2715,2726,2727,2909,2911,2915,2917,2920,2921,2926,2927,2968,2969,2974,2975,2995,2997,3001]
def ridgeSupport193_006 : List Nat := [3003,3008,3009,3014,3015,3016,3017,3022,3023,3029,3031,3035,3037,3064,3065,3070,3071,3088,3089,3094,3095,3365,3367,3377,3379,3410,3411,3422,3423,3437,3439,3449]
def ridgeSupport193_007 : List Nat := [3451,3482,3483,3494,3495,3893,3895,3905,3907,3938,3939,3950,3951,3965,3967,3977,3979,4010,4011,4022,4023,7072,7073,7108,7109,7204,7205,7675,7677,7681,7683,7708]
def ridgeSupport193_008 : List Nat := [7709,7714,7715,7718,7719,7723,7725,7729,7731,7756,7757,7762,7763,7766,7767,7828,7830,7832,7833,7846,7848,7850,7851,7891,7893,7897,7899,7924,7925,7930,7931,7934]
def ridgeSupport193_009 : List Nat := [7935,7996,7998,8000,8001,8014,8016,8018,8019,8116,8118,8120,8121,8134,8136,8138,8139]
cert_ridgeSupport_code_3 193
cert_ridgeSupport_rest_2 193 000 0
cert_ridgeSupport_rest_2 193 001 448
cert_ridgeSupport_rest_2 193 002 896
cert_ridgeSupport_rest_2 193 003 1344
cert_ridgeSupport_rest_2 193 004 1792
cert_ridgeSupport_rest_2 193 005 2240
cert_ridgeSupport_rest_2 193 006 2688
cert_ridgeSupport_rest_2 193 007 3136
cert_ridgeSupport_rest_2 193 008 3584
cert_ridgeSupport_rest_2 193 009 4032
cert_ridgeSupport_rest_2 193 010 4270
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
cert_ridgeSupport_source_3 193 14 305
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
