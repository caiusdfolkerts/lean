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
def ridgeSupport385_000 : List Nat := [12,22,28,31,34,168,169,170,171,172,173,240,241,242,243,244,245,274,278,279,280,281,283,284,291,293,339,340,341,344,345,346]
def ridgeSupport385_001 : List Nat := [348,353,355,396,397,398,399,400,401,430,434,435,436,437,439,440,447,449,495,496,497,500,501,502,504,509,511,514,518,519,520,521]
def ridgeSupport385_002 : List Nat := [523,524,531,533,579,580,581,584,585,586,588,593,595,598,601,602,603,606,607,608,610,615,616,618,619,1889,1891,1908,1910,1920,1921,1926]
def ridgeSupport385_003 : List Nat := [1927,1968,1969,1974,1975,1988,1989,1991,1994,1997,2000,2002,2003,2009,2011,2016,2017,2022,2023,2028,2030,2064,2065,2070,2071,2088,2089,2094,2095,2129,2131,2148]
def ridgeSupport385_004 : List Nat := [2150,2160,2161,2166,2167,2208,2209,2214,2215,2228,2229,2231,2234,2237,2240,2242,2243,2249,2251,2256,2257,2262,2263,2268,2270,2304,2305,2310,2311,2328,2329,2334]
def ridgeSupport385_005 : List Nat := [2335,2598,2600,2610,2612,2638,2639,2650,2651,2813,2815,2825,2827,2858,2859,2870,2871,2897,2899,2916,2918,2928,2929,2934,2935,2976,2977,2982,2983,2996,2997,2999]
def ridgeSupport385_006 : List Nat := [3002,3005,3008,3010,3011,3017,3019,3024,3025,3030,3031,3036,3038,3072,3073,3078,3079,3096,3097,3102,3103,3366,3368,3378,3380,3406,3407,3418,3419,3581,3583,3593]
def ridgeSupport385_007 : List Nat := [3595,3626,3627,3638,3639,3894,3896,3906,3908,3934,3935,3946,3947,4109,4111,4121,4123,4154,4155,4166,4167,7078,7079,7114,7115,7210,7211,7679,7682,7685,7688,7708]
def ridgeSupport385_008 : List Nat := [7710,7712,7713,7716,7719,7727,7730,7733,7736,7756,7758,7760,7761,7764,7767,7828,7829,7831,7833,7882,7884,7886,7887,7895,7898,7901,7904,7924,7926,7928,7929,7932]
def ridgeSupport385_009 : List Nat := [7935,7996,7997,7999,8001,8050,8052,8054,8055,8116,8117,8119,8121,8170,8172,8174,8175]
cert_ridgeSupport_code_3 385
cert_ridgeSupport_rest_2 385 000 0
cert_ridgeSupport_rest_2 385 001 448
cert_ridgeSupport_rest_2 385 002 896
cert_ridgeSupport_rest_2 385 003 1344
cert_ridgeSupport_rest_2 385 004 1792
cert_ridgeSupport_rest_2 385 005 2240
cert_ridgeSupport_rest_2 385 006 2688
cert_ridgeSupport_rest_2 385 007 3136
cert_ridgeSupport_rest_2 385 008 3584
cert_ridgeSupport_rest_2 385 009 4032
cert_ridgeSupport_rest_2 385 010 4270
cert_ridgeSupport_suffix_4 385 010
cert_ridgeSupport_suffix_3 385 009 010
cert_ridgeSupport_suffix_3 385 008 009
cert_ridgeSupport_suffix_3 385 007 008
cert_ridgeSupport_suffix_3 385 006 007
cert_ridgeSupport_suffix_3 385 005 006
cert_ridgeSupport_suffix_3 385 004 005
cert_ridgeSupport_suffix_3 385 003 004
cert_ridgeSupport_suffix_3 385 002 003
cert_ridgeSupport_suffix_3 385 001 002
cert_ridgeSupport_suffix_3 385 000 001
cert_ridgeSupport_source_3 385 14 305
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
