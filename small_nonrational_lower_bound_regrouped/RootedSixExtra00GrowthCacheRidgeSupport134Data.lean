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
def ridgeSupport134_000 : List Nat := [2,36,39,42,43,131,132,134,139,141,166,169,171,174,176,178,181,183,186,188,623,625,628,629,631,660,662,663,666,668,672,674]
def ridgeSupport134_001 : List Nat := [675,678,680,695,697,698,700,701,703,705,706,708,709,712,713,716,718,719,721,722,724,726,727,729,730,733,734,759,760,762,763,764]
def ridgeSupport134_002 : List Nat := [765,767,768,770,771,773,774,2344,2345,2350,2351,2352,2353,2354,2355,2358,2359,2364,2365,2368,2369,2374,2375,2376,2377,2378,2379,2382,2383,2388,2389,2398]
def ridgeSupport134_003 : List Nat := [2399,2400,2401,2402,2403,2422,2423,2424,2425,2426,2427,2446,2447,2448,2449,2450,2451,2470,2471,2472,2473,2474,2475,2494,2495,2496,2497,2498,2499,2518,2519,2520]
def ridgeSupport134_004 : List Nat := [2521,2522,2523,2539,2541,2542,2543,2544,2545,2546,2547,2549,2552,2555,2558,2604,2605,2616,2617,2621,2624,2627,2630,2640,2641,2652,2653,2676,2677,2688,2689,2693]
def ridgeSupport134_005 : List Nat := [2696,2699,2702,2712,2713,2724,2725,2818,2819,2830,2831,2839,2841,2845,2847,2854,2855,2866,2867,4650,4651,4662,4663,4686,4687,4698,4699,4709,4712,4715,4718,4722]
def ridgeSupport134_006 : List Nat := [4723,4734,4735,4758,4759,4770,4771,4781,4784,4787,4790,4864,4865,4876,4877,4900,4901,4912,4913,4927,4929,4933,4935,7126,7127,7128,7129,7130,7131,7774,7775,7776]
def ridgeSupport134_007 : List Nat := [7777,7778,7779,7795,7797,7798,7799,7800,7801,7807,7809,7810,7811,7812,7813,7818,7819,7824,7825,7836,7837,7842,7843,7870,7871,7876,7877,8279,8282,8285,8288,8297]
cert_ridgeSupport_7 134 008 8300 8303 8306 8335 8337 8341 8343
cert_ridgeSupport_code_3 134
cert_ridgeSupport_rest_2 134 000 0
cert_ridgeSupport_rest_2 134 001 448
cert_ridgeSupport_rest_2 134 002 896
cert_ridgeSupport_rest_2 134 003 1344
cert_ridgeSupport_rest_2 134 004 1792
cert_ridgeSupport_rest_2 134 005 2240
cert_ridgeSupport_rest_2 134 006 2688
cert_ridgeSupport_rest_2 134 007 3136
cert_ridgeSupport_rest_2 134 008 3584
cert_ridgeSupport_rest_2 134 009 3682
cert_ridgeSupport_suffix_4 134 009
cert_ridgeSupport_suffix_3 134 008 009
cert_ridgeSupport_suffix_3 134 007 008
cert_ridgeSupport_suffix_3 134 006 007
cert_ridgeSupport_suffix_3 134 005 006
cert_ridgeSupport_suffix_3 134 004 005
cert_ridgeSupport_suffix_3 134 003 004
cert_ridgeSupport_suffix_3 134 002 003
cert_ridgeSupport_suffix_3 134 001 002
cert_ridgeSupport_suffix_3 134 000 001
cert_ridgeSupport_source_3 134 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
