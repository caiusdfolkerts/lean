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
def ridgeSupport70_000 : List Nat := [1,35,39,40,41,130,133,135,138,140,142,145,147,150,152,154,157,159,162,164,624,626,627,630,632,636,638,639,642,644,648,650]
def ridgeSupport70_001 : List Nat := [651,654,656,696,697,699,700,701,702,704,705,707,708,710,711,717,718,720,721,722,723,725,726,728,729,731,732,738,739,741,742,743]
def ridgeSupport70_002 : List Nat := [744,746,747,749,750,752,753,2344,2345,2346,2347,2348,2349,2350,2351,2356,2357,2362,2363,2368,2369,2370,2371,2372,2373,2374,2375,2380,2381,2386,2387,2392]
def ridgeSupport70_003 : List Nat := [2393,2394,2395,2396,2397,2416,2417,2418,2419,2420,2421,2440,2441,2442,2443,2444,2445,2464,2465,2466,2467,2468,2469,2488,2489,2490,2491,2492,2493,2512,2513,2514]
def ridgeSupport70_004 : List Nat := [2515,2516,2517,2536,2537,2538,2539,2540,2541,2545,2547,2551,2553,2557,2559,2602,2603,2614,2615,2623,2625,2629,2631,2638,2639,2650,2651,2674,2675,2686,2687,2695]
def ridgeSupport70_005 : List Nat := [2697,2701,2703,2710,2711,2722,2723,2746,2747,2758,2759,2767,2769,2773,2775,2782,2783,2794,2795,4648,4649,4660,4661,4684,4685,4696,4697,4711,4713,4717,4719,4720]
def ridgeSupport70_006 : List Nat := [4721,4732,4733,4756,4757,4768,4769,4783,4785,4789,4791,4792,4793,4804,4805,4828,4829,4840,4841,4855,4857,4861,4863,7120,7121,7122,7123,7124,7125,7768,7769,7770]
def ridgeSupport70_007 : List Nat := [7771,7772,7773,7792,7793,7794,7795,7796,7797,7804,7805,7806,7807,7808,7809,7816,7817,7822,7823,7834,7835,7840,7841,7852,7853,7858,7859,8281,8283,8287,8289,8299]
cert_ridgeSupport_7 70 008 8301 8305 8307 8317 8319 8323 8325
cert_ridgeSupport_code_3 70
cert_ridgeSupport_rest_2 70 000 0
cert_ridgeSupport_rest_2 70 001 448
cert_ridgeSupport_rest_2 70 002 896
cert_ridgeSupport_rest_2 70 003 1344
cert_ridgeSupport_rest_2 70 004 1792
cert_ridgeSupport_rest_2 70 005 2240
cert_ridgeSupport_rest_2 70 006 2688
cert_ridgeSupport_rest_2 70 007 3136
cert_ridgeSupport_rest_2 70 008 3584
cert_ridgeSupport_rest_2 70 009 3682
cert_ridgeSupport_suffix_4 70 009
cert_ridgeSupport_suffix_3 70 008 009
cert_ridgeSupport_suffix_3 70 007 008
cert_ridgeSupport_suffix_3 70 006 007
cert_ridgeSupport_suffix_3 70 005 006
cert_ridgeSupport_suffix_3 70 004 005
cert_ridgeSupport_suffix_3 70 003 004
cert_ridgeSupport_suffix_3 70 002 003
cert_ridgeSupport_suffix_3 70 001 002
cert_ridgeSupport_suffix_3 70 000 001
cert_ridgeSupport_source_3 70 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
