module
prelude
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
def ridgeSupport70_008 : List Nat := [8301,8305,8307,8317,8319,8323,8325]
def ridgeSupport70_code : Nat := 0x2085820e07f81f607381c606d81ae061817e05b8165eb37ac9ead7ab1ea17a81e9b7a69e8f7a39e897a21e817a01e7f79f9e7d79f1e7579d1e7379c9e7179c1e5d7971e5b7969e597961bd56f51bd36f49bd16f412ff4bf52f94bdd2e94ba12dd4b712c54b112b94ae12b74ad52b14abd2a14a812954a5127d49f127149c126f49b5269499d259496124d493123548d122948a0aeb2ba8adf2b78ad72b54ad12b3cac72b18abb2ae8aa32a88a972a58a8f2a34a892a1ca7f29f8a7329c8a5b2968a4f2938a472914a4128fca3728d8a2b28a89ff27f49f927dc9f327c49ed27b09eb27a89e927a09d527509d327489d127409bd26f09bb26e89b926e09a526909a326889a1268098d263098b2628989262097525d097325c897125c095d257095b25689592560953254894d2530947251894525109432508941250093b24e893524d092f24b892d24b092b24a892924a02f10bc02ee0bb42eb0ba82e80b9c2e60b942e30b882dc0b6c2d90b602d60b542d30b482d10b402ce0b342c70b182c40b0c2c10b002be0af42bc0aec2b90ae02900a3828b0a282880a1028209fc27e09f027809d827309c827002900a2027c09d02680980258093024408e023008a021c085020802900a0027008c001
def ridgeSupport70_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport70_code
def ridgeSupport70_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport70_code
def ridgeSupport70_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport70_code
def ridgeSupport70_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport70_code
def ridgeSupport70_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport70_code
def ridgeSupport70_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport70_code
def ridgeSupport70_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport70_code
def ridgeSupport70_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport70_code
def ridgeSupport70_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport70_code
def ridgeSupport70_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport70_code
def ridgeSupport70_suffix_009 : List Nat := []
def ridgeSupport70_suffix_008 : List Nat := ridgeSupport70_008 ++ ridgeSupport70_suffix_009
def ridgeSupport70_suffix_007 : List Nat := ridgeSupport70_007 ++ ridgeSupport70_suffix_008
def ridgeSupport70_suffix_006 : List Nat := ridgeSupport70_006 ++ ridgeSupport70_suffix_007
def ridgeSupport70_suffix_005 : List Nat := ridgeSupport70_005 ++ ridgeSupport70_suffix_006
def ridgeSupport70_suffix_004 : List Nat := ridgeSupport70_004 ++ ridgeSupport70_suffix_005
def ridgeSupport70_suffix_003 : List Nat := ridgeSupport70_003 ++ ridgeSupport70_suffix_004
def ridgeSupport70_suffix_002 : List Nat := ridgeSupport70_002 ++ ridgeSupport70_suffix_003
def ridgeSupport70_suffix_001 : List Nat := ridgeSupport70_001 ++ ridgeSupport70_suffix_002
def ridgeSupport70_suffix_000 : List Nat := ridgeSupport70_000 ++ ridgeSupport70_suffix_001
theorem ridgeSupport70_source : candidateSupports 70 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport70_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
