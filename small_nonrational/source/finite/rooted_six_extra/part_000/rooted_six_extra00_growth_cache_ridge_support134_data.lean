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
def ridgeSupport134_000 : List Nat := [2,36,39,42,43,131,132,134,139,141,166,169,171,174,176,178,181,183,186,188,623,625,628,629,631,660,662,663,666,668,672,674]
def ridgeSupport134_001 : List Nat := [675,678,680,695,697,698,700,701,703,705,706,708,709,712,713,716,718,719,721,722,724,726,727,729,730,733,734,759,760,762,763,764]
def ridgeSupport134_002 : List Nat := [765,767,768,770,771,773,774,2344,2345,2350,2351,2352,2353,2354,2355,2358,2359,2364,2365,2368,2369,2374,2375,2376,2377,2378,2379,2382,2383,2388,2389,2398]
def ridgeSupport134_003 : List Nat := [2399,2400,2401,2402,2403,2422,2423,2424,2425,2426,2427,2446,2447,2448,2449,2450,2451,2470,2471,2472,2473,2474,2475,2494,2495,2496,2497,2498,2499,2518,2519,2520]
def ridgeSupport134_004 : List Nat := [2521,2522,2523,2539,2541,2542,2543,2544,2545,2546,2547,2549,2552,2555,2558,2604,2605,2616,2617,2621,2624,2627,2630,2640,2641,2652,2653,2676,2677,2688,2689,2693]
def ridgeSupport134_005 : List Nat := [2696,2699,2702,2712,2713,2724,2725,2818,2819,2830,2831,2839,2841,2845,2847,2854,2855,2866,2867,4650,4651,4662,4663,4686,4687,4698,4699,4709,4712,4715,4718,4722]
def ridgeSupport134_006 : List Nat := [4723,4734,4735,4758,4759,4770,4771,4781,4784,4787,4790,4864,4865,4876,4877,4900,4901,4912,4913,4927,4929,4933,4935,7126,7127,7128,7129,7130,7131,7774,7775,7776]
def ridgeSupport134_007 : List Nat := [7777,7778,7779,7795,7797,7798,7799,7800,7801,7807,7809,7810,7811,7812,7813,7818,7819,7824,7825,7836,7837,7842,7843,7870,7871,7876,7877,8279,8282,8285,8288,8297]
def ridgeSupport134_008 : List Nat := [8300,8303,8306,8335,8337,8341,8343]
def ridgeSupport134_code : Nat := 0x20978256091823e07281be06c81a6060817605a815dec57b11ebf7af9ea37a89e9d7a71e917a41e8b7a29e857a11e837a09e8179fde7979e1e7779d9e7579cde637989e617981e5f7979bdb6f69bd96f61bd76f593474d153414cfd3314cc13254c9130d4c313014c012b64acd2b04ab52a34a892974a5927f49f927349c926e49ad268499525b496924f493923748d922b48a8b332cc8b272c98b1f2c74b192c5cb0f2c38b032c08aa52a90a992a60a8e2a2ca882a14a812a00a7529d0a5d2970a512940a46290ca4028f4a3928e0a2d28b09fe27ec9f827d49f327c89f127c09ef27b89ed27ac9db27689d927609d727589c327089c127009bf26f89ab26a89a926a09a726989932648991264098f263897b25e897925e097725d89632588961258095f2578955255094f253894b252894925209472518941250093d24f093724d893324c893124c092f24b892924a03060c143030c083000bfc2fd0bf02fb0be82f80bdc2de0b742da0b642d70b582d40b482d10b3c2ce0b302c90b202c50b102c20b042bf0af42bc0ae82b90adc2a80a982a30a882a00a7029a0a5c2960a5027709d427409c426f02f00ba02dc0b502c80b002b80ab02a40a6023408b0218084020c02b00a80270090002
def ridgeSupport134_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport134_code
def ridgeSupport134_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport134_code
def ridgeSupport134_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport134_code
def ridgeSupport134_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport134_code
def ridgeSupport134_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport134_code
def ridgeSupport134_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport134_code
def ridgeSupport134_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport134_code
def ridgeSupport134_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport134_code
def ridgeSupport134_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport134_code
def ridgeSupport134_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport134_code
def ridgeSupport134_suffix_009 : List Nat := []
def ridgeSupport134_suffix_008 : List Nat := ridgeSupport134_008 ++ ridgeSupport134_suffix_009
def ridgeSupport134_suffix_007 : List Nat := ridgeSupport134_007 ++ ridgeSupport134_suffix_008
def ridgeSupport134_suffix_006 : List Nat := ridgeSupport134_006 ++ ridgeSupport134_suffix_007
def ridgeSupport134_suffix_005 : List Nat := ridgeSupport134_005 ++ ridgeSupport134_suffix_006
def ridgeSupport134_suffix_004 : List Nat := ridgeSupport134_004 ++ ridgeSupport134_suffix_005
def ridgeSupport134_suffix_003 : List Nat := ridgeSupport134_003 ++ ridgeSupport134_suffix_004
def ridgeSupport134_suffix_002 : List Nat := ridgeSupport134_002 ++ ridgeSupport134_suffix_003
def ridgeSupport134_suffix_001 : List Nat := ridgeSupport134_001 ++ ridgeSupport134_suffix_002
def ridgeSupport134_suffix_000 : List Nat := ridgeSupport134_000 ++ ridgeSupport134_suffix_001
theorem ridgeSupport134_source : candidateSupports 134 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport134_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
