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
def ridgeSupport262_000 : List Nat := [3,37,40,42,44,143,144,146,151,153,167,168,170,175,177,190,193,195,198,200,635,637,640,641,643,659,661,664,665,667,684,686]
def ridgeSupport262_001 : List Nat := [687,690,692,695,696,698,699,702,703,704,706,707,709,714,715,737,739,740,742,743,745,747,748,750,751,754,755,758,760,761,763,764]
def ridgeSupport262_002 : List Nat := [766,768,769,771,772,775,776,2346,2347,2352,2353,2356,2357,2358,2359,2360,2361,2366,2367,2370,2371,2376,2377,2380,2381,2382,2383,2384,2385,2390,2391,2404]
def ridgeSupport262_003 : List Nat := [2405,2406,2407,2408,2409,2428,2429,2430,2431,2432,2433,2452,2453,2454,2455,2456,2457,2476,2477,2478,2479,2480,2481,2500,2501,2502,2503,2504,2505,2524,2525,2526]
def ridgeSupport262_004 : List Nat := [2527,2528,2529,2537,2540,2543,2546,2548,2549,2550,2551,2552,2553,2554,2556,2606,2607,2618,2619,2620,2622,2626,2628,2642,2643,2654,2655,2748,2749,2760,2761,2765]
def ridgeSupport262_005 : List Nat := [2768,2771,2774,2784,2785,2796,2797,2820,2821,2832,2833,2837,2840,2843,2846,2856,2857,2868,2869,4652,4653,4664,4665,4688,4689,4700,4701,4708,4710,4714,4716,4794]
def ridgeSupport262_006 : List Nat := [4795,4806,4807,4830,4831,4842,4843,4853,4856,4859,4862,4866,4867,4878,4879,4902,4903,4914,4915,4925,4928,4931,4934,7132,7133,7134,7135,7136,7137,7780,7781,7782]
def ridgeSupport262_007 : List Nat := [7783,7784,7785,7793,7796,7799,7801,7802,7803,7805,7808,7811,7813,7814,7815,7820,7821,7826,7827,7854,7855,7860,7861,7872,7873,7878,7879,8278,8280,8284,8286,8315]
def ridgeSupport262_008 : List Nat := [8318,8321,8324,8333,8336,8339,8342]
def ridgeSupport262_code : Nat := 0x2096824e0908236084820607e81ee05e81720588159ec77b19ec17b01eb57ad1eaf7ab9e937a49e8d7a31e877a19e857a0de8079f5e7b79e9e7979dde7479c5e6979a1e677999e657991be16f81bdf6f79bdd6f713464d0d3404cf53334cc93274c9930f4c393034c092fe4bed2f84bd52eb4ba92df4b792c74b192bb4ae926c49a9266499125d4971251494123948e122d48b0b352cd0b292ca0b1e2c6cb182c54b112c40b052c10aed2bb0ae12b80ad62b4cad02b34ac92b20abd2af0a5f2978a532948a442908a3e28f0a3b28e8a2f28b89fc27e89f927e09f727d89f527d09f227bc9ec27a49e127809df27789dd27709c927209c727189c527109b126c09af26b89ad26b0999266099726589952650981260097f25f897d25f096925a0967259896525909572558951254094f253894d25309492520943250893f24f893924e093724d893524d093124c092b24a83080c1c3040c0c3010c002fe0bf02fb0be42f80bd82f30bc82ef0bb82ec0bac2e90b9c2e60b902e30b842cb0b282c50b0c2c20b002bf0af82bb0ae82b80adc2b40ac82af0ab82ac0a6c2990a602950a4c2830a0428009f427b03200c6030c0c102f80b102bc0aa02a00a702640970248090023c02c00a80280094003
def ridgeSupport262_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport262_code
def ridgeSupport262_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport262_code
def ridgeSupport262_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport262_code
def ridgeSupport262_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport262_code
def ridgeSupport262_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport262_code
def ridgeSupport262_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport262_code
def ridgeSupport262_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport262_code
def ridgeSupport262_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport262_code
def ridgeSupport262_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport262_code
def ridgeSupport262_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport262_code
def ridgeSupport262_suffix_009 : List Nat := []
def ridgeSupport262_suffix_008 : List Nat := ridgeSupport262_008 ++ ridgeSupport262_suffix_009
def ridgeSupport262_suffix_007 : List Nat := ridgeSupport262_007 ++ ridgeSupport262_suffix_008
def ridgeSupport262_suffix_006 : List Nat := ridgeSupport262_006 ++ ridgeSupport262_suffix_007
def ridgeSupport262_suffix_005 : List Nat := ridgeSupport262_005 ++ ridgeSupport262_suffix_006
def ridgeSupport262_suffix_004 : List Nat := ridgeSupport262_004 ++ ridgeSupport262_suffix_005
def ridgeSupport262_suffix_003 : List Nat := ridgeSupport262_003 ++ ridgeSupport262_suffix_004
def ridgeSupport262_suffix_002 : List Nat := ridgeSupport262_002 ++ ridgeSupport262_suffix_003
def ridgeSupport262_suffix_001 : List Nat := ridgeSupport262_001 ++ ridgeSupport262_suffix_002
def ridgeSupport262_suffix_000 : List Nat := ridgeSupport262_000 ++ ridgeSupport262_suffix_001
theorem ridgeSupport262_source : candidateSupports 262 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport262_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
