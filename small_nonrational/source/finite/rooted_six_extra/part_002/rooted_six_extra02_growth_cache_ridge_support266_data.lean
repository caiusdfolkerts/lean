module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport266_000 : List Nat := [7,39,42,44,46,187,188,190,195,197,211,212,214,219,221,234,237,239,242,244,627,629,632,633,635,651,653,656,657,659,676,678]
def ridgeSupport266_001 : List Nat := [679,682,684,687,688,690,691,694,695,696,698,699,701,706,707,729,731,732,734,735,737,739,740,742,743,746,747,750,752,753,755,756]
def ridgeSupport266_002 : List Nat := [758,760,761,763,764,767,768,2638,2639,2644,2645,2648,2649,2650,2651,2652,2653,2658,2659,2662,2663,2668,2669,2672,2673,2674,2675,2676,2677,2682,2683,2696]
def ridgeSupport266_003 : List Nat := [2697,2698,2699,2700,2701,2720,2721,2722,2723,2724,2725,2744,2745,2746,2747,2748,2749,2768,2769,2770,2771,2772,2773,2792,2793,2794,2795,2796,2797,2816,2817,2818]
def ridgeSupport266_004 : List Nat := [2819,2820,2821,2829,2832,2835,2838,2840,2841,2842,2843,2844,2845,2846,2848,2898,2899,2910,2911,2912,2914,2918,2920,2934,2935,2946,2947,3040,3041,3052,3053,3057]
def ridgeSupport266_005 : List Nat := [3060,3063,3066,3076,3077,3088,3089,3112,3113,3124,3125,3129,3132,3135,3138,3148,3149,3160,3161,4224,4225,4236,4237,4260,4261,4272,4273,4280,4282,4286,4288,4366]
def ridgeSupport266_006 : List Nat := [4367,4378,4379,4402,4403,4414,4415,4425,4428,4431,4434,4438,4439,4450,4451,4474,4475,4486,4487,4497,4500,4503,4506,5206,5207,5210,5211,5214,5215,5216,5218,5229]
def ridgeSupport266_007 : List Nat := [5232,5235,5238,5292,5293,5302,5303,5308,5309,5528,5529,5530,5531,5532,5533,6128,6129,6130,6131,6132,6133,6141,6144,6147,6149,6150,6151,6153,6156,6159,6161,6162]
def ridgeSupport266_008 : List Nat := [6163,6168,6169,6174,6175,6202,6203,6208,6209,6220,6221,6226,6227,6434,6436,6440,6442,6471,6474,6477,6480,6489,6492,6495,6498]
def ridgeSupport266_code : Nat := 0x1962cafe5732b3950ca6e52b28f92ac946493245853c296137099841c2060ef07581fc0f6067031813c09604701f80cc04e01f00d805c01e002ffb7f5bfa5fcefe57f1bf85676b3959bacd5666b314bda5e52de96d4ada5651da8e7470a36d18a8c145fa2f516e8b5457a2b466a32f1948c8c61e30d17b8bd458e2c51578ab454a29f14c8a4c4fe27d133899446e23510f887430217d0ba85c42c61610a5852423611908184031658b0c4d626310987ec3c61cb0d5868c296143045820c056022fe97eebf45f8afb57d8be15f02e0d704b775bb2da16ccb625b02d7d6bcb535a92c8163cb1d58e2c6d634b1958c2c59626b10586ac15608b035812c05600aed5762bad5d4ae95742b555a8ad35692b455a0abd55e2aed574ab955c2a95548aa35512a85540a8d5462a2d514a8954429ed4f4a7553a29cd4e4a7153829b54d8a67533298d4c4a5d52e296d4b4a5952c29554a8a4f5270c005fe2fc17d8be45f02f617a0bcc5e22f01770bac5d42e71730b905c62e116f8b785b82db16c8b0c5842bd15d8ae85702b715b0acc5642b01578ab05542a71530a905262911480a3451627b13c89e04ea27307a03c81de0ed07503741b60d606a034c18a0c305f02f017602e01600a804e007
def ridgeSupport266_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport266_code
def ridgeSupport266_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport266_code
def ridgeSupport266_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport266_code
def ridgeSupport266_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport266_code
def ridgeSupport266_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport266_code
def ridgeSupport266_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport266_code
def ridgeSupport266_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport266_code
def ridgeSupport266_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport266_code
def ridgeSupport266_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport266_code
def ridgeSupport266_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport266_code
def ridgeSupport266_suffix_009 : List Nat := []
def ridgeSupport266_suffix_008 : List Nat := ridgeSupport266_008 ++ ridgeSupport266_suffix_009
def ridgeSupport266_suffix_007 : List Nat := ridgeSupport266_007 ++ ridgeSupport266_suffix_008
def ridgeSupport266_suffix_006 : List Nat := ridgeSupport266_006 ++ ridgeSupport266_suffix_007
def ridgeSupport266_suffix_005 : List Nat := ridgeSupport266_005 ++ ridgeSupport266_suffix_006
def ridgeSupport266_suffix_004 : List Nat := ridgeSupport266_004 ++ ridgeSupport266_suffix_005
def ridgeSupport266_suffix_003 : List Nat := ridgeSupport266_003 ++ ridgeSupport266_suffix_004
def ridgeSupport266_suffix_002 : List Nat := ridgeSupport266_002 ++ ridgeSupport266_suffix_003
def ridgeSupport266_suffix_001 : List Nat := ridgeSupport266_001 ++ ridgeSupport266_suffix_002
def ridgeSupport266_suffix_000 : List Nat := ridgeSupport266_000 ++ ridgeSupport266_suffix_001
theorem ridgeSupport266_source : candidateSupports 266 =
    (PackedRawNatGrowth.readList 13 281 ridgeSupport266_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
