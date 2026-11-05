module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport266_000 : List Nat := [7,39,42,44,46,187,188,190,195,197,211,212,214,219,221,234,237,239,242,244,627,629,632,633,635,651,653,656,657,659,676,678]
def ridgeSupport266_001 : List Nat := [679,682,684,687,688,690,691,694,695,696,698,699,701,706,707,729,731,732,734,735,737,739,740,742,743,746,747,750,752,753,755,756]
def ridgeSupport266_002 : List Nat := [758,760,761,763,764,767,768,2638,2639,2644,2645,2648,2649,2650,2651,2652,2653,2658,2659,2662,2663,2668,2669,2672,2673,2674,2675,2676,2677,2682,2683,2696]
def ridgeSupport266_003 : List Nat := [2697,2698,2699,2700,2701,2720,2721,2722,2723,2724,2725,2744,2745,2746,2747,2748,2749,2768,2769,2770,2771,2772,2773,2792,2793,2794,2795,2796,2797,2816,2817,2818]
def ridgeSupport266_004 : List Nat := [2819,2820,2821,2829,2832,2835,2838,2840,2841,2842,2843,2844,2845,2846,2848,2898,2899,2910,2911,2912,2914,2918,2920,2934,2935,2946,2947,3040,3041,3052,3053,3057]
def ridgeSupport266_005 : List Nat := [3060,3063,3066,3076,3077,3088,3089,3112,3113,3124,3125,3129,3132,3135,3138,3148,3149,3160,3161,4224,4225,4236,4237,4260,4261,4272,4273,4280,4282,4286,4288,4366]
def ridgeSupport266_006 : List Nat := [4367,4378,4379,4402,4403,4414,4415,4425,4428,4431,4434,4438,4439,4450,4451,4474,4475,4486,4487,4497,4500,4503,4506,5878,5879,5882,5883,5886,5887,5890,5891,5894]
def ridgeSupport266_007 : List Nat := [5895,5898,5899,5912,5913,5914,5915,5916,5917,5936,5937,5938,5939,5940,5941,5949,5952,5955,5958,5960,5961,5962,5963,5964,5965,5966,5968,5973,5976,5979,5982,5984]
def ridgeSupport266_008 : List Nat := [5985,5986,5987,5988,5989,5990,5992,5996,5998,5999,6001,6006,6007,6008,6010,6014,6016,6030,6031,6042,6043,6044,6046,6050,6052,6057,6059,6117,6120,6123,6126,6136]
def ridgeSupport266_009 : List Nat := [6137,6148,6149,6153,6156,6159,6162,6164,6169,6171,6174,6177,6180,6190,6191,6202,6203,6207,6210,6213,6216,6218,6223,6780,6781,6792,6793,6800,6802,6806,6808,6816]
def ridgeSupport266_010 : List Nat := [6817,6819,6821,6828,6829,6886,6887,6898,6899,6909,6912,6915,6918,6922,6923,6926,6931,6934,6935,6940,6941,6952,6953,6963,6966,6969,6972,6976,6977,6980,6985,6988]
def ridgeSupport266_011 : List Nat := [6989,7438,7439,7442,7443,7446,7447,7448,7450,7461,7464,7467,7470,7524,7525,7534,7535,7540,7541,7760,7761,7762,7763,7764,7765]
def ridgeSupport266_code : Nat := 0x1e55f2a794fca5e51f2875d7ae9d6feb77597ac9d2ee95f4a3a4bd1ae8c745fa2dd13e89743fa1db4dda66d27689b41da06cf3673b36d99eca7651b1dd8e6c5f62db13d876c2f615b06d81ec035fbaf3d796b9f5cdaadd566a97547aa1d506a6352da92d486a27511a7dd3e613f095848c22e10b07f83bc1d60bf05d824c10e07b037819c0a604b01f80cc04e0170097f9bfc5fbafd77e8bf2deaef537a4bd15e7af3979bbcd5e3ef1d780bbf5deaef1777bbb5dc6edf76ebb65da2ecd765bb25d8eec5761bb05d7aeb7758baadd42e9d74dba65d2ee95749ba45d1ae87740b9edcd6e69733b995cc6e6171db8e5c6ee35719b8c5c2ee15707b835c0ee056ffb7f5beedf56f7b7b466a32f1948c8c61e30d17b8bd458e2c51578ab454a29f14c8a4c4fe27d133899446e23510f887430217d0ba85c42c61610a5852423611908184031658b0c4d626310987ec3c61cb0d5868c296143045820c056022fe97eebf45f8afb57d8be15f02e0d704b775bb2da16ccb625b02d7d6bcb535a92c8163cb1d58e2c6d634b1958c2c59626b10586ac15608b035812c05600aed5762bad5d4ae95742b555a8ad35692b455a0abd55e2aed574ab955c2a95548aa35512a85540a8d5462a2d514a8954429ed4f4a7553a29cd4e4a7153829b54d8a67533298d4c4a5d52e296d4b4a5952c29554a8a4f5270c005fe2fc17d8be45f02f617a0bcc5e22f01770bac5d42e71730b905c62e116f8b785b82db16c8b0c5842bd15d8ae85702b715b0acc5642b01578ab05542a71530a905262911480a3451627b13c89e04ea27307a03c81de0ed07503741b60d606a034c18a0c305f02f017602e01600a804e007
def ridgeSupport266_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport266_code
def ridgeSupport266_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport266_code
def ridgeSupport266_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport266_code
def ridgeSupport266_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport266_code
def ridgeSupport266_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport266_code
def ridgeSupport266_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport266_code
def ridgeSupport266_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport266_code
def ridgeSupport266_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport266_code
def ridgeSupport266_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport266_code
def ridgeSupport266_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport266_code
def ridgeSupport266_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport266_code
def ridgeSupport266_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport266_code
def ridgeSupport266_rest_012 : Nat := PackedRawNatGrowth.drop 4901 ridgeSupport266_code
def ridgeSupport266_suffix_012 : List Nat := []
def ridgeSupport266_suffix_011 : List Nat := ridgeSupport266_011 ++ ridgeSupport266_suffix_012
def ridgeSupport266_suffix_010 : List Nat := ridgeSupport266_010 ++ ridgeSupport266_suffix_011
def ridgeSupport266_suffix_009 : List Nat := ridgeSupport266_009 ++ ridgeSupport266_suffix_010
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
    (PackedRawNatGrowth.readList 13 377 ridgeSupport266_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
