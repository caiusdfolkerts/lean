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
def ridgeSupport138_000 : List Nat := [6,38,41,44,45,175,176,178,183,185,210,213,215,218,220,222,225,227,230,232,615,617,620,621,623,652,654,655,658,660,664,666]
def ridgeSupport138_001 : List Nat := [667,670,672,687,689,690,692,693,695,697,698,700,701,704,705,708,710,711,713,714,716,718,719,721,722,725,726,751,752,754,755,756]
def ridgeSupport138_002 : List Nat := [757,759,760,762,763,765,766,2636,2637,2642,2643,2644,2645,2646,2647,2650,2651,2656,2657,2660,2661,2666,2667,2668,2669,2670,2671,2674,2675,2680,2681,2690]
def ridgeSupport138_003 : List Nat := [2691,2692,2693,2694,2695,2714,2715,2716,2717,2718,2719,2738,2739,2740,2741,2742,2743,2762,2763,2764,2765,2766,2767,2786,2787,2788,2789,2790,2791,2810,2811,2812]
def ridgeSupport138_004 : List Nat := [2813,2814,2815,2831,2833,2834,2835,2836,2837,2838,2839,2841,2844,2847,2850,2896,2897,2908,2909,2913,2916,2919,2922,2932,2933,2944,2945,2968,2969,2980,2981,2985]
def ridgeSupport138_005 : List Nat := [2988,2991,2994,3004,3005,3016,3017,3110,3111,3122,3123,3131,3133,3137,3139,3146,3147,3158,3159,4222,4223,4234,4235,4258,4259,4270,4271,4281,4284,4287,4290,4294]
def ridgeSupport138_006 : List Nat := [4295,4306,4307,4330,4331,4342,4343,4353,4356,4359,4362,4436,4437,4448,4449,4472,4473,4484,4485,4499,4501,4505,4507,5204,5205,5210,5211,5212,5213,5217,5220,5223]
def ridgeSupport138_007 : List Nat := [5226,5237,5239,5290,5291,5296,5297,5306,5307,5522,5523,5524,5525,5526,5527,6122,6123,6124,6125,6126,6127,6143,6145,6146,6147,6148,6149,6155,6157,6158,6159,6160]
def ridgeSupport138_008 : List Nat := [6161,6166,6167,6172,6173,6184,6185,6190,6191,6218,6219,6224,6225,6435,6438,6441,6444,6453,6456,6459,6462,6491,6493,6497,6499]
def ridgeSupport138_code : Nat := 0x1963cb0e5772b793ec9de4e326b92cc94e49b247851c28612f09582fc1760a705181dc0e605f02d811c08603f01d80dc05e017009803c016006fff7efbf75fb6fd97ebbf5565eb2d595aca564eb254bba5d52c69614aba5551de8eb46aa33d1928c345da2e516e8b5455a2a466e3331958c9c6163091798bc45862c11558aa442a20f104880c3de1ed0eb875434e1a50c7863430a17f0bc85cc2be15d0a3851422e11507f83f315d8acc4b625310d882c3d61db0cd864c276132f25790bbd5de2ec975ebac5d4ae95748b995cc2e05700b755ba2da96ceb645b0ad756b8b515a82c8963eb1c58cac5d62cb1558a2c4d624b11587abfd5fcafd57e2bed5f4ae75732b955c8ae35712b3d59cacd5662b2d594ab755b2ad5568ab35592a7d53ca9d54e2a6d534a875432a15508a8354129e54f0a7353929bd4dca6d53629ad4d4a6553229854c0a5b52d295d4aca5552a294d4a4a4d5260bf85fa2fb17d0be05ee2f517a0bcc5e42f01778b585aa2d21688b3c59c2cc1650b2458e2c61620b045802bd15e0ae85722b715a8ad05642b11578a8053c29b14d0a605282921478a3851826f13689b04d226707403981c60e106f03701b40d706a83481720b705902c015e02d01600a404c006
def ridgeSupport138_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport138_code
def ridgeSupport138_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport138_code
def ridgeSupport138_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport138_code
def ridgeSupport138_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport138_code
def ridgeSupport138_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport138_code
def ridgeSupport138_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport138_code
def ridgeSupport138_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport138_code
def ridgeSupport138_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport138_code
def ridgeSupport138_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport138_code
def ridgeSupport138_rest_009 : Nat := PackedRawNatGrowth.drop 3653 ridgeSupport138_code
def ridgeSupport138_suffix_009 : List Nat := []
def ridgeSupport138_suffix_008 : List Nat := ridgeSupport138_008 ++ ridgeSupport138_suffix_009
def ridgeSupport138_suffix_007 : List Nat := ridgeSupport138_007 ++ ridgeSupport138_suffix_008
def ridgeSupport138_suffix_006 : List Nat := ridgeSupport138_006 ++ ridgeSupport138_suffix_007
def ridgeSupport138_suffix_005 : List Nat := ridgeSupport138_005 ++ ridgeSupport138_suffix_006
def ridgeSupport138_suffix_004 : List Nat := ridgeSupport138_004 ++ ridgeSupport138_suffix_005
def ridgeSupport138_suffix_003 : List Nat := ridgeSupport138_003 ++ ridgeSupport138_suffix_004
def ridgeSupport138_suffix_002 : List Nat := ridgeSupport138_002 ++ ridgeSupport138_suffix_003
def ridgeSupport138_suffix_001 : List Nat := ridgeSupport138_001 ++ ridgeSupport138_suffix_002
def ridgeSupport138_suffix_000 : List Nat := ridgeSupport138_000 ++ ridgeSupport138_suffix_001
theorem ridgeSupport138_source : candidateSupports 138 =
    (PackedRawNatGrowth.readList 13 281 ridgeSupport138_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
