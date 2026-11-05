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
def ridgeSupport11_000 : List Nat := [0,5,6,7,8,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200]
def ridgeSupport11_001 : List Nat := [201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232]
def ridgeSupport11_002 : List Nat := [233,234,235,236,237,238,239,240,241,242,243,244,245,2876,2877,2878,2879,2880,2881,2882,2883,2884,2885,2886,2887,2888,2889,2890,2891,2892,2893,2894]
def ridgeSupport11_003 : List Nat := [2895,2896,2897,2898,2899,2900,2901,2902,2903,2904,2905,2906,2907,2908,2909,2910,2911,2912,2913,2914,2915,2916,2917,2918,2919,2920,2921,2922,2923,2924,2925,2926]
def ridgeSupport11_004 : List Nat := [2927,2928,2929,2930,2931,2932,2933,2934,2935,2936,2937,2938,2939,2940,2941,2942,2943,2944,2945,2946,2947,2948,2949,2950,2951,2952,2953,2954,2955,2956,2957,2958]
def ridgeSupport11_005 : List Nat := [2959,2960,2961,2962,2963,2964,2965,2966,2967,2968,2969,2970,2971,2972,2973,2974,2975,2976,2977,2978,2979,2980,2981,2982,2983,2984,2985,2986,2987,2988,2989,2990]
def ridgeSupport11_006 : List Nat := [2991,2992,2993,2994,2995,2996,2997,2998,2999,3000,3001,3002,3003,3004,3005,3006,3007,3008,3009,3010,3011,3012,3013,3014,3015,3016,3017,3018,3019,3020,3021,3022]
def ridgeSupport11_007 : List Nat := [3023,3024,3025,3026,3027,3028,3029,3030,3031,3032,3033,3034,3035,3036,3037,3038,3039,3040,3041,3042,3043,3044,3045,3046,3047,3048,3049,3050,3051,3052,3053,3054]
def ridgeSupport11_008 : List Nat := [3055,3056,3057,3058,3059,3060,3061,3062,3063,3064,3065,3066,3067,3068,3069,3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085,3086]
def ridgeSupport11_009 : List Nat := [3087,3088,3089,3090,3091,3092,3093,3094,3095,3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117,3118]
def ridgeSupport11_010 : List Nat := [3119,3120,3121,3122,3123,3124,3125,3126,3127,3128,3129,3130,3131,3132,3133,3134,3135,3136,3137,3138,3139,3140,3141,3142,3143,3144,3145,3146,3147,3148,3149,3150]
def ridgeSupport11_011 : List Nat := [3151,3152,3153,3154,3155,3156,3157,3158,3159,3160,3161,3162,3163,5216,5217,5218,5219,5220,5221,5222,5223,5224,5225,5226,5227,5228,5229,5230,5231,5232,5233,5234]
def ridgeSupport11_012 : List Nat := [5235,5236,5237,5238,5239,5552,5553,5554,5555,5556,5557,5558,5559,5560,5561,5562,5563,5564,5565,5566,5567,5568,5569,5570,5571,5572,5573,5574,5575,6164,6165,6166]
def ridgeSupport11_013 : List Nat := [6167,6168,6169,6170,6171,6172,6173,6174,6175,6176,6177,6178,6179,6180,6181,6182,6183,6184,6185,6186,6187,6188,6189,6190,6191,6192,6193,6194,6195,6196,6197,6198]
def ridgeSupport11_014 : List Nat := [6199,6200,6201,6202,6203,6204,6205,6206,6207,6208,6209,6210,6211,6212,6213,6214,6215,6216,6217,6218,6219,6220,6221,6222,6223,6224,6225,6226,6227,6228,6229,6230]
def ridgeSupport11_015 : List Nat := [6231,6232,6233,6234,6235]
def ridgeSupport11_code : Nat := 0x185bc2d61670b1857c2b61570a9853c2961470a184fc27613709984bc256127091847c236117089843c21610708183fc1f60f707983bc1d60e7071837c1b60d7069833c1960c706182fc1760b705982bc1560a7051827c136097049823c11608704181fc0f607703981bc0d6067031817c0b60570295c7ae35716b895c3ae15706b815bfadf56f6b795bbadd56e6b715b7adb56d6b695b3ad956c6b61477a3b51d68e9473a3951c68e146fa3751b68d946ba3551a68d1467a3351968c9463a3151868c0c5b62d31658b0c5762b31558a8c5362931458a0c4f6273135898c4b6253125890c476233115888c436213105880c3f61f30f5878c3b61d30e5870c3761b30d5868c3361930c5860c2f61730b5858c2b61530a5850c276133095848c236113085840c1f60f3075838c1b60d3065830c1760b3055828c136093045820c0f6073035818c0b6053025810c076033015808c036013005800bff5ff2ff57f8bfb5fd2fe57f0bf75fb2fd57e8bf35f92fc57e0bef5f72fb57d8beb5f52fa57d0be75f32f957c8be35f12f857c0bdf5ef2f757b8bdb5ed2f657b0bd75eb2f557a8bd35e92f457a0bcf5e72f35798bcb5e52f25790bc75e32f15788bc35e12f05780bbf5df2ef5778bbb5dd2ee5770bb75db2ed5768bb35d92ec5760baf5d72eb5758bab5d52ea5750ba75d32e95748ba35d12e85740b9f5cf2e75738b9b5cd2e65730b975cb2e55728b935c92e45720b8f5c72e35718b8b5c52e25710b875c32e15708b835c12e05700b7f5bf2df56f8b7b5bd2de56f0b775bb2dd56e8b735b92dc56e0b6f5b72db56d8b6b5b52da56d0b675b32d956c8b635b12d856c0b5f5af2d756b8b5b5ad2d656b0b575ab2d556a8b535a92d456a0b4f5a72d35698b4b5a52d25690b475a32d15688b435a12d05680b3f59f2cf56780f507a03cc1e40f107803bc1dc0ed07603ac1d40e9074039c1cc0e5072038c1c40e1070037c1bc0dd06e036c1b40d906c035c1ac0d506a034c1a40d1068033c19c0cd066032c1940c9064031c18c0c5062030c1840c106002fc17c0bd05e02ec1740b905c02dc16c0b505a02cc1640b105802bc15c008003801800a000
def ridgeSupport11_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport11_code
def ridgeSupport11_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport11_code
def ridgeSupport11_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport11_code
def ridgeSupport11_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport11_code
def ridgeSupport11_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport11_code
def ridgeSupport11_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport11_code
def ridgeSupport11_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport11_code
def ridgeSupport11_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport11_code
def ridgeSupport11_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport11_code
def ridgeSupport11_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport11_code
def ridgeSupport11_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport11_code
def ridgeSupport11_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport11_code
def ridgeSupport11_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport11_code
def ridgeSupport11_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport11_code
def ridgeSupport11_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport11_code
def ridgeSupport11_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport11_code
def ridgeSupport11_rest_016 : Nat := PackedRawNatGrowth.drop 6305 ridgeSupport11_code
def ridgeSupport11_suffix_016 : List Nat := []
def ridgeSupport11_suffix_015 : List Nat := ridgeSupport11_015 ++ ridgeSupport11_suffix_016
def ridgeSupport11_suffix_014 : List Nat := ridgeSupport11_014 ++ ridgeSupport11_suffix_015
def ridgeSupport11_suffix_013 : List Nat := ridgeSupport11_013 ++ ridgeSupport11_suffix_014
def ridgeSupport11_suffix_012 : List Nat := ridgeSupport11_012 ++ ridgeSupport11_suffix_013
def ridgeSupport11_suffix_011 : List Nat := ridgeSupport11_011 ++ ridgeSupport11_suffix_012
def ridgeSupport11_suffix_010 : List Nat := ridgeSupport11_010 ++ ridgeSupport11_suffix_011
def ridgeSupport11_suffix_009 : List Nat := ridgeSupport11_009 ++ ridgeSupport11_suffix_010
def ridgeSupport11_suffix_008 : List Nat := ridgeSupport11_008 ++ ridgeSupport11_suffix_009
def ridgeSupport11_suffix_007 : List Nat := ridgeSupport11_007 ++ ridgeSupport11_suffix_008
def ridgeSupport11_suffix_006 : List Nat := ridgeSupport11_006 ++ ridgeSupport11_suffix_007
def ridgeSupport11_suffix_005 : List Nat := ridgeSupport11_005 ++ ridgeSupport11_suffix_006
def ridgeSupport11_suffix_004 : List Nat := ridgeSupport11_004 ++ ridgeSupport11_suffix_005
def ridgeSupport11_suffix_003 : List Nat := ridgeSupport11_003 ++ ridgeSupport11_suffix_004
def ridgeSupport11_suffix_002 : List Nat := ridgeSupport11_002 ++ ridgeSupport11_suffix_003
def ridgeSupport11_suffix_001 : List Nat := ridgeSupport11_001 ++ ridgeSupport11_suffix_002
def ridgeSupport11_suffix_000 : List Nat := ridgeSupport11_000 ++ ridgeSupport11_suffix_001
theorem ridgeSupport11_source : candidateSupports 11 =
    (PackedRawNatGrowth.readList 13 485 ridgeSupport11_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
