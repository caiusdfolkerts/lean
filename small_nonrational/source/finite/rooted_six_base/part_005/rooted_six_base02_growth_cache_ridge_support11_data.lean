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
def ridgeSupport11_011 : List Nat := [3151,3152,3153,3154,3155,3156,3157,3158,3159,3160,3161,3162,3163,6008,6009,6010,6011,6012,6013,6014,6015,6016,6017,6018,6019,6020,6021,6022,6023,6024,6025,6026]
def ridgeSupport11_012 : List Nat := [6027,6028,6029,6030,6031,6032,6033,6034,6035,6036,6037,6038,6039,6040,6041,6042,6043,6044,6045,6046,6047,6048,6049,6050,6051,6052,6053,6054,6055,6056,6057,6058]
def ridgeSupport11_013 : List Nat := [6059,6060,6061,6062,6063,6064,6065,6066,6067,6068,6069,6070,6071,6072,6073,6074,6075,6076,6077,6078,6079,6080,6081,6082,6083,6084,6085,6086,6087,6088,6089,6090]
def ridgeSupport11_014 : List Nat := [6091,6092,6093,6094,6095,6096,6097,6098,6099,6100,6101,6102,6103,6104,6105,6106,6107,6108,6109,6110,6111,6112,6113,6114,6115,6116,6117,6118,6119,6120,6121,6122]
def ridgeSupport11_015 : List Nat := [6123,6124,6125,6126,6127,6128,6129,6130,6131,6132,6133,6134,6135,6136,6137,6138,6139,6140,6141,6142,6143,6144,6145,6146,6147,6148,6149,6150,6151,6152,6153,6154]
def ridgeSupport11_016 : List Nat := [6155,6156,6157,6158,6159,6160,6161,6162,6163,6164,6165,6166,6167,6168,6169,6170,6171,6172,6173,6174,6175,6176,6177,6178,6179,6180,6181,6182,6183,6184,6185,6186]
def ridgeSupport11_017 : List Nat := [6187,6188,6189,6190,6191,6192,6193,6194,6195,6196,6197,6198,6199,6200,6201,6202,6203,6204,6205,6206,6207,6208,6209,6210,6211,6212,6213,6214,6215,6216,6217,6218]
def ridgeSupport11_018 : List Nat := [6219,6220,6221,6222,6223,7448,7449,7450,7451,7452,7453,7454,7455,7456,7457,7458,7459,7460,7461,7462,7463,7464,7465,7466,7467,7468,7469,7470,7471,7784,7785,7786]
def ridgeSupport11_019 : List Nat := [7787,7788,7789,7790,7791,7792,7793,7794,7795,7796,7797,7798,7799,7800,7801,7802,7803,7804,7805,7806,7807]
def ridgeSupport11_code : Nat := 0x1e7ff3f79f7cf9e7bf3d79e7cf1e77f3b79d7ce9e73f3979c7ce1e6ff3779b7cd9e6bf3579a7cd1d2fe9774b7a59d2be9574a7a51d27e937497a49d23e917487a41d1fe8f7477a39d1be8d7467a3184fc27613709984bc256127091847c236117089843c21610708183fc1f60f707983bc1d60e7071837c1b60d7069833c1960c706182fc1760b705982bc1560a7051827c136097049823c11608704181fc0f607703981bc0d6067031817c0b6057029813c09604702180fc07603701980bc056027011807c036017009803c0160070017ffbff5ff6ff97fbbfd5fe6ff17f7bfb5fd6fe97f3bf95fc6fe17efbf75fb6fd97ebbf55fa6fd17e7bf35f96fc97e3bf15f86fc17dfbef5f76fb97dbbed5f66fb17d7beb5f56fa97d3be95f46fa17cfbe75f36f997cbbe55f26f917c7be35f16f897c3be15f06f817bfbdf5ef6f797bbbdd5ee6f717b7bdb5ed6f697b3bd95ec6f617afbd75eb6f597abbd55ea6f517a7bd35e96f497a3bd15e86f4179fbcf5e76f3979bbcd5e66f31797bcb5e56f29793bc95e46f2178fbc75e36f1978bbc55e26f11787bc35e16f09783bc15e06f0177fbbf5df6ef977bbbd5de6ef0c5b62d31658b0c5762b31558a8c5362931458a0c4f6273135898c4b6253125890c476233115888c436213105880c3f61f30f5878c3b61d30e5870c3761b30d5868c3361930c5860c2f61730b5858c2b61530a5850c276133095848c236113085840c1f60f3075838c1b60d3065830c1760b3055828c136093045820c0f6073035818c0b6053025810c076033015808c036013005800bff5ff2ff57f8bfb5fd2fe57f0bf75fb2fd57e8bf35f92fc57e0bef5f72fb57d8beb5f52fa57d0be75f32f957c8be35f12f857c0bdf5ef2f757b8bdb5ed2f657b0bd75eb2f557a8bd35e92f457a0bcf5e72f35798bcb5e52f25790bc75e32f15788bc35e12f05780bbf5df2ef5778bbb5dd2ee5770bb75db2ed5768bb35d92ec5760baf5d72eb5758bab5d52ea5750ba75d32e95748ba35d12e85740b9f5cf2e75738b9b5cd2e65730b975cb2e55728b935c92e45720b8f5c72e35718b8b5c52e25710b875c32e15708b835c12e05700b7f5bf2df56f8b7b5bd2de56f0b775bb2dd56e8b735b92dc56e0b6f5b72db56d8b6b5b52da56d0b675b32d956c8b635b12d856c0b5f5af2d756b8b5b5ad2d656b0b575ab2d556a8b535a92d456a0b4f5a72d35698b4b5a52d25690b475a32d15688b435a12d05680b3f59f2cf56780f507a03cc1e40f107803bc1dc0ed07603ac1d40e9074039c1cc0e5072038c1c40e1070037c1bc0dd06e036c1b40d906c035c1ac0d506a034c1a40d1068033c19c0cd066032c1940c9064031c18c0c5062030c1840c106002fc17c0bd05e02ec1740b905c02dc16c0b505a02cc1640b105802bc15c008003801800a000
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
def ridgeSupport11_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport11_code
def ridgeSupport11_rest_017 : Nat := PackedRawNatGrowth.drop 7072 ridgeSupport11_code
def ridgeSupport11_rest_018 : Nat := PackedRawNatGrowth.drop 7488 ridgeSupport11_code
def ridgeSupport11_rest_019 : Nat := PackedRawNatGrowth.drop 7904 ridgeSupport11_code
def ridgeSupport11_rest_020 : Nat := PackedRawNatGrowth.drop 8177 ridgeSupport11_code
def ridgeSupport11_suffix_020 : List Nat := []
def ridgeSupport11_suffix_019 : List Nat := ridgeSupport11_019 ++ ridgeSupport11_suffix_020
def ridgeSupport11_suffix_018 : List Nat := ridgeSupport11_018 ++ ridgeSupport11_suffix_019
def ridgeSupport11_suffix_017 : List Nat := ridgeSupport11_017 ++ ridgeSupport11_suffix_018
def ridgeSupport11_suffix_016 : List Nat := ridgeSupport11_016 ++ ridgeSupport11_suffix_017
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
    (PackedRawNatGrowth.readList 13 629 ridgeSupport11_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
