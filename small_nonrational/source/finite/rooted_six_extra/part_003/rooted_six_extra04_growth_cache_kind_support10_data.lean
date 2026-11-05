module
prelude
public import RootedSixExtra04GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport10_000 : List Nat := [2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519]
def kindSupport10_001 : List Nat := [2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549,2550,2551]
def kindSupport10_002 : List Nat := [2552,2553,2554,2555,2556,2557,2558,2559,2560,2561,2562,2563,2564,2565,2566,2567,2568,2569,2570,2571,2572,2573,2574,2575,2576,2577,2578,2579,2580,2581,2582,2583]
def kindSupport10_003 : List Nat := [2584,2585,2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596,2597,2598,2599,2600,2601,2602,2603,2604,2605,2606,2607,2608,2609,2610,2611,2612,2613,2614,2615]
def kindSupport10_004 : List Nat := [2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646,2647]
def kindSupport10_005 : List Nat := [2648,2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674,2675,2676,2677,2678,2679]
def kindSupport10_006 : List Nat := [2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711]
def kindSupport10_007 : List Nat := [2712,2713,2714,2715,2716,2717,2718,2719,2720,2721,2722,2723,2724,2725,2726,2727,2728,2729,2730,2731,2732,2733,2734,2735,2736,2737,2738,2739,2740,2741,2742,2743]
def kindSupport10_008 : List Nat := [2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757,2758,2759,2760,2761,2762,2763,2764,2765,2766,2767,2768,2769,2770,2771,2772,2773,2774,2775]
def kindSupport10_009 : List Nat := [2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791,2792,2793,2794,2795,2796,2797,2798,2799,2800,2801,2802,2803,2804,2805,2806,2807]
def kindSupport10_010 : List Nat := [2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2818,2819,2820,2821,2822,2823,2824,2825,2826,2827,2828,2829,2830,2831,2832,2833,2834,2835,2836,2837,2838,2839]
def kindSupport10_011 : List Nat := [2840,2841,2842,2843,2844,2845,2846,2847,2848,2849,2850,2851,2852,2853,2854,2855,2856,2857,2858,2859,2860,2861,2862,2863,2864,2865,2866,2867,2868,2869,2870,2871]
def kindSupport10_012 : List Nat := [2872,2873,2874,2875,2876,2877,2878,2879,2880,2881,2882,2883,2884,2885,2886,2887,2888,2889,2890,2891,2892,2893,2894,2895,2896,2897,2898,2899,2900,2901,2902,2903]
def kindSupport10_013 : List Nat := [2904,2905,2906,2907,2908,2909,2910,2911,2912,2913,2914,2915,2916,2917,2918,2919,2920,2921,2922,2923,2924,2925,2926,2927,2928,2929,2930,2931,2932,2933,2934,2935]
def kindSupport10_014 : List Nat := [2936,2937,2938,2939,2940,2941,2942,2943,2944,2945,2946,2947,2948,2949,2950,2951,2952,2953,2954,2955,2956,2957,2958,2959,2960,2961,2962,2963,2964,2965,2966,2967]
def kindSupport10_015 : List Nat := [2968,2969,2970,2971,2972,2973,2974,2975,2976,2977,2978,2979,2980,2981,2982,2983,2984,2985,2986,2987,2988,2989,2990,2991,2992,2993,2994,2995,2996,2997,2998,2999]
def kindSupport10_016 : List Nat := [3000,3001,3002,3003,3004,3005,3006,3007,3008,3009,3010,3011,3012,3013,3014,3015,3016,3017,3018,3019,3020,3021,3022,3023,3024,3025,3026,3027,3028,3029,3030,3031]
def kindSupport10_017 : List Nat := [3032,3033,3034,3035,3036,3037,3038,3039,3040,3041,3042,3043,3044,3045,3046,3047,3048,3049,3050,3051,3052,3053,3054,3055,3056,3057,3058,3059,3060,3061,3062,3063]
def kindSupport10_018 : List Nat := [3064,3065,3066,3067,3068,3069,3070,3071,3072,3073,3074,3075,3076,3077,3078,3079,3080,3081,3082,3083,3084,3085,3086,3087,3088,3089,3090,3091,3092,3093,3094,3095]
def kindSupport10_019 : List Nat := [3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106,3107,3108,3109,3110,3111,3112,3113,3114,3115,3116,3117,3118,3119,3120,3121,3122,3123,3124,3125,3126,3127]
def kindSupport10_020 : List Nat := [3128,3129,3130,3131,3132,3133,3134,3135,3136,3137,3138,3139,3140,3141,3142,3143,3144,3145,3146,3147,3148,3149,3150,3151,3152,3153,3154,3155,3156,3157,3158,3159]
def kindSupport10_021 : List Nat := [3160,3161,3162,3163,3164,3165,3166,3167,3168,3169,3170,3171,3172,3173,3174,3175,3176,3177,3178,3179,3180,3181,3182,3183,3184,3185,3186,3187,3188,3189,3190,3191]
def kindSupport10_022 : List Nat := [3192,3193,3194,3195,3196,3197,3198,3199,3200,3201,3202,3203,3204,3205,3206,3207,3208,3209,3210,3211,3212,3213,3214,3215,3216,3217,3218,3219,3220,3221,3222,3223]
def kindSupport10_023 : List Nat := [3224,3225,3226,3227,3228,3229,3230,3231,3232,3233,3234,3235,3236,3237,3238,3239,3240,3241,3242,3243,3244,3245,3246,3247,3248,3249,3250,3251,3252,3253,3254,3255]
def kindSupport10_024 : List Nat := [3256,3257,3258,3259,3260,3261,3262,3263,3264,3265,3266,3267,3268,3269,3270,3271,3272,3273,3274,3275,3276,3277,3278,3279,3280,3281,3282,3283,3284,3285,3286,3287]
def kindSupport10_025 : List Nat := [3288,3289,3290,3291,3292,3293,3294,3295,3296,3297,3298,3299,3300,3301,3302,3303,3304,3305,3306,3307,3308,3309,3310,3311,3312,3313,3314,3315,3316,3317,3318,3319]
def kindSupport10_026 : List Nat := [3320,3321,3322,3323,3324,3325,3326,3327,3328,3329,3330,3331,3332,3333,3334,3335,3336,3337,3338,3339,3340,3341,3342,3343,3344,3345,3346,3347,3348,3349,3350,3351]
def kindSupport10_027 : List Nat := [3352,3353,3354,3355,3356,3357,3358,3359,3360,3361,3362,3363,3364,3365,3366,3367,3368,3369,3370,3371,3372,3373,3374,3375,3376,3377,3378,3379,3380,3381,3382,3383]
def kindSupport10_028 : List Nat := [3384,3385,3386,3387,3388,3389,3390,3391,3392,3393,3394,3395,3396,3397,3398,3399,3400,3401,3402,3403,3404,3405,3406,3407,3408,3409,3410,3411,3412,3413,3414,3415]
def kindSupport10_029 : List Nat := [3416,3417,3418,3419,3420,3421,3422,3423,3424,3425,3426,3427,3428,3429,3430,3431,3432,3433,3434,3435,3436,3437,3438,3439,3440,3441,3442,3443,3444,3445,3446,3447]
def kindSupport10_030 : List Nat := [3448,3449,3450,3451,3452,3453,3454,3455,3456,3457,3458,3459,3460,3461,3462,3463,3464,3465,3466,3467,3468,3469,3470,3471,3472,3473,3474,3475,3476,3477,3478,3479]
def kindSupport10_031 : List Nat := [3480,3481,3482,3483,3484,3485,3486,3487,3488,3489,3490,3491,3492,3493,3494,3495,3496,3497,3498,3499,3500,3501,3502,3503,3504,3505,3506,3507,3508,3509,3510,3511]
def kindSupport10_032 : List Nat := [3512,3513,3514,3515,3516,3517,3518,3519,3520,3521,3522,3523,3524,3525,3526,3527,3528,3529,3530,3531,3532,3533,3534,3535,3536,3537,3538,3539,3540,3541,3542,3543]
def kindSupport10_033 : List Nat := [3544,3545,3546,3547,3548,3549,3550,3551,3552,3553,3554,3555,3556,3557,3558,3559,3560,3561,3562,3563,3564,3565,3566,3567,3568,3569,3570,3571,3572,3573,3574,3575]
def kindSupport10_034 : List Nat := [3576,3577,3578,3579,3580,3581,3582,3583,3584,3585,3586,3587,3588,3589,3590,3591,3592,3593,3594,3595,3596,3597,3598,3599,3600,3601,3602,3603,3604,3605,3606,3607]
def kindSupport10_035 : List Nat := [3608,3609,3610,3611,3612,3613,3614,3615,3616,3617,3618,3619,3620,3621,3622,3623,3624,3625,3626,3627,3628,3629,3630,3631,3632,3633,3634,3635,3636,3637,3638,3639]
def kindSupport10_code : Nat := 0xe37e36e35e34e33e32e31e30e2fe2ee2de2ce2be2ae29e28e27e26e25e24e23e22e21e20e1fe1ee1de1ce1be1ae19e18e17e16e15e14e13e12e11e10e0fe0ee0de0ce0be0ae09e08e07e06e05e04e03e02e01e00dffdfedfddfcdfbdfadf9df8df7df6df5df4df3df2df1df0defdeededdecdebdeade9de8de7de6de5de4de3de2de1de0ddfddedddddcddbddadd9dd8dd7dd6dd5dd4dd3dd2dd1dd0dcfdcedcddccdcbdcadc9dc8dc7dc6dc5dc4dc3dc2dc1dc0dbfdbedbddbcdbbdbadb9db8db7db6db5db4db3db2db1db0dafdaedaddacdabdaada9da8da7da6da5da4da3da2da1da0d9fd9ed9dd9cd9bd9ad99d98d97d96d95d94d93d92d91d90d8fd8ed8dd8cd8bd8ad89d88d87d86d85d84d83d82d81d80d7fd7ed7dd7cd7bd7ad79d78d77d76d75d74d73d72d71d70d6fd6ed6dd6cd6bd6ad69d68d67d66d65d64d63d62d61d60d5fd5ed5dd5cd5bd5ad59d58d57d56d55d54d53d52d51d50d4fd4ed4dd4cd4bd4ad49d48d47d46d45d44d43d42d41d40d3fd3ed3dd3cd3bd3ad39d38d37d36d35d34d33d32d31d30d2fd2ed2dd2cd2bd2ad29d28d27d26d25d24d23d22d21d20d1fd1ed1dd1cd1bd1ad19d18d17d16d15d14d13d12d11d10d0fd0ed0dd0cd0bd0ad09d08d07d06d05d04d03d02d01d00cffcfecfdcfccfbcfacf9cf8cf7cf6cf5cf4cf3cf2cf1cf0cefceecedceccebceace9ce8ce7ce6ce5ce4ce3ce2ce1ce0cdfcdecddcdccdbcdacd9cd8cd7cd6cd5cd4cd3cd2cd1cd0ccfcceccdcccccbccacc9cc8cc7cc6cc5cc4cc3cc2cc1cc0cbfcbecbdcbccbbcbacb9cb8cb7cb6cb5cb4cb3cb2cb1cb0cafcaecadcaccabcaaca9ca8ca7ca6ca5ca4ca3ca2ca1ca0c9fc9ec9dc9cc9bc9ac99c98c97c96c95c94c93c92c91c90c8fc8ec8dc8cc8bc8ac89c88c87c86c85c84c83c82c81c80c7fc7ec7dc7cc7bc7ac79c78c77c76c75c74c73c72c71c70c6fc6ec6dc6cc6bc6ac69c68c67c66c65c64c63c62c61c60c5fc5ec5dc5cc5bc5ac59c58c57c56c55c54c53c52c51c50c4fc4ec4dc4cc4bc4ac49c48c47c46c45c44c43c42c41c40c3fc3ec3dc3cc3bc3ac39c38c37c36c35c34c33c32c31c30c2fc2ec2dc2cc2bc2ac29c28c27c26c25c24c23c22c21c20c1fc1ec1dc1cc1bc1ac19c18c17c16c15c14c13c12c11c10c0fc0ec0dc0cc0bc0ac09c08c07c06c05c04c03c02c01c00bffbfebfdbfcbfbbfabf9bf8bf7bf6bf5bf4bf3bf2bf1bf0befbeebedbecbebbeabe9be8be7be6be5be4be3be2be1be0bdfbdebddbdcbdbbdabd9bd8bd7bd6bd5bd4bd3bd2bd1bd0bcfbcebcdbccbcbbcabc9bc8bc7bc6bc5bc4bc3bc2bc1bc0bbfbbebbdbbcbbbbbabb9bb8bb7bb6bb5bb4bb3bb2bb1bb0bafbaebadbacbabbaaba9ba8ba7ba6ba5ba4ba3ba2ba1ba0b9fb9eb9db9cb9bb9ab99b98b97b96b95b94b93b92b91b90b8fb8eb8db8cb8bb8ab89b88b87b86b85b84b83b82b81b80b7fb7eb7db7cb7bb7ab79b78b77b76b75b74b73b72b71b70b6fb6eb6db6cb6bb6ab69b68b67b66b65b64b63b62b61b60b5fb5eb5db5cb5bb5ab59b58b57b56b55b54b53b52b51b50b4fb4eb4db4cb4bb4ab49b48b47b46b45b44b43b42b41b40b3fb3eb3db3cb3bb3ab39b38b37b36b35b34b33b32b31b30b2fb2eb2db2cb2bb2ab29b28b27b26b25b24b23b22b21b20b1fb1eb1db1cb1bb1ab19b18b17b16b15b14b13b12b11b10b0fb0eb0db0cb0bb0ab09b08b07b06b05b04b03b02b01b00affafeafdafcafbafaaf9af8af7af6af5af4af3af2af1af0aefaeeaedaecaebaeaae9ae8ae7ae6ae5ae4ae3ae2ae1ae0adfadeaddadcadbadaad9ad8ad7ad6ad5ad4ad3ad2ad1ad0acfaceacdaccacbacaac9ac8ac7ac6ac5ac4ac3ac2ac1ac0abfabeabdabcabbabaab9ab8ab7ab6ab5ab4ab3ab2ab1ab0aafaaeaadaacaabaaaaa9aa8aa7aa6aa5aa4aa3aa2aa1aa0a9fa9ea9da9ca9ba9aa99a98a97a96a95a94a93a92a91a90a8fa8ea8da8ca8ba8aa89a88a87a86a85a84a83a82a81a80a7fa7ea7da7ca7ba7aa79a78a77a76a75a74a73a72a71a70a6fa6ea6da6ca6ba6aa69a68a67a66a65a64a63a62a61a60a5fa5ea5da5ca5ba5aa59a58a57a56a55a54a53a52a51a50a4fa4ea4da4ca4ba4aa49a48a47a46a45a44a43a42a41a40a3fa3ea3da3ca3ba3aa39a38a37a36a35a34a33a32a31a30a2fa2ea2da2ca2ba2aa29a28a27a26a25a24a23a22a21a20a1fa1ea1da1ca1ba1aa19a18a17a16a15a14a13a12a11a10a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a009ff9fe9fd9fc9fb9fa9f99f89f79f69f59f49f39f29f19f09ef9ee9ed9ec9eb9ea9e99e89e79e69e59e49e39e29e19e09df9de9dd9dc9db9da9d99d89d79d69d59d49d39d29d19d09cf9ce9cd9cc9cb9ca9c99c89c79c69c59c49c39c29c19c09bf9be9bd9bc9bb9ba9b99b8
def kindSupport10_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport10_code
def kindSupport10_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport10_code
def kindSupport10_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport10_code
def kindSupport10_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport10_code
def kindSupport10_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport10_code
def kindSupport10_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport10_code
def kindSupport10_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport10_code
def kindSupport10_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport10_code
def kindSupport10_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport10_code
def kindSupport10_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport10_code
def kindSupport10_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport10_code
def kindSupport10_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport10_code
def kindSupport10_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport10_code
def kindSupport10_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport10_code
def kindSupport10_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport10_code
def kindSupport10_rest_015 : Nat := PackedRawNatGrowth.drop 5760 kindSupport10_code
def kindSupport10_rest_016 : Nat := PackedRawNatGrowth.drop 6144 kindSupport10_code
def kindSupport10_rest_017 : Nat := PackedRawNatGrowth.drop 6528 kindSupport10_code
def kindSupport10_rest_018 : Nat := PackedRawNatGrowth.drop 6912 kindSupport10_code
def kindSupport10_rest_019 : Nat := PackedRawNatGrowth.drop 7296 kindSupport10_code
def kindSupport10_rest_020 : Nat := PackedRawNatGrowth.drop 7680 kindSupport10_code
def kindSupport10_rest_021 : Nat := PackedRawNatGrowth.drop 8064 kindSupport10_code
def kindSupport10_rest_022 : Nat := PackedRawNatGrowth.drop 8448 kindSupport10_code
def kindSupport10_rest_023 : Nat := PackedRawNatGrowth.drop 8832 kindSupport10_code
def kindSupport10_rest_024 : Nat := PackedRawNatGrowth.drop 9216 kindSupport10_code
def kindSupport10_rest_025 : Nat := PackedRawNatGrowth.drop 9600 kindSupport10_code
def kindSupport10_rest_026 : Nat := PackedRawNatGrowth.drop 9984 kindSupport10_code
def kindSupport10_rest_027 : Nat := PackedRawNatGrowth.drop 10368 kindSupport10_code
def kindSupport10_rest_028 : Nat := PackedRawNatGrowth.drop 10752 kindSupport10_code
def kindSupport10_rest_029 : Nat := PackedRawNatGrowth.drop 11136 kindSupport10_code
def kindSupport10_rest_030 : Nat := PackedRawNatGrowth.drop 11520 kindSupport10_code
def kindSupport10_rest_031 : Nat := PackedRawNatGrowth.drop 11904 kindSupport10_code
def kindSupport10_rest_032 : Nat := PackedRawNatGrowth.drop 12288 kindSupport10_code
def kindSupport10_rest_033 : Nat := PackedRawNatGrowth.drop 12672 kindSupport10_code
def kindSupport10_rest_034 : Nat := PackedRawNatGrowth.drop 13056 kindSupport10_code
def kindSupport10_rest_035 : Nat := PackedRawNatGrowth.drop 13440 kindSupport10_code
def kindSupport10_rest_036 : Nat := PackedRawNatGrowth.drop 13824 kindSupport10_code
def kindSupport10_suffix_036 : List Nat := []
def kindSupport10_suffix_035 : List Nat := kindSupport10_035 ++ kindSupport10_suffix_036
def kindSupport10_suffix_034 : List Nat := kindSupport10_034 ++ kindSupport10_suffix_035
def kindSupport10_suffix_033 : List Nat := kindSupport10_033 ++ kindSupport10_suffix_034
def kindSupport10_suffix_032 : List Nat := kindSupport10_032 ++ kindSupport10_suffix_033
def kindSupport10_suffix_031 : List Nat := kindSupport10_031 ++ kindSupport10_suffix_032
def kindSupport10_suffix_030 : List Nat := kindSupport10_030 ++ kindSupport10_suffix_031
def kindSupport10_suffix_029 : List Nat := kindSupport10_029 ++ kindSupport10_suffix_030
def kindSupport10_suffix_028 : List Nat := kindSupport10_028 ++ kindSupport10_suffix_029
def kindSupport10_suffix_027 : List Nat := kindSupport10_027 ++ kindSupport10_suffix_028
def kindSupport10_suffix_026 : List Nat := kindSupport10_026 ++ kindSupport10_suffix_027
def kindSupport10_suffix_025 : List Nat := kindSupport10_025 ++ kindSupport10_suffix_026
def kindSupport10_suffix_024 : List Nat := kindSupport10_024 ++ kindSupport10_suffix_025
def kindSupport10_suffix_023 : List Nat := kindSupport10_023 ++ kindSupport10_suffix_024
def kindSupport10_suffix_022 : List Nat := kindSupport10_022 ++ kindSupport10_suffix_023
def kindSupport10_suffix_021 : List Nat := kindSupport10_021 ++ kindSupport10_suffix_022
def kindSupport10_suffix_020 : List Nat := kindSupport10_020 ++ kindSupport10_suffix_021
def kindSupport10_suffix_019 : List Nat := kindSupport10_019 ++ kindSupport10_suffix_020
def kindSupport10_suffix_018 : List Nat := kindSupport10_018 ++ kindSupport10_suffix_019
def kindSupport10_suffix_017 : List Nat := kindSupport10_017 ++ kindSupport10_suffix_018
def kindSupport10_suffix_016 : List Nat := kindSupport10_016 ++ kindSupport10_suffix_017
def kindSupport10_suffix_015 : List Nat := kindSupport10_015 ++ kindSupport10_suffix_016
def kindSupport10_suffix_014 : List Nat := kindSupport10_014 ++ kindSupport10_suffix_015
def kindSupport10_suffix_013 : List Nat := kindSupport10_013 ++ kindSupport10_suffix_014
def kindSupport10_suffix_012 : List Nat := kindSupport10_012 ++ kindSupport10_suffix_013
def kindSupport10_suffix_011 : List Nat := kindSupport10_011 ++ kindSupport10_suffix_012
def kindSupport10_suffix_010 : List Nat := kindSupport10_010 ++ kindSupport10_suffix_011
def kindSupport10_suffix_009 : List Nat := kindSupport10_009 ++ kindSupport10_suffix_010
def kindSupport10_suffix_008 : List Nat := kindSupport10_008 ++ kindSupport10_suffix_009
def kindSupport10_suffix_007 : List Nat := kindSupport10_007 ++ kindSupport10_suffix_008
def kindSupport10_suffix_006 : List Nat := kindSupport10_006 ++ kindSupport10_suffix_007
def kindSupport10_suffix_005 : List Nat := kindSupport10_005 ++ kindSupport10_suffix_006
def kindSupport10_suffix_004 : List Nat := kindSupport10_004 ++ kindSupport10_suffix_005
def kindSupport10_suffix_003 : List Nat := kindSupport10_003 ++ kindSupport10_suffix_004
def kindSupport10_suffix_002 : List Nat := kindSupport10_002 ++ kindSupport10_suffix_003
def kindSupport10_suffix_001 : List Nat := kindSupport10_001 ++ kindSupport10_suffix_002
def kindSupport10_suffix_000 : List Nat := kindSupport10_000 ++ kindSupport10_suffix_001
theorem kindSupport10_source : kindSupports 10 =
    (PackedRawNatGrowth.readList 12 1152 kindSupport10_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
