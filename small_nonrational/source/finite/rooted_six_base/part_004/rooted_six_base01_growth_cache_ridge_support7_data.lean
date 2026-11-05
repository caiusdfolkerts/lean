module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport7_000 : List Nat := [0,1,2,3,4,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142]
def ridgeSupport7_001 : List Nat := [143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174]
def ridgeSupport7_002 : List Nat := [175,176,177,178,179,180,181,182,183,184,185,186,187,2418,2419,2420,2421,2422,2423,2424,2425,2426,2427,2428,2429,2430,2431,2432,2433,2434,2435,2436]
def ridgeSupport7_003 : List Nat := [2437,2438,2439,2440,2441,2442,2443,2444,2445,2446,2447,2448,2449,2450,2451,2452,2453,2454,2455,2456,2457,2458,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468]
def ridgeSupport7_004 : List Nat := [2469,2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,2480,2481,2482,2483,2484,2485,2486,2487,2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500]
def ridgeSupport7_005 : List Nat := [2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532]
def ridgeSupport7_006 : List Nat := [2533,2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549,2550,2551,2552,2553,2554,2555,2556,2557,2558,2559,2560,2561,2562,2563,2564]
def ridgeSupport7_007 : List Nat := [2565,2566,2567,2568,2569,2570,2571,2572,2573,2574,2575,2576,2577,2578,2579,2580,2581,2582,2583,2584,2585,2586,2587,2588,2589,2590,2591,2592,2593,2594,2595,2596]
def ridgeSupport7_008 : List Nat := [2597,2598,2599,2600,2601,2602,2603,2604,2605,2606,2607,2608,2609,2610,2611,2612,2613,2614,2615,2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628]
def ridgeSupport7_009 : List Nat := [2629,2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646,2647,2648,2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660]
def ridgeSupport7_010 : List Nat := [2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674,2675,2676,2677,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2691,2692]
def ridgeSupport7_011 : List Nat := [2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712,2713,2714,2715,2716,2717,2718,2719,2720,2721,2722,2723,2724]
def ridgeSupport7_012 : List Nat := [2725,2726,2727,2728,2729,2730,2731,2732,2733,2734,2735,2736,2737,2738,2739,2740,2741,2742,2743,2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756]
def ridgeSupport7_013 : List Nat := [2757,2758,2759,2760,2761,2762,2763,2764,2765,2766,2767,2768,2769,2770,2771,2772,2773,2774,2775,2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788]
def ridgeSupport7_014 : List Nat := [2789,2790,2791,2792,2793,2794,2795,2796,2797,2798,2799,2800,2801,2802,2803,2804,2805,2806,2807,2808,2809,2810,2811,2812,2813,2814,2815,2816,2817,2818,2819,2820]
def ridgeSupport7_015 : List Nat := [2821,2822,2823,2824,2825,2826,2827,2828,2829,2830,2831,2832,2833,2834,2835,2836,2837,2838,2839,2840,2841,2842,2843,2844,2845,2846,2847,2848,2849,7890,7891,7892]
def ridgeSupport7_016 : List Nat := [7893,7894,7895,7896,7897,7898,7899,7900,7901,7902,7903,7904,7905,7906,7907,7908,7909,7910,7911,7912,7913,7914,7915,7916,7917,7918,7919,7920,7921,7922,7923,7924]
def ridgeSupport7_017 : List Nat := [7925,7926,7927,7928,7929,7930,7931,7932,7933,7934,7935,7936,7937,7938,7939,7940,7941,7942,7943,7944,7945,7946,7947,7948,7949,7950,7951,7952,7953,7954,7955,7956]
def ridgeSupport7_018 : List Nat := [7957,7958,7959,7960,7961,7962,7963,7964,7965,7966,7967,7968,7969,7970,7971,7972,7973,7974,7975,7976,7977,7978,7979,7980,7981,7982,7983,7984,7985,7986,7987,7988]
def ridgeSupport7_019 : List Nat := [7989,7990,7991,7992,7993,7994,7995,7996,7997,7998,7999,8000,8001,8002,8003,8004,8005,8006,8007,8008,8009,8010,8011,8012,8013,8014,8015,8016,8017,8018,8019,8020]
def ridgeSupport7_020 : List Nat := [8021,8022,8023,8024,8025,8026,8027,8028,8029,8030,8031,8032,8033,8034,8035,8036,8037,8038,8039,8040,8041,8042,8043,8044,8045,8046,8047,8048,8049,8050,8051,8052]
def ridgeSupport7_021 : List Nat := [8053,8054,8055,8056,8057,8058,8059,8060,8061,8062,8063,8064,8065,8066,8067,8068,8069,8070,8071,8072,8073,8074,8075,8076,8077,8078,8079,8080,8081,8082,8083,8084]
def ridgeSupport7_022 : List Nat := [8085,8086,8087,8088,8089,8090,8091,8092,8093,8094,8095,8096,8097,8098,8099,8100,8101,8102,8103,8104,8105,8106,8107,8108,8109,8110,8111,8112,8113,8114,8115,8116]
def ridgeSupport7_023 : List Nat := [8117,8118,8119,8120,8121,8122,8123,8124,8125,8126,8127,8128,8129,8130,8131,8132,8133,8134,8135,8136,8137,8138,8139,8140,8141,8142,8143,8144,8145,8146,8147,8148]
def ridgeSupport7_024 : List Nat := [8149,8150,8151,8152,8153,8154,8155,8156,8157,8158,8159,8160,8161,8162,8163,8164,8165,8166,8167,8168,8169,8170,8171,8172,8173,8174,8175,8176,8177,12030,12031,12032]
def ridgeSupport7_025 : List Nat := [12033,12034,12035,12036,12037,12038,12039,12040,12041,12042,12043,12044,12045,12046,12047,12048,12049,12050,12051,12052,12053,12054,12055,12056,12057,12058,12059,12060,12061,12062,12063,12064]
def ridgeSupport7_026 : List Nat := [12065,12066,12067,12068,12069,12070,12071,12072,12073,12074,12075,12076,12077,12078,12079,12080,12081,12082,12083,12084,12085,12086,12087,12088,12089,12090,12091,12092,12093,12094,12095,12096]
def ridgeSupport7_027 : List Nat := [12097,12098,12099,12100,12101,12102,12103,12104,12105,12106,12107,12108,12109,12110,12111,12112,12113,12114,12115,12116,12117,12118,12119,12120,12121,12122,12123,12124,12125,12126,12127,12128]
def ridgeSupport7_028 : List Nat := [12129,12130,12131,12132,12133,12134,12135,12136,12137,12138,12139,12140,12141,12142,12143,12144,12145,12146,12147,12148,12149,12150,12151,12152,12153,12154,12155,12156,12157,12158,12159,12160]
def ridgeSupport7_029 : List Nat := [12161,12162,12163,12164,12165,12166,12167,12168,12169,12170,12171,12172,12173,12174,12175,12176,12177,12178,12179,12180,12181,12182,12183,12184,12185,12186,12187,12188,12189,12190,12191,12192]
def ridgeSupport7_030 : List Nat := [12193,12194,12195,12196,12197,12198,12199,12200,12201,12202,12203,12204,12205,12206,12207,12208,12209,12210,12211,12212,12213,12214,12215,12216,12217,12218,12219,12220,12221,12222,12223,12224]
def ridgeSupport7_031 : List Nat := [12225,12226,12227,12228,12229,12230,12231,12232,12233,12234,12235,12236,12237,12238,12239,12240,12241,12242,12243,12244,12245,14442,14443,14444,14445,14446,14447,14448,14449,14450,14451,14452]
def ridgeSupport7_032 : List Nat := [14453,14454,14455,14456,14457,14458,14459,14460,14461,14462,14463,14464,14465,14790,14791,14792,14793,14794,14795,14796,14797,14798,14799,14800,14801,14802,14803,14804,14805,14806,14807,14808]
def ridgeSupport7_033 : List Nat := [14809,14810,14811,14812,14813]
def ridgeSupport7_code : Nat := 0x39dde7739dbe76b9d9e7639d7e75b9d5e7539d3e74b9d1e7439cfe73b9cde7339cbe72b9c9e7239c7e71b881e20387fe1fb87de1f387be1eb879e1e3877e1db875e1d3873e1cb871e1c386fe1bb86de1b386be1aafd5bf52fd3bf4afd1bf42fcfbf3afcdbf32fcbbf2afc9bf22fc7bf1afc5bf12fc3bf0afc1bf02fbfbefafbdbef2fbbbeeafb9bee2fb7bedafb5bed2fb3becafb1bec2fafbebafadbeb2fabbeaafa9bea2fa7be9afa5be92fa3be8afa1be82f9fbe7af9dbe72f9bbe6af99be62f97be5af95be52f93be4af91be42f8fbe3af8dbe32f8bbe2af89be22f87be1af85be12f83be0af81be02f7fbdfaf7dbdf2f7bbdeaf79bde2f77bddaf75bdd2f73bdcaf71bdc2f6fbdbaf6dbdb2f6bbdaaf69bda2f67bd9af65bd92f63bd8af61bd82f5fbd7af5dbd72f5bbd6af59bd62f57bd5af55bd52f53bd4af51bd42f4fbd3af4dbd32f4bbd2af49bd22f47bd1af45bd12f43bd0af41bd02f3fbcfaf3dbcf2f3bbceaf39bce2f37bcdaf35bcd2f33bccaf31bcc2f2fbcbaf2dbcb2f2bbcaaf29bca2f27bc9af25bc92f23bc8af21bc82f1fbc7af1dbc72f1bbc6af19bc62f17bc5af15bc52f13bc4af11bc42f0fbc3af0dbc32f0bbc2af09bc22f07bc1af05bc12f03bc0af01bc02effbbf9ff17fc1fef7fb9fed7fb1feb7fa9fe97fa1fe77f99fe57f91fe37f89fe17f81fdf7f79fdd7f71fdb7f69fd97f61fd77f59fd57f51fd37f49fd17f41fcf7f39fcd7f31fcb7f29fc97f21fc77f19fc57f11fc37f09fc17f01fbf7ef9fbd7ef1fbb7ee9fb97ee1fb77ed9fb57ed1fb37ec9fb17ec1faf7eb9fad7eb1fab7ea9fa97ea1fa77e99fa57e91fa37e89fa17e81f9f7e79f9d7e71f9b7e69f997e61f977e59f957e51f937e49f917e41f8f7e39f8d7e31f8b7e29f897e21f877e19f857e11f837e09f817e01f7f7df9f7d7df1f7b7de9f797de1f777dd9f757dd1f737dc9f717dc1f6f7db9f6d7db1f6b7da9f697da1f677d99f657d91f637d89f617d81f5f7d79f5d7d71f5b7d69f597d61f577d59f557d51f537d49f517d41f4f7d39f4d7d31f4b7d29f497d21f477d19f457d11f437d09f417d01f3f7cf9f3d7cf1f3b7ce9f397ce1f377cd9f357cd1f337cc9f317cc1f2f7cb9f2d7cb1f2b7ca9f297ca1f277c99f257c91f237c89f217c81f1f7c79f1d7c71f1b7c69f197c61f177c59f157c51f137c49f117c41f0f7c39f0d7c31f0b7c29f097c21f077c19f057c11f037c09f017c01eff7bf9efd7bf1efb7be9ef97be1ef77bd9ef57bd1ef37bc9ef17bc1eef7bb9eed7bb1eeb7ba9ee97ba1ee77b99ee57b91ee37b89ee17b81edf7b79edd7b71edb7b69ed97b61ed77b59ed57b51ed37b48b212c80b1f2c78b1d2c70b1b2c68b192c60b172c58b152c50b132c48b112c40b0f2c38b0d2c30b0b2c28b092c20b072c18b052c10b032c08b012c00aff2bf8afd2bf0afb2be8af92be0af72bd8af52bd0af32bc8af12bc0aef2bb8aed2bb0aeb2ba8ae92ba0ae72b98ae52b90ae32b88ae12b80adf2b78add2b70adb2b68ad92b60ad72b58ad52b50ad32b48ad12b40acf2b38acd2b30acb2b28ac92b20ac72b18ac52b10ac32b08ac12b00abf2af8abd2af0abb2ae8ab92ae0ab72ad8ab52ad0ab32ac8ab12ac0aaf2ab8aad2ab0aab2aa8aa92aa0aa72a98aa52a90aa32a88aa12a80a9f2a78a9d2a70a9b2a68a992a60a972a58a952a50a932a48a912a40a8f2a38a8d2a30a8b2a28a892a20a872a18a852a10a832a08a812a00a7f29f8a7d29f0a7b29e8a7929e0a7729d8a7529d0a7329c8a7129c0a6f29b8a6d29b0a6b29a8a6929a0a672998a652990a632988a612980a5f2978a5d2970a5b2968a592960a572958a552950a532948a512940a4f2938a4d2930a4b2928a492920a472918a452910a432908a412900a3f28f8a3d28f0a3b28e8a3928e0a3728d8a3528d0a3328c8a3128c0a2f28b8a2d28b0a2b28a8a2928a0a272898a252890a232888a212880a1f2878a1d2870a1b2868a192860a172858a152850a132848a112840a0f2838a0d2830a0b2828a092820a072818a052810a032808a0128009ff27f89fd27f09fb27e89f927e09f727d89f527d09f327c89f127c09ef27b89ed27b09eb27a89e927a09e727989e527909e327889e127809df27789dd27709db27689d927609d727589d527509d327489d127409cf27389cd27309cb27289c927209c727189c527109c327089c127009bf26f89bd26f09bb26e89b926e09b726d89b526d09b326c89b126c09af26b89ad26b09ab26a89a926a09a726989a526909a326889a1268099f267899d267099b26689992660997265899526509932648991264098f263898d263098b26289892620987261898526109832608981260097f25f897d25f097b25e897925e097725d897525d097325c80bb02e80b902e00b702d80b502d00b302c80b102c00af02b80ad02b00ab02a80a902a00a702980a502900a302880a1028009f027809d027009b02680990260097025809502500930248091024008f023808d023008b02280890220087021808502100830208081020007f01f807d01f007b01e807901e007701d807501d0004000c0020004000
def ridgeSupport7_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport7_code
def ridgeSupport7_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport7_code
def ridgeSupport7_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport7_code
def ridgeSupport7_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport7_code
def ridgeSupport7_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport7_code
def ridgeSupport7_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport7_code
def ridgeSupport7_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport7_code
def ridgeSupport7_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport7_code
def ridgeSupport7_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport7_code
def ridgeSupport7_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport7_code
def ridgeSupport7_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport7_code
def ridgeSupport7_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport7_code
def ridgeSupport7_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport7_code
def ridgeSupport7_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport7_code
def ridgeSupport7_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport7_code
def ridgeSupport7_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport7_code
def ridgeSupport7_rest_016 : Nat := PackedRawNatGrowth.drop 7168 ridgeSupport7_code
def ridgeSupport7_rest_017 : Nat := PackedRawNatGrowth.drop 7616 ridgeSupport7_code
def ridgeSupport7_rest_018 : Nat := PackedRawNatGrowth.drop 8064 ridgeSupport7_code
def ridgeSupport7_rest_019 : Nat := PackedRawNatGrowth.drop 8512 ridgeSupport7_code
def ridgeSupport7_rest_020 : Nat := PackedRawNatGrowth.drop 8960 ridgeSupport7_code
def ridgeSupport7_rest_021 : Nat := PackedRawNatGrowth.drop 9408 ridgeSupport7_code
def ridgeSupport7_rest_022 : Nat := PackedRawNatGrowth.drop 9856 ridgeSupport7_code
def ridgeSupport7_rest_023 : Nat := PackedRawNatGrowth.drop 10304 ridgeSupport7_code
def ridgeSupport7_rest_024 : Nat := PackedRawNatGrowth.drop 10752 ridgeSupport7_code
def ridgeSupport7_rest_025 : Nat := PackedRawNatGrowth.drop 11200 ridgeSupport7_code
def ridgeSupport7_rest_026 : Nat := PackedRawNatGrowth.drop 11648 ridgeSupport7_code
def ridgeSupport7_rest_027 : Nat := PackedRawNatGrowth.drop 12096 ridgeSupport7_code
def ridgeSupport7_rest_028 : Nat := PackedRawNatGrowth.drop 12544 ridgeSupport7_code
def ridgeSupport7_rest_029 : Nat := PackedRawNatGrowth.drop 12992 ridgeSupport7_code
def ridgeSupport7_rest_030 : Nat := PackedRawNatGrowth.drop 13440 ridgeSupport7_code
def ridgeSupport7_rest_031 : Nat := PackedRawNatGrowth.drop 13888 ridgeSupport7_code
def ridgeSupport7_rest_032 : Nat := PackedRawNatGrowth.drop 14336 ridgeSupport7_code
def ridgeSupport7_rest_033 : Nat := PackedRawNatGrowth.drop 14784 ridgeSupport7_code
def ridgeSupport7_rest_034 : Nat := PackedRawNatGrowth.drop 14854 ridgeSupport7_code
def ridgeSupport7_suffix_034 : List Nat := []
def ridgeSupport7_suffix_033 : List Nat := ridgeSupport7_033 ++ ridgeSupport7_suffix_034
def ridgeSupport7_suffix_032 : List Nat := ridgeSupport7_032 ++ ridgeSupport7_suffix_033
def ridgeSupport7_suffix_031 : List Nat := ridgeSupport7_031 ++ ridgeSupport7_suffix_032
def ridgeSupport7_suffix_030 : List Nat := ridgeSupport7_030 ++ ridgeSupport7_suffix_031
def ridgeSupport7_suffix_029 : List Nat := ridgeSupport7_029 ++ ridgeSupport7_suffix_030
def ridgeSupport7_suffix_028 : List Nat := ridgeSupport7_028 ++ ridgeSupport7_suffix_029
def ridgeSupport7_suffix_027 : List Nat := ridgeSupport7_027 ++ ridgeSupport7_suffix_028
def ridgeSupport7_suffix_026 : List Nat := ridgeSupport7_026 ++ ridgeSupport7_suffix_027
def ridgeSupport7_suffix_025 : List Nat := ridgeSupport7_025 ++ ridgeSupport7_suffix_026
def ridgeSupport7_suffix_024 : List Nat := ridgeSupport7_024 ++ ridgeSupport7_suffix_025
def ridgeSupport7_suffix_023 : List Nat := ridgeSupport7_023 ++ ridgeSupport7_suffix_024
def ridgeSupport7_suffix_022 : List Nat := ridgeSupport7_022 ++ ridgeSupport7_suffix_023
def ridgeSupport7_suffix_021 : List Nat := ridgeSupport7_021 ++ ridgeSupport7_suffix_022
def ridgeSupport7_suffix_020 : List Nat := ridgeSupport7_020 ++ ridgeSupport7_suffix_021
def ridgeSupport7_suffix_019 : List Nat := ridgeSupport7_019 ++ ridgeSupport7_suffix_020
def ridgeSupport7_suffix_018 : List Nat := ridgeSupport7_018 ++ ridgeSupport7_suffix_019
def ridgeSupport7_suffix_017 : List Nat := ridgeSupport7_017 ++ ridgeSupport7_suffix_018
def ridgeSupport7_suffix_016 : List Nat := ridgeSupport7_016 ++ ridgeSupport7_suffix_017
def ridgeSupport7_suffix_015 : List Nat := ridgeSupport7_015 ++ ridgeSupport7_suffix_016
def ridgeSupport7_suffix_014 : List Nat := ridgeSupport7_014 ++ ridgeSupport7_suffix_015
def ridgeSupport7_suffix_013 : List Nat := ridgeSupport7_013 ++ ridgeSupport7_suffix_014
def ridgeSupport7_suffix_012 : List Nat := ridgeSupport7_012 ++ ridgeSupport7_suffix_013
def ridgeSupport7_suffix_011 : List Nat := ridgeSupport7_011 ++ ridgeSupport7_suffix_012
def ridgeSupport7_suffix_010 : List Nat := ridgeSupport7_010 ++ ridgeSupport7_suffix_011
def ridgeSupport7_suffix_009 : List Nat := ridgeSupport7_009 ++ ridgeSupport7_suffix_010
def ridgeSupport7_suffix_008 : List Nat := ridgeSupport7_008 ++ ridgeSupport7_suffix_009
def ridgeSupport7_suffix_007 : List Nat := ridgeSupport7_007 ++ ridgeSupport7_suffix_008
def ridgeSupport7_suffix_006 : List Nat := ridgeSupport7_006 ++ ridgeSupport7_suffix_007
def ridgeSupport7_suffix_005 : List Nat := ridgeSupport7_005 ++ ridgeSupport7_suffix_006
def ridgeSupport7_suffix_004 : List Nat := ridgeSupport7_004 ++ ridgeSupport7_suffix_005
def ridgeSupport7_suffix_003 : List Nat := ridgeSupport7_003 ++ ridgeSupport7_suffix_004
def ridgeSupport7_suffix_002 : List Nat := ridgeSupport7_002 ++ ridgeSupport7_suffix_003
def ridgeSupport7_suffix_001 : List Nat := ridgeSupport7_001 ++ ridgeSupport7_suffix_002
def ridgeSupport7_suffix_000 : List Nat := ridgeSupport7_000 ++ ridgeSupport7_suffix_001
theorem ridgeSupport7_source : candidateRows 7 =
    (PackedRawNatGrowth.readList 14 1061 ridgeSupport7_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
