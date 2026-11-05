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
def ridgeSupport840_000 : List Nat := [551,552,553,820,821,822,1085,1086,1087,1437,1438,1439,1483,1484,1485,2856,2857,2858,2859,2860,2861,2952,2953,2954,2955,2956,2957,3048,3049,3050,3051,3052]
def ridgeSupport840_001 : List Nat := [3053,3120,3121,3122,3123,3124,3125,3216,3217,3218,3219,3220,3221,3312,3313,3314,3315,3316,3317,3600,3601,3602,3603,3604,3605,3612,3613,3614,3615,3616,3617,3816]
def ridgeSupport840_002 : List Nat := [3817,3818,3819,3820,3821,3912,3913,3914,3915,3916,3917,4008,4009,4010,4011,4012,4013,4296,4297,4298,4299,4300,4301,4308,4309,4310,4311,4312,4313,5760,5761,5762]
def ridgeSupport840_003 : List Nat := [5763,5764,5765,5808,5809,5810,5811,5812,5813,5952,5953,5954,5955,5956,5957,6210,6211,6212,6213,6214,6215,6240,6241,6242,6243,6244,6245,8178,8179,8192,8193,8198]
def ridgeSupport840_004 : List Nat := [8199,8205,8207,8215,8218,8221,8224,8226,8227,8240,8241,8246,8247,8325,8327,8335,8338,8341,8344,8373,8375,8383,8386,8389,8392,8418,8419,8432,8433,8438,8439,8445]
def ridgeSupport840_005 : List Nat := [8447,8455,8458,8461,8464,8466,8467,8480,8481,8486,8487,8565,8567,8575,8578,8581,8584,8613,8615,8623,8626,8629,8632,8844,8845,8846,8847,8848,8849,8856,8857,8858]
def ridgeSupport840_006 : List Nat := [8859,8860,8861,8946,8947,8960,8961,8966,8967,8973,8975,8983,8986,8989,8992,8994,8995,9008,9009,9014,9015,9093,9095,9103,9106,9109,9112,9141,9143,9151,9154,9157]
def ridgeSupport840_007 : List Nat := [9160,9372,9373,9374,9375,9376,9377,9384,9385,9386,9387,9388,9389,10485,10487,10495,10498,10501,10504,10506,10507,10520,10521,10526,10527,10554,10555,10568,10569,10574,10575,10653]
def ridgeSupport840_008 : List Nat := [10655,10663,10666,10669,10672,10680,10681,10682,10683,10684,10685,10902,10903,10904,10905,10906,10907,10932,10933,10934,10935,10936,10937,12261,12263,12268,12321,12323,12331,12334,12337,12340]
def ridgeSupport840_009 : List Nat := [12393,12395,12400,12453,12455,12463,12466,12469,12472,12660,12661,12662,12663,12664,12665,12741,12743,12748,12801,12803,12811,12814,12817,12820,13008,13009,13010,13011,13012,13013,13689,13691]
def ridgeSupport840_010 : List Nat := [13696,13785,13787,13795,13798,13801,13804,13962,13963,13964,13965,13966,13967,14814,14815,14828,14829,14834,14835,14850,14851,14864,14865,14870,14871,14910,14911,14924,14925,14930,14931,15104]
def ridgeSupport840_011 : List Nat := [15106,15114,15119,15120,15125]
def ridgeSupport840_code : Nat := 0x3b15ec43b0fec2bb02ec03a53e94ba4de933a3fe8fba17e85ba11e843a03e80b9f3e7cb9ede7b39dfe77b68fda3b68dda3368bda2b5ecd7a75e6d78f5dbd767580d5ef579cb572d4cb4f2d2cb472d0c853211c83b20bc80f201c7331c7c717179c5e3177c5db175c5d30b8c2d70b2c2bf0a7c297070c1af069c0d3031c0bb02bc08f021bfb2fe7bf96ab9aae2ab7aadaab5aad2a9baa6aa99aa62a97aa5a9bda6f29bba6ea9b9a6e29b0a6b69aaa69e99fa67694fa53a949a52293ba4ea91fa47a919a46290ba42a908a416902a3fe8f7a3d64ad92b24ab92aa4a992a24a1928249f927a49d92723c88f163c28efe3b78ed63988e563928e3e3878e163378cda3318cc23238c8a3208c7631a8c5e30f8c363078c1a3018c022f38bca29d8a7229b8a6a2998a622918a4228f8a3a28d8a321b886d61b286be1a78696188861618285fe17785d6127849a1218482113844a110843610a841e0ff83f60f783da0f183c20e3838a0c883160c282fe0b782d60988256092823e087821603780da03180c2023808a020807601a805e00f8036007801a0018001ff37fc98656191863618986161818476119845611184361097455d117435d097415d016b55ad16b35ac96b15ac16855a116835a096815a010d943610d743590d543510cd43310cb43290c94320fad3eb0fab3ea8fa93ea0f4d3d30f4b3d28f493d20eed3bb0eeb3ba8ee93ba0e213880e1f3878e1d3870e153850e133848e113840cf533d0cf333c8cf133c0c953250c933248c913240c3530d0c3330c8c3130c0bed2fb0beb2fa8be92fa0b8d2e30b8b2e28b892e20b2d2cb0b2b2ca8b292ca05cd17305cb167c59e167443f10f843d0cd83350cd022908a0227
def ridgeSupport840_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport840_code
def ridgeSupport840_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport840_code
def ridgeSupport840_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport840_code
def ridgeSupport840_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport840_code
def ridgeSupport840_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport840_code
def ridgeSupport840_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport840_code
def ridgeSupport840_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport840_code
def ridgeSupport840_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport840_code
def ridgeSupport840_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport840_code
def ridgeSupport840_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport840_code
def ridgeSupport840_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport840_code
def ridgeSupport840_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport840_code
def ridgeSupport840_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport840_code
def ridgeSupport840_suffix_012 : List Nat := []
def ridgeSupport840_suffix_011 : List Nat := ridgeSupport840_011 ++ ridgeSupport840_suffix_012
def ridgeSupport840_suffix_010 : List Nat := ridgeSupport840_010 ++ ridgeSupport840_suffix_011
def ridgeSupport840_suffix_009 : List Nat := ridgeSupport840_009 ++ ridgeSupport840_suffix_010
def ridgeSupport840_suffix_008 : List Nat := ridgeSupport840_008 ++ ridgeSupport840_suffix_009
def ridgeSupport840_suffix_007 : List Nat := ridgeSupport840_007 ++ ridgeSupport840_suffix_008
def ridgeSupport840_suffix_006 : List Nat := ridgeSupport840_006 ++ ridgeSupport840_suffix_007
def ridgeSupport840_suffix_005 : List Nat := ridgeSupport840_005 ++ ridgeSupport840_suffix_006
def ridgeSupport840_suffix_004 : List Nat := ridgeSupport840_004 ++ ridgeSupport840_suffix_005
def ridgeSupport840_suffix_003 : List Nat := ridgeSupport840_003 ++ ridgeSupport840_suffix_004
def ridgeSupport840_suffix_002 : List Nat := ridgeSupport840_002 ++ ridgeSupport840_suffix_003
def ridgeSupport840_suffix_001 : List Nat := ridgeSupport840_001 ++ ridgeSupport840_suffix_002
def ridgeSupport840_suffix_000 : List Nat := ridgeSupport840_000 ++ ridgeSupport840_suffix_001
theorem ridgeSupport840_source : candidateRows 840 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport840_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
