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
def ridgeSupport74_000 : List Nat := [5,45,46,47,188,191,193,196,198,200,203,205,208,210,212,215,217,220,222,765,770,771,773,774,775,776,778,779,781,782,784,785]
def ridgeSupport74_001 : List Nat := [791,792,794,795,796,797,799,800,802,803,805,806,812,813,815,816,817,818,820,821,823,824,826,827,3114,3115,3116,3117,3118,3119,3120,3121]
def ridgeSupport74_002 : List Nat := [3126,3127,3132,3133,3138,3139,3140,3141,3142,3143,3144,3145,3150,3151,3156,3157,3162,3163,3164,3165,3166,3167,3174,3175,3176,3177,3178,3179,3186,3187,3188,3189]
def ridgeSupport74_003 : List Nat := [3190,3191,3194,3196,3200,3202,3206,3208,3210,3211,3212,3213,3214,3215,3218,3220,3224,3226,3230,3232,3234,3235,3236,3237,3238,3239,3264,3265,3270,3271,3276,3277]
def ridgeSupport74_004 : List Nat := [3288,3289,3294,3295,3300,3301,3312,3313,3315,3317,3318,3319,3321,3323,3324,3325,3327,3329,3336,3337,3339,3341,3342,3343,3345,3347,3348,3349,3351,3353,3362,3364]
def ridgeSupport74_005 : List Nat := [3368,3370,3374,3376,3380,3382,3386,3388,3390,3391,3396,3397,3402,3403,3408,3409,3420,3421,3426,3427,3435,3437,3441,3443,3450,3451,3462,3463,3477,3479,3483,3485]
def ridgeSupport74_006 : List Nat := [3488,3490,3494,3496,3498,3499,3504,3505,3510,3511,3516,3517,3528,3529,3534,3535,3543,3545,3549,3551,3558,3559,3570,3571,3585,3587,3591,3593,3596,3598,3602,3604]
def ridgeSupport74_007 : List Nat := [3606,3607,3612,3613,3618,3619,3624,3625,3636,3637,3642,3643,3651,3653,3657,3659,3666,3667,3678,3679,3693,3695,3699,3701,7122,7125,7127,7129,7130,7133,7135,7137]
def ridgeSupport74_008 : List Nat := [7138,7141,7143,7145,8418,8419,8420,8421,8422,8423,8424,8425,8430,8431,8436,8437,8442,8443,8444,8445,8446,8447,8448,8449,8454,8455,8460,8461,8466,8467,8468,8469]
def ridgeSupport74_009 : List Nat := [8470,8471,8490,8491,8492,8493,8494,8495,8514,8515,8516,8517,8518,8519,8538,8539,8540,8541,8542,8543,8562,8563,8564,8565,8566,8567,8586,8587,8588,8589,8590,8591]
def ridgeSupport74_010 : List Nat := [8610,8611,8612,8613,8614,8615,8619,8621,8625,8627,8631,8633,8676,8677,8688,8689,8697,8699,8703,8705,8712,8713,8724,8725,8748,8749,8760,8761,8769,8771,8775,8777]
def ridgeSupport74_011 : List Nat := [8784,8785,8796,8797,8820,8821,8832,8833,8841,8843,8847,8849,8856,8857,8868,8869,11538,11540,11542,11544,11549,11553,11554,11556,11558,11560,11565,11569,11570,11572,11574,11576]
def ridgeSupport74_012 : List Nat := [11581,11585,12378,12379,12380,12381,12382,12383,12390,12391,12392,12393,12394,12395,12402,12403,12404,12405,12406,12407,12426,12427,12428,12429,12430,12431,12450,12451,12452,12453,12454,12455]
def ridgeSupport74_013 : List Nat := [12459,12461,12465,12467,12471,12473,12474,12475,12476,12477,12478,12479,12483,12485,12489,12491,12495,12497,12501,12502,12504,12505,12507,12508,12513,12515,12519,12521,12528,12529,12540,12541]
def ridgeSupport74_014 : List Nat := [12549,12551,12555,12557,12560,12562,12567,12569,12573,12575,12582,12583,12594,12595,12603,12605,12609,12611,12614,12616,12621,12623,12627,12629,12636,12637,12648,12649,12657,12659,12663,12665]
def ridgeSupport74_015 : List Nat := [12668,12670,14382,14384,14386,14388,14390,14392,14478,14479,14480,14481,14482,14483,14493,14495,14499,14501,14505,14507,14850,14851,14852,14853,14854,14855,15222,15226,15230]
def ridgeSupport74_code : Nat := 0x3b7eedebb76e81fa06e817a04e80fa02e2af8a9e2978a3e27f89de24f892e247890e23f88ee0e3836e0d3832e0c382ec5fb17cc5e7177c5cf171c5a7168c57715cc557153c53f14dc523146c50f141c4f713bc4cf132c49f126c47f11dc467117c44b110c43710bc41f105c3f70fcc3c70f0c3a70e7c38f0e1c3730dbc3670d8c35b0d5c3470cfc32f0c9c3170c3c2ff0bec2f70bcc2ef0bac2e70b7c2cf0b1c2b70abc29f0a6c2970a4c28f0a2c23f08ec23708cc22f08ac1df076c1d7074c1cf072c1af06ac1a7068c19f066c17f05ec17705cc16f05ab506d3db4e2d36b4d2d32b4c6d2db4a2d26b492d22b486d1db462d16b452d128a962a48a662988a4628f8a2e2898a0628089d6274897625c89462508926247890e24188e623888b622c8856214882620888061ff87ee1f987c61f087961e486e61b786ce1b186b61ab869e1a686961a4868e1a2863e18e863618c862e18a85de17685d617485ce172857e15e857615c856e15a851e1468516144850e14284be12e84b612c84ae12a845e1168456114844e112843610c841e106840610083fe0fe83f60fc83ee0fa83d60f483be0ee83a60e8839e0e683960e4838e0e26fa5be76f95be26f85bdf6f75bda6f65bd76f55bd239d4e7339bce6d397ce5e394ce52392ce493914e4338ece3a38d4e3438a4e28388ce223874e1c385ce163850e123838e0c3824e07380ce0137ccdf2379cde6377cddd3764dd7373cdce3724dc836f4dbc36dcdb636c4db036acdaa36a0da63688da03674d9b365cd95361cd8635ecd7a35ccd7135b4d6b358cd623574d5c3544d50352cd4a3514d4434fcd3e34f0d3a34d8d3434c0d2e34a8d283490d223464d173454d14344cd11343cd0e3434d0b3424d083404cff33f4cfc33eccf933dccf633d4cf333c4cf03394ce4337ccde3364cd83334ccc331ccc63304cc0329cca63294ca4328cca23280c9e3268c983250c92323cc8e3234c8c322cc8a3220c863208c8031f0c7a31dcc7631d4c7431ccc7231acc6a31a4c68319cc66317cc5e3174c5c316cc5a3154c54313cc4e3124c48311cc463114c44310cc4230f4c3c30dcc3630c4c3030bcc2e30b4c2c30acc2a0cec33a0ce03370cd43340cc83310cc032f0cb432c0c983250c8c3220c8031f0c7431c0c6c31a0c603170c443100c3830d0c2c30a0c203070c183050c0c3020bf40de03700d9035c0d403480d003340cb03200c603100c102fc0bc00bc02e00b4005
def ridgeSupport74_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport74_code
def ridgeSupport74_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport74_code
def ridgeSupport74_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport74_code
def ridgeSupport74_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport74_code
def ridgeSupport74_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport74_code
def ridgeSupport74_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport74_code
def ridgeSupport74_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport74_code
def ridgeSupport74_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport74_code
def ridgeSupport74_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport74_code
def ridgeSupport74_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport74_code
def ridgeSupport74_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport74_code
def ridgeSupport74_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport74_code
def ridgeSupport74_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport74_code
def ridgeSupport74_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport74_code
def ridgeSupport74_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport74_code
def ridgeSupport74_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport74_code
def ridgeSupport74_rest_016 : Nat := PackedRawNatGrowth.drop 7126 ridgeSupport74_code
def ridgeSupport74_suffix_016 : List Nat := []
def ridgeSupport74_suffix_015 : List Nat := ridgeSupport74_015 ++ ridgeSupport74_suffix_016
def ridgeSupport74_suffix_014 : List Nat := ridgeSupport74_014 ++ ridgeSupport74_suffix_015
def ridgeSupport74_suffix_013 : List Nat := ridgeSupport74_013 ++ ridgeSupport74_suffix_014
def ridgeSupport74_suffix_012 : List Nat := ridgeSupport74_012 ++ ridgeSupport74_suffix_013
def ridgeSupport74_suffix_011 : List Nat := ridgeSupport74_011 ++ ridgeSupport74_suffix_012
def ridgeSupport74_suffix_010 : List Nat := ridgeSupport74_010 ++ ridgeSupport74_suffix_011
def ridgeSupport74_suffix_009 : List Nat := ridgeSupport74_009 ++ ridgeSupport74_suffix_010
def ridgeSupport74_suffix_008 : List Nat := ridgeSupport74_008 ++ ridgeSupport74_suffix_009
def ridgeSupport74_suffix_007 : List Nat := ridgeSupport74_007 ++ ridgeSupport74_suffix_008
def ridgeSupport74_suffix_006 : List Nat := ridgeSupport74_006 ++ ridgeSupport74_suffix_007
def ridgeSupport74_suffix_005 : List Nat := ridgeSupport74_005 ++ ridgeSupport74_suffix_006
def ridgeSupport74_suffix_004 : List Nat := ridgeSupport74_004 ++ ridgeSupport74_suffix_005
def ridgeSupport74_suffix_003 : List Nat := ridgeSupport74_003 ++ ridgeSupport74_suffix_004
def ridgeSupport74_suffix_002 : List Nat := ridgeSupport74_002 ++ ridgeSupport74_suffix_003
def ridgeSupport74_suffix_001 : List Nat := ridgeSupport74_001 ++ ridgeSupport74_suffix_002
def ridgeSupport74_suffix_000 : List Nat := ridgeSupport74_000 ++ ridgeSupport74_suffix_001
theorem ridgeSupport74_source : candidateRows 74 =
    (PackedRawNatGrowth.readList 14 509 ridgeSupport74_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
