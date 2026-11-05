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
def ridgeSupport904_000 : List Nat := [572,573,574,841,842,843,1106,1107,1108,1458,1459,1460,1480,1481,1482,2850,2851,2852,2853,2854,2855,2946,2947,2948,2949,2950,2951,3042,3043,3044,3045,3046]
def ridgeSupport904_001 : List Nat := [3047,3114,3115,3116,3117,3118,3119,3210,3211,3212,3213,3214,3215,3306,3307,3308,3309,3310,3311,3708,3709,3710,3711,3712,3713,3720,3721,3722,3723,3724,3725,3810]
def ridgeSupport904_002 : List Nat := [3811,3812,3813,3814,3815,3906,3907,3908,3909,3910,3911,4002,4003,4004,4005,4006,4007,4404,4405,4406,4407,4408,4409,4416,4417,4418,4419,4420,4421,5754,5755,5756]
def ridgeSupport904_003 : List Nat := [5757,5758,5759,5802,5803,5804,5805,5806,5807,5946,5947,5948,5949,5950,5951,6318,6319,6320,6321,6322,6323,6348,6349,6350,6351,6352,6353,8184,8185,8190,8191,8196]
def ridgeSupport904_004 : List Nat := [8197,8211,8213,8217,8219,8223,8225,8232,8233,8238,8239,8244,8245,8331,8333,8337,8339,8343,8345,8379,8381,8385,8387,8391,8393,8424,8425,8430,8431,8436,8437,8451]
def ridgeSupport904_005 : List Nat := [8453,8457,8459,8463,8465,8472,8473,8478,8479,8484,8485,8571,8573,8577,8579,8583,8585,8619,8621,8625,8627,8631,8633,8916,8917,8918,8919,8920,8921,8928,8929,8930]
def ridgeSupport904_006 : List Nat := [8931,8932,8933,8952,8953,8958,8959,8964,8965,8979,8981,8985,8987,8991,8993,9000,9001,9006,9007,9012,9013,9099,9101,9105,9107,9111,9113,9147,9149,9153,9155,9159]
def ridgeSupport904_007 : List Nat := [9161,9444,9445,9446,9447,9448,9449,9456,9457,9458,9459,9460,9461,10491,10493,10497,10499,10503,10505,10512,10513,10518,10519,10524,10525,10560,10561,10566,10567,10572,10573,10659]
def ridgeSupport904_008 : List Nat := [10661,10665,10667,10671,10673,10674,10675,10676,10677,10678,10679,10974,10975,10976,10977,10978,10979,11004,11005,11006,11007,11008,11009,12265,12267,12269,12327,12329,12333,12335,12339,12341]
def ridgeSupport904_009 : List Nat := [12397,12399,12401,12459,12461,12465,12467,12471,12473,12714,12715,12716,12717,12718,12719,12745,12747,12749,12807,12809,12813,12815,12819,12821,13062,13063,13064,13065,13066,13067,13693,13695]
def ridgeSupport904_010 : List Nat := [13697,13791,13793,13797,13799,13803,13805,14016,14017,14018,14019,14020,14021,14820,14821,14826,14827,14832,14833,14856,14857,14862,14863,14868,14869,14916,14917,14922,14923,14928,14929,15110]
def ridgeSupport904_011 : List Nat := [15112,15116,15118,15122,15124]
def ridgeSupport904_code : Nat := 0x3b14ec4bb0eec33b08ec1ba51e943a4be92ba45e913a15e853a0fe83ba09e8239f1e7c39ebe7ab9e5e7936c5db136c3db0b6c1db035edd7af5e7d7975e1d77f581d5ff57dcc2f30acc27308cc1f306c857213c83f20dc827207c7371cbc7271afc6bb1adc6b31abc6ab0b9c2df0b3c2c70adc2af071c1bf06dc0d7033c0bf02dc0a7027bfb6febbfa6b01ac02affabfaafdabf2ae3ab8aae1ab82adfab7a9b7a6da9b5a6d29b3a6ca9b1a6be9aba6a69a5a68e94da532947a51a941a50291da472917a45a911a442909a41e903a4068fda3ee4f593d24f393ca4f193c24e993a24e7939a4e593923c98f1e3c38f063bd8eee3998e5e3938e4638d8e2e3358cd232f8cba3298ca23218c7e31b8c663158c4e3058c122ff8bfa2f98be22e58b922e38b8a2e18b822d98b622d78b5a2d58b521b986de1b386c61ad86ae189861e183860617d85ee125849211f847a1198462111843e10b8426105840e0f583d20ef83ba0e983a20c9831e0c383060bd82ee099825e093824608d822e03580d202f80ba02980a2021807e01b8066015804e0058011fff7ff9ff97fe18d163418cf63398cd63318b362c98b162c18af62b973f5cf973d5cf173b5ce96af5ab96ad5ab16ab5aa967f59f967d59f167b59e914545111434509141450113944e113744d913544d0fa73e98fa53e90fa33e88f473d18f453d10f433d08ee73b98ee53b90ee33b88e8d3a30e8b3a28e893a20e813a00e7f39f8e7d39f0cef33b8ced33b0ceb33a8c8f3238c8d3230c8b3228c2f30b8c2d30b0c2b30a8be72f98be52f90be32f88b872e18b852e10b832e08b272c98b252c90b232c885ca17245c816d05b316c8454114c4520d2c34a0d2423e08f423c
def ridgeSupport904_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport904_code
def ridgeSupport904_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport904_code
def ridgeSupport904_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport904_code
def ridgeSupport904_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport904_code
def ridgeSupport904_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport904_code
def ridgeSupport904_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport904_code
def ridgeSupport904_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport904_code
def ridgeSupport904_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport904_code
def ridgeSupport904_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport904_code
def ridgeSupport904_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport904_code
def ridgeSupport904_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport904_code
def ridgeSupport904_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport904_code
def ridgeSupport904_rest_012 : Nat := PackedRawNatGrowth.drop 4998 ridgeSupport904_code
def ridgeSupport904_suffix_012 : List Nat := []
def ridgeSupport904_suffix_011 : List Nat := ridgeSupport904_011 ++ ridgeSupport904_suffix_012
def ridgeSupport904_suffix_010 : List Nat := ridgeSupport904_010 ++ ridgeSupport904_suffix_011
def ridgeSupport904_suffix_009 : List Nat := ridgeSupport904_009 ++ ridgeSupport904_suffix_010
def ridgeSupport904_suffix_008 : List Nat := ridgeSupport904_008 ++ ridgeSupport904_suffix_009
def ridgeSupport904_suffix_007 : List Nat := ridgeSupport904_007 ++ ridgeSupport904_suffix_008
def ridgeSupport904_suffix_006 : List Nat := ridgeSupport904_006 ++ ridgeSupport904_suffix_007
def ridgeSupport904_suffix_005 : List Nat := ridgeSupport904_005 ++ ridgeSupport904_suffix_006
def ridgeSupport904_suffix_004 : List Nat := ridgeSupport904_004 ++ ridgeSupport904_suffix_005
def ridgeSupport904_suffix_003 : List Nat := ridgeSupport904_003 ++ ridgeSupport904_suffix_004
def ridgeSupport904_suffix_002 : List Nat := ridgeSupport904_002 ++ ridgeSupport904_suffix_003
def ridgeSupport904_suffix_001 : List Nat := ridgeSupport904_001 ++ ridgeSupport904_suffix_002
def ridgeSupport904_suffix_000 : List Nat := ridgeSupport904_000 ++ ridgeSupport904_suffix_001
theorem ridgeSupport904_source : candidateRows 904 =
    (PackedRawNatGrowth.readList 14 357 ridgeSupport904_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
