module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport13_000 : List Nat := [0,15,16,17,18,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384]
def ridgeSupport13_001 : List Nat := [385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416]
def ridgeSupport13_002 : List Nat := [417,418,419,420,421,422,423,424,425,426,427,428,429,3880,3881,3882,3883,3884,3885,3886,3887,3888,3889,3890,3891,3892,3893,3894,3895,3896,3897,3898]
def ridgeSupport13_003 : List Nat := [3899,3900,3901,3902,3903,3904,3905,3906,3907,3908,3909,3910,3911,3912,3913,3914,3915,3916,3917,3918,3919,3920,3921,3922,3923,3924,3925,3926,3927,3928,3929,3930]
def ridgeSupport13_004 : List Nat := [3931,3932,3933,3934,3935,3936,3937,3938,3939,3940,3941,3942,3943,3944,3945,3946,3947,3948,3949,3950,3951,3952,3953,3954,3955,3956,3957,3958,3959,3960,3961,3962]
def ridgeSupport13_005 : List Nat := [3963,3964,3965,3966,3967,3968,3969,3970,3971,3972,3973,3974,3975,3976,3977,3978,3979,3980,3981,3982,3983,3984,3985,3986,3987,3988,3989,3990,3991,3992,3993,3994]
def ridgeSupport13_006 : List Nat := [3995,3996,3997,3998,3999,4000,4001,4002,4003,4004,4005,4006,4007,4008,4009,4010,4011,4012,4013,4014,4015,4016,4017,4018,4019,4020,4021,4022,4023,4024,4025,4026]
def ridgeSupport13_007 : List Nat := [4027,4028,4029,4030,4031,4032,4033,4034,4035,4036,4037,4038,4039,4040,4041,4042,4043,4044,4045,4046,4047,4048,4049,4050,4051,4052,4053,4054,4055,4056,4057,4058]
def ridgeSupport13_008 : List Nat := [4059,4060,4061,4062,4063,4064,4065,4066,4067,4068,4069,4070,4071,4072,4073,4074,4075,4076,4077,4078,4079,4080,4081,4082,4083,4084,4085,4086,4087,4088,4089,4090]
def ridgeSupport13_009 : List Nat := [4091,4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,4106,4107,4108,4109,4110,4111,4112,4113,4114,4115,4116,4117,4118,4119,4120,4121,4122]
def ridgeSupport13_010 : List Nat := [4123,4124,4125,4126,4127,4128,4129,4130,4131,4132,4133,4134,4135,4136,4137,4138,4139,4140,4141,4142,4143,4144,4145,4146,4147,4148,4149,4150,4151,4152,4153,4154]
def ridgeSupport13_011 : List Nat := [4155,4156,4157,4158,4159,4160,4161,4162,4163,4164,4165,4166,4167,7312,7313,7314,7315,7316,7317,7318,7319,7320,7321,7322,7323,7324,7325,7326,7327,7328,7329,7330]
def ridgeSupport13_012 : List Nat := [7331,7332,7333,7334,7335,8104,8105,8106,8107,8108,8109,8110,8111,8112,8113,8114,8115,8116,8117,8118,8119,8120,8121,8122,8123,8124,8125,8126,8127,8128,8129,8130]
def ridgeSupport13_013 : List Nat := [8131,8132,8133,8134,8135,8136,8137,8138,8139,8140,8141,8142,8143,8144,8145,8146,8147,8148,8149,8150,8151,8152,8153,8154,8155,8156,8157,8158,8159,8160,8161,8162]
def ridgeSupport13_014 : List Nat := [8163,8164,8165,8166,8167,8168,8169,8170,8171,8172,8173,8174,8175]
def ridgeSupport13_code : Nat := 0x1fef7fb9fed7fb1feb7fa9fe97fa1fe77f99fe57f91fe37f89fe17f81fdf7f79fdd7f71fdb7f69fd97f61fd77f59fd57f51fd37f49fd17f41fcf7f39fcd7f31fcb7f29fc97f21fc77f19fc57f11fc37f09fc17f01fbf7ef9fbd7ef1fbb7ee9fb97ee1fb77ed9fb57ed1fb37ec9fb17ec1faf7eb9fad7eb1fab7ea9fa97ea1ca77299ca57291ca37289ca17281c9f7279c9d7271c9b7269c997261c977259c957251c937249c917241047411904541110434109041410103f40f903d40f103b40e903940e103740d903540d103340c903140c102f40b902d40b102b40a902940a1027409902540910234089021408101f407901d407101b40690194061017405901540510134049011404100f403900d403100b402900940210074019005401100340090014000fff3ff8ffd3ff0ffb3fe8ff93fe0ff73fd8ff53fd0ff33fc8ff13fc0fef3fb8fed3fb0feb3fa8fe93fa0fe73f98fe53f90fe33f88fe13f80fdf3f78fdd3f70fdb3f68fd93f60fd73f58fd53f50fd33f48fd13f40fcf3f38fcd3f30fcb3f28fc93f20fc73f18fc53f10fc33f08fc13f00fbf3ef8fbd3ef0fbb3ee8fb93ee0fb73ed8fb53ed0fb33ec8fb13ec0faf3eb8fad3eb0fab3ea8fa93ea0fa73e98fa53e90fa33e88fa13e80f9f3e78f9d3e70f9b3e68f993e60f973e58f953e50f933e48f913e40f8f3e38f8d3e30f8b3e28f893e20f873e18f853e10f833e08f813e00f7f3df8f7d3df0f7b3de8f793de0f773dd8f753dd0f733dc8f713dc0f6f3db8f6d3db0f6b3da8f693da0f673d98f653d90f633d88f613d80f5f3d78f5d3d70f5b3d68f593d60f573d58f553d50f533d48f513d40f4f3d38f4d3d30f4b3d28f493d20f473d18f453d10f433d08f413d00f3f3cf8f3d3cf0f3b3ce8f393ce0f373cd8f353cd0f333cc8f313cc0f2f3cb8f2d3cb0f2b3ca8f293ca01ad06b01ab06a81a906a01a706981a506901a306881a1068019f067819d067019b06681990660197065819506501930648191064018f063818d063018b06281890620187061818506101830608181060017f05f817d05f017b05e817905e017705d817505d017305c817105c016f05b816d05b016b05a816905a016705980120044010003c000
def ridgeSupport13_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport13_code
def ridgeSupport13_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport13_code
def ridgeSupport13_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport13_code
def ridgeSupport13_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport13_code
def ridgeSupport13_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport13_code
def ridgeSupport13_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport13_code
def ridgeSupport13_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport13_code
def ridgeSupport13_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport13_code
def ridgeSupport13_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport13_code
def ridgeSupport13_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport13_code
def ridgeSupport13_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport13_code
def ridgeSupport13_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport13_code
def ridgeSupport13_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport13_code
def ridgeSupport13_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport13_code
def ridgeSupport13_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport13_code
def ridgeSupport13_rest_015 : Nat := PackedRawNatGrowth.drop 6454 ridgeSupport13_code
def ridgeSupport13_suffix_015 : List Nat := []
def ridgeSupport13_suffix_014 : List Nat := ridgeSupport13_014 ++ ridgeSupport13_suffix_015
def ridgeSupport13_suffix_013 : List Nat := ridgeSupport13_013 ++ ridgeSupport13_suffix_014
def ridgeSupport13_suffix_012 : List Nat := ridgeSupport13_012 ++ ridgeSupport13_suffix_013
def ridgeSupport13_suffix_011 : List Nat := ridgeSupport13_011 ++ ridgeSupport13_suffix_012
def ridgeSupport13_suffix_010 : List Nat := ridgeSupport13_010 ++ ridgeSupport13_suffix_011
def ridgeSupport13_suffix_009 : List Nat := ridgeSupport13_009 ++ ridgeSupport13_suffix_010
def ridgeSupport13_suffix_008 : List Nat := ridgeSupport13_008 ++ ridgeSupport13_suffix_009
def ridgeSupport13_suffix_007 : List Nat := ridgeSupport13_007 ++ ridgeSupport13_suffix_008
def ridgeSupport13_suffix_006 : List Nat := ridgeSupport13_006 ++ ridgeSupport13_suffix_007
def ridgeSupport13_suffix_005 : List Nat := ridgeSupport13_005 ++ ridgeSupport13_suffix_006
def ridgeSupport13_suffix_004 : List Nat := ridgeSupport13_004 ++ ridgeSupport13_suffix_005
def ridgeSupport13_suffix_003 : List Nat := ridgeSupport13_003 ++ ridgeSupport13_suffix_004
def ridgeSupport13_suffix_002 : List Nat := ridgeSupport13_002 ++ ridgeSupport13_suffix_003
def ridgeSupport13_suffix_001 : List Nat := ridgeSupport13_001 ++ ridgeSupport13_suffix_002
def ridgeSupport13_suffix_000 : List Nat := ridgeSupport13_000 ++ ridgeSupport13_suffix_001
theorem ridgeSupport13_source : candidateSupports 13 =
    (PackedRawNatGrowth.readList 14 461 ridgeSupport13_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
