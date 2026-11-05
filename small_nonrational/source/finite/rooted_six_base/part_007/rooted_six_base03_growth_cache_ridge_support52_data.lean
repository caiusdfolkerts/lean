module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport52_000 : List Nat := [0,61,62,63,64,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988]
def ridgeSupport52_001 : List Nat := [989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020]
def ridgeSupport52_002 : List Nat := [1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,3966,3967,3968,3969,3970,3971,3972,3973,3974,3975,3976,3977,3978,3979,3980,3981,3982,3983,3984]
def ridgeSupport52_003 : List Nat := [3985,3986,3987,3988,3989,3990,3991,3992,3993,3994,3995,3996,3997,3998,3999,4000,4001,4002,4003,4004,4005,4006,4007,4008,4009,4010,4011,4012,4013,4014,4015,4016]
def ridgeSupport52_004 : List Nat := [4017,4018,4019,4020,4021,4022,4023,4024,4025,4026,4027,4028,4029,4030,4031,4032,4033,4034,4035,4036,4037,4038,4039,4040,4041,4042,4043,4044,4045,4046,4047,4048]
def ridgeSupport52_005 : List Nat := [4049,4050,4051,4052,4053,4054,4055,4056,4057,4058,4059,4060,4061,4062,4063,4064,4065,4066,4067,4068,4069,4070,4071,4072,4073,4074,4075,4076,4077,4078,4079,4080]
def ridgeSupport52_006 : List Nat := [4081,4082,4083,4084,4085,4086,4087,4088,4089,4090,4091,4092,4093,4094,4095,4096,4097,4098,4099,4100,4101,4102,4103,4104,4105,4106,4107,4108,4109,4110,4111,4112]
def ridgeSupport52_007 : List Nat := [4113,4114,4115,4116,4117,4118,4119,4120,4121,4122,4123,4124,4125,4126,4127,4128,4129,4130,4131,4132,4133,4134,4135,4136,4137,4138,4139,4140,4141,4142,4143,4144]
def ridgeSupport52_008 : List Nat := [4145,4146,4147,4148,4149,4150,4151,4152,4153,4154,4155,4156,4157,4158,4159,4160,4161,4162,4163,4164,4165,4166,4167,4168,4169,4170,4171,4172,4173,4174,4175,4176]
def ridgeSupport52_009 : List Nat := [4177,4178,4179,4180,4181,4626,4627,4628,4629,4630,4631,4632,4633,4634,4635,4636,4637,4638,4639,4640,4641,4642,4643,4644,4645,4646,4647,4648,4649,5190,5191,5192]
def ridgeSupport52_010 : List Nat := [5193,5194,5195,5196,5197,5198,5199,5200,5201,5202,5203,5204,5205,5206,5207,5208,5209,5210,5211,5212,5213]
def ridgeSupport52_code : Nat := 0x145da2e516e8b5459a2c515e8ad455a2a514e8a5451a28513e89d44da26512e895449a24511e88d229914489e44d225912488e445221910487e43d21d90e486e43521990c485e42d21590a484e42505582a414e0a5051828413e09d04d826412e095049824411e08d045822410e08504182040fe07d03d81e40ee07503981c40de06d03581a40ce06503181840be05d02d81640ae055029814409e04d025812408e045021810407e03d01d80e406e03501980c405e02d01580a404e025011808403e01d00d806402e015009804401e00d005802400e0050018003ffdffcffd7fe3fedff4ff97fc3fddfecff57fa3fcdfe4ff17f83fbdfdcfed7f63fadfd4fe97f43f9dfccfe57f23f8dfc4fe17f03f7dfbcfdd7ee3f6dfb4fd97ec3f5dfacfd57ea3f4dfa4fd17e83f3df9cfcd7e63f2df94fc97e43f1df8cfc57e23f0df84fc17e03efdf7cfbd7de3eedf74fb97dc3eddf6cfb57da3ecdf64fb17d83ebdf5cfad7d63eadf54fa97d43e9df4cfa57d23e8df44fa17d03e7df3cf9d7ce3e6df34f997cc3e5df2cf957ca3e4df24f917c83e3df1cf8d7c63e2df14f897c43e1df0cf857c23e0df04f817c03dfdefc409204101c80c405202100c8044012000ffc7fc3fd1fe0fec7f43f91fc0fdc7ec3f51fa0fcc7e43f11f80fbc7dc3ed1f60fac7d43e91f40f9c7cc3e51f20f8c7c43e11f00f7c7bc3dd1ee0f6c7b43d91ec0f5c7ac3d51ea0f4c7a43d11e80f3c79c3cd1e60f2c7943c91e40f1c78c3c51e20f0c78404001f80f807a000
def ridgeSupport52_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport52_code
def ridgeSupport52_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport52_code
def ridgeSupport52_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport52_code
def ridgeSupport52_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport52_code
def ridgeSupport52_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport52_code
def ridgeSupport52_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport52_code
def ridgeSupport52_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport52_code
def ridgeSupport52_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport52_code
def ridgeSupport52_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport52_code
def ridgeSupport52_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport52_code
def ridgeSupport52_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport52_code
def ridgeSupport52_rest_011 : Nat := PackedRawNatGrowth.drop 4433 ridgeSupport52_code
def ridgeSupport52_suffix_011 : List Nat := []
def ridgeSupport52_suffix_010 : List Nat := ridgeSupport52_010 ++ ridgeSupport52_suffix_011
def ridgeSupport52_suffix_009 : List Nat := ridgeSupport52_009 ++ ridgeSupport52_suffix_010
def ridgeSupport52_suffix_008 : List Nat := ridgeSupport52_008 ++ ridgeSupport52_suffix_009
def ridgeSupport52_suffix_007 : List Nat := ridgeSupport52_007 ++ ridgeSupport52_suffix_008
def ridgeSupport52_suffix_006 : List Nat := ridgeSupport52_006 ++ ridgeSupport52_suffix_007
def ridgeSupport52_suffix_005 : List Nat := ridgeSupport52_005 ++ ridgeSupport52_suffix_006
def ridgeSupport52_suffix_004 : List Nat := ridgeSupport52_004 ++ ridgeSupport52_suffix_005
def ridgeSupport52_suffix_003 : List Nat := ridgeSupport52_003 ++ ridgeSupport52_suffix_004
def ridgeSupport52_suffix_002 : List Nat := ridgeSupport52_002 ++ ridgeSupport52_suffix_003
def ridgeSupport52_suffix_001 : List Nat := ridgeSupport52_001 ++ ridgeSupport52_suffix_002
def ridgeSupport52_suffix_000 : List Nat := ridgeSupport52_000 ++ ridgeSupport52_suffix_001
theorem ridgeSupport52_source : candidateSupports 52 =
    (PackedRawNatGrowth.readList 13 341 ridgeSupport52_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
