module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport82_000 : List Nat := [35,45,55,56,57,624,625,628,629,634,636,637,640,641,646,648,649,652,653,658,780,781,784,785,790,792,793,796,797,802,804,805]
def ridgeSupport82_001 : List Nat := [808,809,814,936,937,939,940,941,942,944,945,947,948,950,951,957,958,960,961,962,963,965,966,968,969,971,972,978,979,981,982,983]
def ridgeSupport82_002 : List Nat := [984,986,987,989,990,992,993,4168,4169,4170,4171,4172,4173,4174,4175,4180,4181,4186,4187,4192,4193,4194,4195,4196,4197,4198,4199,4204,4205,4210,4211,4216]
def ridgeSupport82_003 : List Nat := [4217,4218,4219,4220,4221,4240,4241,4242,4243,4244,4245,4264,4265,4266,4267,4268,4269,4288,4289,4290,4291,4292,4293,4312,4313,4314,4315,4316,4317,4336,4337,4338]
def ridgeSupport82_004 : List Nat := [4339,4340,4341,4360,4361,4362,4363,4364,4365,4369,4371,4375,4377,4381,4383,4654,4655,4672,4673,4690,4691,4699,4701,4705,4707,4708,4709,4726,4727,4744,4745,4762]
def ridgeSupport82_005 : List Nat := [4763,4771,4773,4777,4779,4780,4781,4798,4799,4816,4817,4834,4835,4843,4845,4849,4851,4852,4853,5182,5183,5200,5201,5218,5219,5227,5229,5233,5235,5236,5237,5254]
def ridgeSupport82_006 : List Nat := [5255,5272,5273,5290,5291,5299,5301,5305,5307,5308,5309,5326,5327,5344,5345,5362,5363,5371,5373,5377,5379,5380,5381,7336,7337,7338,7339,7340,7341,8176,8177,8178]
def ridgeSupport82_007 : List Nat := [8179,8180,8181,8200,8201,8202,8203,8204,8205,8212,8213,8214,8215,8216,8217,8275,8277,8284,8285,8293,8295,8302,8303,8311,8313,8320,8321,8395,8397,8404,8405,8413]
cert_ridgeSupport_7 82 008 8415 8422 8423 8431 8433 8440 8441
cert_ridgeSupport_code_3 82
cert_ridgeSupport_rest_2 82 000 0
cert_ridgeSupport_rest_2 82 001 448
cert_ridgeSupport_rest_2 82 002 896
cert_ridgeSupport_rest_2 82 003 1344
cert_ridgeSupport_rest_2 82 004 1792
cert_ridgeSupport_rest_2 82 005 2240
cert_ridgeSupport_rest_2 82 006 2688
cert_ridgeSupport_rest_2 82 007 3136
cert_ridgeSupport_rest_2 82 008 3584
cert_ridgeSupport_rest_2 82 009 3682
cert_ridgeSupport_suffix_4 82 009
cert_ridgeSupport_suffix_3 82 008 009
cert_ridgeSupport_suffix_3 82 007 008
cert_ridgeSupport_suffix_3 82 006 007
cert_ridgeSupport_suffix_3 82 005 006
cert_ridgeSupport_suffix_3 82 004 005
cert_ridgeSupport_suffix_3 82 003 004
cert_ridgeSupport_suffix_3 82 002 003
cert_ridgeSupport_suffix_3 82 001 002
cert_ridgeSupport_suffix_3 82 000 001
cert_ridgeSupport_source_3 82 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
