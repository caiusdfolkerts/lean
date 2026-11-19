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
def ridgeSupport530_000 : List Nat := [38,48,57,59,60,647,650,651,654,657,671,674,675,678,681,683,686,687,690,693,803,806,807,810,813,827,830,831,834,837,839,842]
def ridgeSupport530_001 : List Nat := [843,846,849,956,957,959,960,963,964,965,967,968,970,975,976,977,978,980,981,984,985,986,988,989,991,996,997,998,999,1001,1002,1005]
def ridgeSupport530_002 : List Nat := [1006,1007,1009,1010,1012,1017,1018,4172,4173,4178,4179,4184,4185,4186,4187,4188,4189,4190,4191,4196,4197,4202,4203,4208,4209,4210,4211,4212,4213,4214,4215,4234]
def ridgeSupport530_003 : List Nat := [4235,4236,4237,4238,4239,4258,4259,4260,4261,4262,4263,4282,4283,4284,4285,4286,4287,4306,4307,4308,4309,4310,4311,4330,4331,4332,4333,4334,4335,4354,4355,4356]
def ridgeSupport530_004 : List Nat := [4357,4358,4359,4360,4362,4366,4368,4372,4374,4378,4379,4380,4381,4382,4383,4730,4731,4748,4749,4766,4767,4768,4770,4774,4776,4784,4785,4802,4803,4820,4821,4838]
def ridgeSupport530_005 : List Nat := [4839,4840,4842,4846,4848,4856,4857,4874,4875,4892,4893,4910,4911,4912,4914,4918,4920,4928,4929,5258,5259,5276,5277,5294,5295,5296,5298,5302,5304,5312,5313,5330]
def ridgeSupport530_006 : List Nat := [5331,5348,5349,5366,5367,5368,5370,5374,5376,5384,5385,5402,5403,5420,5421,5438,5439,5440,5442,5446,5448,5456,5457,7354,7355,7356,7357,7358,7359,8194,8195,8196]
def ridgeSupport530_007 : List Nat := [8197,8198,8199,8200,8202,8206,8208,8210,8211,8212,8214,8218,8220,8222,8223,8290,8292,8306,8307,8308,8310,8324,8325,8326,8328,8342,8343,8410,8412,8426,8427,8428]
cert_ridgeSupport_7 530 008 8430 8444 8445 8446 8448 8462 8463
cert_ridgeSupport_code_3 530
cert_ridgeSupport_rest_2 530 000 0
cert_ridgeSupport_rest_2 530 001 448
cert_ridgeSupport_rest_2 530 002 896
cert_ridgeSupport_rest_2 530 003 1344
cert_ridgeSupport_rest_2 530 004 1792
cert_ridgeSupport_rest_2 530 005 2240
cert_ridgeSupport_rest_2 530 006 2688
cert_ridgeSupport_rest_2 530 007 3136
cert_ridgeSupport_rest_2 530 008 3584
cert_ridgeSupport_rest_2 530 009 3682
cert_ridgeSupport_suffix_4 530 009
cert_ridgeSupport_suffix_3 530 008 009
cert_ridgeSupport_suffix_3 530 007 008
cert_ridgeSupport_suffix_3 530 006 007
cert_ridgeSupport_suffix_3 530 005 006
cert_ridgeSupport_suffix_3 530 004 005
cert_ridgeSupport_suffix_3 530 003 004
cert_ridgeSupport_suffix_3 530 002 003
cert_ridgeSupport_suffix_3 530 001 002
cert_ridgeSupport_suffix_3 530 000 001
cert_ridgeSupport_source_3 530 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
