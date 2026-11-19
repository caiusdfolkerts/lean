module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public meta import CertificateNumbers
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport290_000 : List Nat := [39,48,50,52,529,627,630,631,634,637,651,654,655,658,661,676,677,680,681,686,771,772,774,775,778,779,780,782,783,785,790,791]
def ridgeSupport290_001 : List Nat := [813,815,816,818,819,821,823,824,826,827,830,831,834,836,837,839,840,842,844,845,847,848,851,852,3742,3743,3748,3749,3752,3753,3754,3755]
def ridgeSupport290_002 : List Nat := [3756,3757,3762,3763,3766,3767,3772,3773,3776,3777,3778,3779,3780,3781,3786,3787,3800,3801,3802,3803,3804,3805,3824,3825,3826,3827,3828,3829,3848,3849,3850,3851]
def ridgeSupport290_003 : List Nat := [3852,3853,3872,3873,3874,3875,3876,3877,3896,3897,3898,3899,3900,3901,3920,3921,3922,3923,3924,3925,3933,3936,3939,3942,3944,3945,3946,3947,3948,3949,3950,3952]
def ridgeSupport290_004 : List Nat := [4230,4231,4248,4249,4266,4267,4268,4270,4274,4276,4284,4285,4372,4373,4390,4391,4408,4409,4413,4416,4419,4422,4426,4427,4444,4445,4462,4463,4480,4481,4485,4488]
def ridgeSupport290_005 : List Nat := [4491,4494,4498,4499,4765,4767,4770,4772,4777,4779,4797,4799,4802,4804,4809,4811,4828,4830,4835,4837,4840,4842,6514,6515,6518,6519,6522,6523,6526,6527,6530,6531]
def ridgeSupport290_006 : List Nat := [6534,6535,6548,6549,6550,6551,6552,6553,6572,6573,6574,6575,6576,6577,6585,6588,6591,6594,6596,6597,6598,6599,6600,6601,6602,6604,6609,6612,6615,6618,6620,6621]
def ridgeSupport290_007 : List Nat := [6622,6623,6624,6625,6626,6628,6632,6634,6635,6637,6642,6643,6786,6787,6788,6790,6794,6796,6804,6805,6813,6815,6822,6823,6824,6826,6892,6893,6897,6900,6903,6906]
def ridgeSupport290_008 : List Nat := [6910,6911,6920,6925,6928,6929,6933,6936,6946,6947,6951,6954,6957,6960,6964,6965,6974,6979,6982,6983,6987,6990,7129,7130,7137,7138,7144,7147,7498,7499,7502,7503]
cert_ridgeSupport_2 290 7506 7507 7521 7523 7532 7537 7538 7543 7916 7917 7918 7919 7920 7921 8043 8051 8058
cert_ridgeSupport_code_2 290
cert_ridgeSupport_rest 290 000 0
cert_ridgeSupport_rest 290 001 416
cert_ridgeSupport_rest 290 002 832
cert_ridgeSupport_rest 290 003 1248
cert_ridgeSupport_rest 290 004 1664
cert_ridgeSupport_rest 290 005 2080
cert_ridgeSupport_rest 290 006 2496
cert_ridgeSupport_rest 290 007 2912
cert_ridgeSupport_rest 290 008 3328
cert_ridgeSupport_rest 290 009 3744
cert_ridgeSupport_rest 290 010 3965
cert_ridgeSupport_suffix_2 290 010
cert_ridgeSupport_suffix 290 009 010
cert_ridgeSupport_suffix 290 008 009
cert_ridgeSupport_suffix 290 007 008
cert_ridgeSupport_suffix 290 006 007
cert_ridgeSupport_suffix 290 005 006
cert_ridgeSupport_suffix 290 004 005
cert_ridgeSupport_suffix 290 003 004
cert_ridgeSupport_suffix 290 002 003
cert_ridgeSupport_suffix 290 001 002
cert_ridgeSupport_suffix 290 000 001
cert_ridgeSupport_source 290 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
