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
def ridgeSupport546_000 : List Nat := [40,49,51,52,530,639,642,643,646,649,663,666,667,670,673,675,678,679,682,685,792,793,795,796,799,800,801,803,804,806,811,812]
def ridgeSupport546_001 : List Nat := [813,814,816,817,820,821,822,824,825,827,832,833,834,835,837,838,841,842,843,845,846,848,853,854,3744,3745,3750,3751,3756,3757,3758,3759]
def ridgeSupport546_002 : List Nat := [3760,3761,3762,3763,3768,3769,3774,3775,3780,3781,3782,3783,3784,3785,3786,3787,3806,3807,3808,3809,3810,3811,3830,3831,3832,3833,3834,3835,3854,3855,3856,3857]
def ridgeSupport546_003 : List Nat := [3858,3859,3878,3879,3880,3881,3882,3883,3902,3903,3904,3905,3906,3907,3926,3927,3928,3929,3930,3931,3932,3934,3938,3940,3944,3946,3950,3951,3952,3953,3954,3955]
def ridgeSupport546_004 : List Nat := [4302,4303,4320,4321,4338,4339,4340,4342,4346,4348,4356,4357,4374,4375,4392,4393,4410,4411,4412,4414,4418,4420,4428,4429,4446,4447,4464,4465,4482,4483,4484,4486]
def ridgeSupport546_005 : List Nat := [4490,4492,4500,4501,4781,4783,4786,4788,4793,4795,4813,4815,4818,4820,4825,4827,4829,4831,4834,4836,4841,4843,6516,6517,6520,6521,6522,6523,6528,6529,6532,6533]
def ridgeSupport546_006 : List Nat := [6534,6535,6554,6555,6556,6557,6558,6559,6578,6579,6580,6581,6582,6583,6584,6586,6590,6592,6596,6598,6602,6603,6604,6605,6606,6607,6608,6610,6614,6616,6620,6622]
def ridgeSupport546_007 : List Nat := [6626,6627,6628,6629,6630,6631,6633,6634,6636,6637,6639,6640,6840,6841,6842,6844,6848,6850,6858,6859,6867,6869,6876,6877,6878,6880,6894,6895,6896,6898,6902,6904]
def ridgeSupport546_008 : List Nat := [6912,6913,6921,6923,6930,6931,6932,6934,6948,6949,6950,6952,6956,6958,6966,6967,6975,6977,6984,6985,6986,6988,7133,7134,7141,7142,7145,7146,7500,7501,7504,7505]
cert_ridgeSupport_2 546 7506 7507 7527 7529 7533 7535 7539 7541 7922 7923 7924 7925 7926 7927 8047 8055 8059
cert_ridgeSupport_code_2 546
cert_ridgeSupport_rest 546 000 0
cert_ridgeSupport_rest 546 001 416
cert_ridgeSupport_rest 546 002 832
cert_ridgeSupport_rest 546 003 1248
cert_ridgeSupport_rest 546 004 1664
cert_ridgeSupport_rest 546 005 2080
cert_ridgeSupport_rest 546 006 2496
cert_ridgeSupport_rest 546 007 2912
cert_ridgeSupport_rest 546 008 3328
cert_ridgeSupport_rest 546 009 3744
cert_ridgeSupport_rest 546 010 3965
cert_ridgeSupport_suffix_2 546 010
cert_ridgeSupport_suffix 546 009 010
cert_ridgeSupport_suffix 546 008 009
cert_ridgeSupport_suffix 546 007 008
cert_ridgeSupport_suffix 546 006 007
cert_ridgeSupport_suffix 546 005 006
cert_ridgeSupport_suffix 546 004 005
cert_ridgeSupport_suffix 546 003 004
cert_ridgeSupport_suffix 546 002 003
cert_ridgeSupport_suffix 546 001 002
cert_ridgeSupport_suffix 546 000 001
cert_ridgeSupport_source 546 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
