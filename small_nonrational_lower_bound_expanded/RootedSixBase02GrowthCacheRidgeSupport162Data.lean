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
def ridgeSupport162_000 : List Nat := [38,47,50,51,528,615,618,619,622,625,652,653,656,657,662,664,665,668,669,674,771,773,774,776,777,779,781,782,784,785,788,789]
def ridgeSupport162_001 : List Nat := [792,794,795,797,798,800,802,803,805,806,809,810,835,836,838,839,840,841,843,844,846,847,849,850,3740,3741,3746,3747,3748,3749,3750,3751]
def ridgeSupport162_002 : List Nat := [3754,3755,3760,3761,3764,3765,3770,3771,3772,3773,3774,3775,3778,3779,3784,3785,3794,3795,3796,3797,3798,3799,3818,3819,3820,3821,3822,3823,3842,3843,3844,3845]
def ridgeSupport162_003 : List Nat := [3846,3847,3866,3867,3868,3869,3870,3871,3890,3891,3892,3893,3894,3895,3914,3915,3916,3917,3918,3919,3935,3937,3938,3939,3940,3941,3942,3943,3945,3948,3951,3954]
def ridgeSupport162_004 : List Nat := [4228,4229,4246,4247,4264,4265,4269,4272,4275,4278,4282,4283,4300,4301,4318,4319,4336,4337,4341,4344,4347,4350,4354,4355,4442,4443,4460,4461,4478,4479,4487,4489]
def ridgeSupport162_005 : List Nat := [4493,4495,4496,4497,4749,4751,4754,4756,4761,4763,4796,4798,4803,4805,4808,4810,4812,4814,4819,4821,4824,4826,6512,6513,6518,6519,6520,6521,6524,6525,6530,6531]
def ridgeSupport162_006 : List Nat := [6532,6533,6542,6543,6544,6545,6546,6547,6566,6567,6568,6569,6570,6571,6587,6589,6590,6591,6592,6593,6594,6595,6597,6600,6603,6606,6611,6613,6614,6615,6616,6617]
def ridgeSupport162_007 : List Nat := [6618,6619,6621,6624,6627,6630,6632,6633,6638,6640,6641,6643,6784,6785,6789,6792,6795,6798,6802,6803,6812,6817,6820,6821,6825,6828,6838,6839,6843,6846,6849,6852]
def ridgeSupport162_008 : List Nat := [6856,6857,6866,6871,6874,6875,6879,6882,6944,6945,6953,6955,6959,6961,6962,6963,6976,6978,6980,6981,6989,6991,7125,7126,7136,7139,7140,7143,7496,7497,7502,7503]
cert_ridgeSupport_2 162 7504 7505 7520 7525 7526 7531 7540 7542 7910 7911 7912 7913 7914 7915 8039 8050 8054
cert_ridgeSupport_code_2 162
cert_ridgeSupport_rest 162 000 0
cert_ridgeSupport_rest 162 001 416
cert_ridgeSupport_rest 162 002 832
cert_ridgeSupport_rest 162 003 1248
cert_ridgeSupport_rest 162 004 1664
cert_ridgeSupport_rest 162 005 2080
cert_ridgeSupport_rest 162 006 2496
cert_ridgeSupport_rest 162 007 2912
cert_ridgeSupport_rest 162 008 3328
cert_ridgeSupport_rest 162 009 3744
cert_ridgeSupport_rest 162 010 3965
cert_ridgeSupport_suffix_2 162 010
cert_ridgeSupport_suffix 162 009 010
cert_ridgeSupport_suffix 162 008 009
cert_ridgeSupport_suffix 162 007 008
cert_ridgeSupport_suffix 162 006 007
cert_ridgeSupport_suffix 162 005 006
cert_ridgeSupport_suffix 162 004 005
cert_ridgeSupport_suffix 162 003 004
cert_ridgeSupport_suffix 162 002 003
cert_ridgeSupport_suffix 162 001 002
cert_ridgeSupport_suffix 162 000 001
cert_ridgeSupport_source 162 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
