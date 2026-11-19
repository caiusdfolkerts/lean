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
def ridgeSupport98_000 : List Nat := [37,47,48,49,527,616,617,620,621,626,628,629,632,633,638,640,641,644,645,650,772,773,775,776,777,778,780,781,783,784,786,787]
def ridgeSupport98_001 : List Nat := [793,794,796,797,798,799,801,802,804,805,807,808,814,815,817,818,819,820,822,823,825,826,828,829,3740,3741,3742,3743,3744,3745,3746,3747]
def ridgeSupport98_002 : List Nat := [3752,3753,3758,3759,3764,3765,3766,3767,3768,3769,3770,3771,3776,3777,3782,3783,3788,3789,3790,3791,3792,3793,3812,3813,3814,3815,3816,3817,3836,3837,3838,3839]
def ridgeSupport98_003 : List Nat := [3840,3841,3860,3861,3862,3863,3864,3865,3884,3885,3886,3887,3888,3889,3908,3909,3910,3911,3912,3913,3932,3933,3934,3935,3936,3937,3941,3943,3947,3949,3953,3955]
def ridgeSupport98_004 : List Nat := [4226,4227,4244,4245,4262,4263,4271,4273,4277,4279,4280,4281,4298,4299,4316,4317,4334,4335,4343,4345,4349,4351,4352,4353,4370,4371,4388,4389,4406,4407,4415,4417]
def ridgeSupport98_005 : List Nat := [4421,4423,4424,4425,4748,4750,4755,4757,4760,4762,4764,4766,4771,4773,4776,4778,4780,4782,4787,4789,4792,4794,6512,6513,6514,6515,6516,6517,6524,6525,6526,6527]
def ridgeSupport98_006 : List Nat := [6528,6529,6536,6537,6538,6539,6540,6541,6560,6561,6562,6563,6564,6565,6584,6585,6586,6587,6588,6589,6593,6595,6599,6601,6605,6607,6608,6609,6610,6611,6612,6613]
def ridgeSupport98_007 : List Nat := [6617,6619,6623,6625,6629,6631,6635,6636,6638,6639,6641,6642,6782,6783,6791,6793,6797,6799,6800,6801,6814,6816,6818,6819,6827,6829,6836,6837,6845,6847,6851,6853]
def ridgeSupport98_008 : List Nat := [6854,6855,6868,6870,6872,6873,6881,6883,6890,6891,6899,6901,6905,6907,6908,6909,6922,6924,6926,6927,6935,6937,7124,7127,7128,7131,7132,7135,7496,7497,7498,7499]
cert_ridgeSupport_2 98 7500 7501 7522 7524 7528 7530 7534 7536 7904 7905 7906 7907 7908 7909 8038 8042 8046
cert_ridgeSupport_code_2 98
cert_ridgeSupport_rest 98 000 0
cert_ridgeSupport_rest 98 001 416
cert_ridgeSupport_rest 98 002 832
cert_ridgeSupport_rest 98 003 1248
cert_ridgeSupport_rest 98 004 1664
cert_ridgeSupport_rest 98 005 2080
cert_ridgeSupport_rest 98 006 2496
cert_ridgeSupport_rest 98 007 2912
cert_ridgeSupport_rest 98 008 3328
cert_ridgeSupport_rest 98 009 3744
cert_ridgeSupport_rest 98 010 3965
cert_ridgeSupport_suffix_2 98 010
cert_ridgeSupport_suffix 98 009 010
cert_ridgeSupport_suffix 98 008 009
cert_ridgeSupport_suffix 98 007 008
cert_ridgeSupport_suffix 98 006 007
cert_ridgeSupport_suffix 98 005 006
cert_ridgeSupport_suffix 98 004 005
cert_ridgeSupport_suffix 98 003 004
cert_ridgeSupport_suffix 98 002 003
cert_ridgeSupport_suffix 98 001 002
cert_ridgeSupport_suffix 98 000 001
cert_ridgeSupport_source 98 13 305
end Papers.RationalityTen.RootedCaches.RootedSixBase02
