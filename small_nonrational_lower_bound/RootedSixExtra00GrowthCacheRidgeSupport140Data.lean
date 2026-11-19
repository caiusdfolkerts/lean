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
def ridgeSupport140_000 : List Nat := [16,66,69,72,73,359,360,362,367,369,394,397,399,402,404,406,409,411,414,416,1044,1046,1049,1050,1052,1081,1083,1084,1087,1089,1093,1095]
def ridgeSupport140_001 : List Nat := [1096,1099,1101,1116,1118,1119,1121,1122,1124,1126,1127,1129,1130,1133,1134,1137,1139,1140,1142,1143,1145,1147,1148,1150,1151,1154,1155,1180,1181,1183,1184,1185]
def ridgeSupport140_002 : List Nat := [1186,1188,1189,1191,1192,1194,1195,3640,3641,3646,3647,3648,3649,3650,3651,3654,3655,3660,3661,3664,3665,3670,3671,3672,3673,3674,3675,3678,3679,3684,3685,3694]
def ridgeSupport140_003 : List Nat := [3695,3696,3697,3698,3699,3718,3719,3720,3721,3722,3723,3742,3743,3744,3745,3746,3747,3766,3767,3768,3769,3770,3771,3790,3791,3792,3793,3794,3795,3814,3815,3816]
def ridgeSupport140_004 : List Nat := [3817,3818,3819,3835,3837,3838,3839,3840,3841,3842,3843,3845,3848,3851,3854,3900,3901,3912,3913,3917,3920,3923,3926,3936,3937,3948,3949,3972,3973,3984,3985,3989]
def ridgeSupport140_005 : List Nat := [3992,3995,3998,4008,4009,4020,4021,4114,4115,4126,4127,4135,4137,4141,4143,4150,4151,4162,4163,5946,5947,5958,5959,5982,5983,5994,5995,6005,6008,6011,6014,6018]
def ridgeSupport140_006 : List Nat := [6019,6030,6031,6054,6055,6066,6067,6077,6080,6083,6086,6160,6161,6172,6173,6196,6197,6208,6209,6223,6225,6229,6231,7282,7283,7284,7285,7286,7287,8062,8063,8064]
def ridgeSupport140_007 : List Nat := [8065,8066,8067,8083,8085,8086,8087,8088,8089,8095,8097,8098,8099,8100,8101,8106,8107,8112,8113,8124,8125,8130,8131,8158,8159,8164,8165,8567,8570,8573,8576,8585]
cert_ridgeSupport_7 140 008 8588 8591 8594 8623 8625 8629 8631
cert_ridgeSupport_code_3 140
cert_ridgeSupport_rest_2 140 000 0
cert_ridgeSupport_rest_2 140 001 448
cert_ridgeSupport_rest_2 140 002 896
cert_ridgeSupport_rest_2 140 003 1344
cert_ridgeSupport_rest_2 140 004 1792
cert_ridgeSupport_rest_2 140 005 2240
cert_ridgeSupport_rest_2 140 006 2688
cert_ridgeSupport_rest_2 140 007 3136
cert_ridgeSupport_rest_2 140 008 3584
cert_ridgeSupport_rest_2 140 009 3682
cert_ridgeSupport_suffix_4 140 009
cert_ridgeSupport_suffix_3 140 008 009
cert_ridgeSupport_suffix_3 140 007 008
cert_ridgeSupport_suffix_3 140 006 007
cert_ridgeSupport_suffix_3 140 005 006
cert_ridgeSupport_suffix_3 140 004 005
cert_ridgeSupport_suffix_3 140 003 004
cert_ridgeSupport_suffix_3 140 002 003
cert_ridgeSupport_suffix_3 140 001 002
cert_ridgeSupport_suffix_3 140 000 001
cert_ridgeSupport_source_3 140 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
