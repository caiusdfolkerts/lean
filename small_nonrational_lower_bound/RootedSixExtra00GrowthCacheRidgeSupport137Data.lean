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
def ridgeSupport137_000 : List Nat := [6,16,25,28,29,202,205,206,209,212,239,240,243,244,249,251,252,255,256,261,358,361,362,365,368,395,396,399,400,405,407,408]
def ridgeSupport137_001 : List Nat := [411,412,417,514,516,517,519,520,522,524,525,527,528,531,532,535,537,538,540,541,543,545,546,548,549,552,553,578,579,581,582,583]
def ridgeSupport137_002 : List Nat := [584,586,587,589,590,592,593,2872,2873,2878,2879,2880,2881,2882,2883,2886,2887,2892,2893,2896,2897,2902,2903,2904,2905,2906,2907,2910,2911,2916,2917,2926]
def ridgeSupport137_003 : List Nat := [2927,2928,2929,2930,2931,2950,2951,2952,2953,2954,2955,2974,2975,2976,2977,2978,2979,2998,2999,3000,3001,3002,3003,3022,3023,3024,3025,3026,3027,3046,3047,3048]
def ridgeSupport137_004 : List Nat := [3049,3050,3051,3067,3069,3070,3071,3072,3073,3074,3075,3077,3080,3083,3086,3360,3361,3378,3379,3396,3397,3401,3404,3407,3410,3414,3415,3432,3433,3450,3451,3468]
def ridgeSupport137_005 : List Nat := [3469,3473,3476,3479,3482,3486,3487,3574,3575,3592,3593,3610,3611,3619,3621,3625,3627,3628,3629,3888,3889,3906,3907,3924,3925,3929,3932,3935,3938,3942,3943,3960]
def ridgeSupport137_006 : List Nat := [3961,3978,3979,3996,3997,4001,4004,4007,4010,4014,4015,4102,4103,4120,4121,4138,4139,4147,4149,4153,4155,4156,4157,7186,7187,7188,7189,7190,7191,7894,7895,7896]
def ridgeSupport137_007 : List Nat := [7897,7898,7899,7915,7917,7918,7919,7920,7921,7927,7929,7930,7931,7932,7933,7985,7988,7998,7999,8003,8006,8016,8017,8041,8043,8050,8051,8105,8108,8118,8119,8123]
cert_ridgeSupport_7 137 008 8126 8136 8137 8161 8163 8170 8171
cert_ridgeSupport_code_3 137
cert_ridgeSupport_rest_2 137 000 0
cert_ridgeSupport_rest_2 137 001 448
cert_ridgeSupport_rest_2 137 002 896
cert_ridgeSupport_rest_2 137 003 1344
cert_ridgeSupport_rest_2 137 004 1792
cert_ridgeSupport_rest_2 137 005 2240
cert_ridgeSupport_rest_2 137 006 2688
cert_ridgeSupport_rest_2 137 007 3136
cert_ridgeSupport_rest_2 137 008 3584
cert_ridgeSupport_rest_2 137 009 3682
cert_ridgeSupport_suffix_4 137 009
cert_ridgeSupport_suffix_3 137 008 009
cert_ridgeSupport_suffix_3 137 007 008
cert_ridgeSupport_suffix_3 137 006 007
cert_ridgeSupport_suffix_3 137 005 006
cert_ridgeSupport_suffix_3 137 004 005
cert_ridgeSupport_suffix_3 137 003 004
cert_ridgeSupport_suffix_3 137 002 003
cert_ridgeSupport_suffix_3 137 001 002
cert_ridgeSupport_suffix_3 137 000 001
cert_ridgeSupport_source_3 137 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
