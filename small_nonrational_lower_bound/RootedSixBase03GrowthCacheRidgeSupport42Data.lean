module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public meta import CertificateNumbers
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport42_000 : List Nat := [0,41,42,43,44,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723]
def ridgeSupport42_001 : List Nat := [724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755]
def ridgeSupport42_002 : List Nat := [756,757,758,759,760,761,762,763,764,765,766,767,768,3618,3619,3620,3621,3622,3623,3624,3625,3626,3627,3628,3629,3630,3631,3632,3633,3634,3635,3636]
def ridgeSupport42_003 : List Nat := [3637,3638,3639,3640,3641,3642,3643,3644,3645,3646,3647,3648,3649,3650,3651,3652,3653,3654,3655,3656,3657,3658,3659,3660,3661,3662,3663,3664,3665,3666,3667,3668]
def ridgeSupport42_004 : List Nat := [3669,3670,3671,3672,3673,3674,3675,3676,3677,3678,3679,3680,3681,3682,3683,3684,3685,3686,3687,3688,3689,3690,3691,3692,3693,3694,3695,3696,3697,3698,3699,3700]
def ridgeSupport42_005 : List Nat := [3701,3702,3703,3704,3705,3706,3707,3708,3709,3710,3711,3712,3713,3714,3715,3716,3717,3718,3719,3720,3721,3722,3723,3724,3725,3726,3727,3728,3729,3730,3731,3732]
def ridgeSupport42_006 : List Nat := [3733,3734,3735,3736,3737,3738,3739,3740,3741,3742,3743,3744,3745,3746,3747,3748,3749,3750,3751,3752,3753,3754,3755,3756,3757,3758,3759,3760,3761,3762,3763,3764]
def ridgeSupport42_007 : List Nat := [3765,3766,3767,3768,3769,3770,3771,3772,3773,3774,3775,3776,3777,3778,3779,3780,3781,3782,3783,3784,3785,3786,3787,3788,3789,3790,3791,3792,3793,3794,3795,3796]
def ridgeSupport42_008 : List Nat := [3797,3798,3799,3800,3801,3802,3803,3804,3805,3806,3807,3808,3809,3810,3811,3812,3813,3814,3815,3816,3817,3818,3819,3820,3821,3822,3823,3824,3825,3826,3827,3828]
def ridgeSupport42_009 : List Nat := [3829,3830,3831,3832,3833,4590,4591,4592,4593,4594,4595,4596,4597,4598,4599,4600,4601,4602,4603,4604,4605,4606,4607,4608,4609,4610,4611,4612,4613,5130,5131,5132]
def ridgeSupport42_010 : List Nat := [5133,5134,5135,5136,5137,5138,5139,5140,5141,5142,5143,5144,5145,5146,5147,5148,5149,5150,5151,5152,5153]
cert_ridgeSupport_code_2 42
cert_ridgeSupport_rest 42 000 0
cert_ridgeSupport_rest 42 001 416
cert_ridgeSupport_rest 42 002 832
cert_ridgeSupport_rest 42 003 1248
cert_ridgeSupport_rest 42 004 1664
cert_ridgeSupport_rest 42 005 2080
cert_ridgeSupport_rest 42 006 2496
cert_ridgeSupport_rest 42 007 2912
cert_ridgeSupport_rest 42 008 3328
cert_ridgeSupport_rest 42 009 3744
cert_ridgeSupport_rest 42 010 4160
cert_ridgeSupport_rest 42 011 4433
cert_ridgeSupport_suffix_2 42 011
cert_ridgeSupport_suffix 42 010 011
cert_ridgeSupport_suffix 42 009 010
cert_ridgeSupport_suffix 42 008 009
cert_ridgeSupport_suffix 42 007 008
cert_ridgeSupport_suffix 42 006 007
cert_ridgeSupport_suffix 42 005 006
cert_ridgeSupport_suffix 42 004 005
cert_ridgeSupport_suffix 42 003 004
cert_ridgeSupport_suffix 42 002 003
cert_ridgeSupport_suffix 42 001 002
cert_ridgeSupport_suffix 42 000 001
cert_ridgeSupport_source 42 13 341
end Papers.RationalityTen.RootedCaches.RootedSixBase03
