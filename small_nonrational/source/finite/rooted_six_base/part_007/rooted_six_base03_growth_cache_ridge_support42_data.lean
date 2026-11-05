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
def ridgeSupport42_code : Nat := 0x1421a10507e83d41da0e506e835419a0c505e82d415a0a504e825411a08503e81d40da06502e815205902480e40520190047fe3fd1fd8fe47ee3f51f98fc47de3ed1f58fa47ce3e51f18f847be3dcef977c3bdddecef577a3bcdde4ef17783bbdddceed7763baddd4ee97743b9ddccee57723b8ddc4ee17703b7ddbcedd76e3b6ddb4ed976c3b5ddaced576a3b4dda4ed17683b3dd9cecd7663b2dd94ec97643b1dd8cec57623b0dd84ec17603afdd7cebd75e3aedd74eb975c3addd6ceb575a3acdd64eb17583abdd5cead7563aadd54ea97543a9dd4cea57523a8dd44ea17503a7dd3ce9d74e3a6dd34e9974c3a5dd2ce9574a3a4dd24e917483a3dd1ce8d7463a2dd14e897443a1dd0ce857423a0dd04e8174039fdcfce7d73e39edcf4e7973c39ddcece7573a39cdce4e7173839bdcdce6d73639adcd4e69734399dccce65732398dcc4e61730397dcbce5d72e396dcb4e5972c395dcace5572a394dca4e51728393dc9ce4d726392dc94e49724391dc8ce45722390dc84e4172038fdc7ce3d71e38edc74e3971c38ddc6ce3571a38cdc64e3171838bdc5ce2d71638adc54e29714389dc4ce25712388dc4430017f8bf85fa2fc17d8be85f22f817b8bd85ea2f41798bc85e22f01778bb85da2ec1758ba85d22e81738b985ca2e41718b885c22e016f8b785ba2dc16d8b685b22d816b8b585aa2d41698b485a22d01678b3859a2cc1658b285922c81638b1858a2c41618b085822c015f8af857a2bc15d8ae857202c01580a8052000
def ridgeSupport42_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport42_code
def ridgeSupport42_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport42_code
def ridgeSupport42_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport42_code
def ridgeSupport42_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport42_code
def ridgeSupport42_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport42_code
def ridgeSupport42_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport42_code
def ridgeSupport42_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport42_code
def ridgeSupport42_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport42_code
def ridgeSupport42_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport42_code
def ridgeSupport42_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport42_code
def ridgeSupport42_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport42_code
def ridgeSupport42_rest_011 : Nat := PackedRawNatGrowth.drop 4433 ridgeSupport42_code
def ridgeSupport42_suffix_011 : List Nat := []
def ridgeSupport42_suffix_010 : List Nat := ridgeSupport42_010 ++ ridgeSupport42_suffix_011
def ridgeSupport42_suffix_009 : List Nat := ridgeSupport42_009 ++ ridgeSupport42_suffix_010
def ridgeSupport42_suffix_008 : List Nat := ridgeSupport42_008 ++ ridgeSupport42_suffix_009
def ridgeSupport42_suffix_007 : List Nat := ridgeSupport42_007 ++ ridgeSupport42_suffix_008
def ridgeSupport42_suffix_006 : List Nat := ridgeSupport42_006 ++ ridgeSupport42_suffix_007
def ridgeSupport42_suffix_005 : List Nat := ridgeSupport42_005 ++ ridgeSupport42_suffix_006
def ridgeSupport42_suffix_004 : List Nat := ridgeSupport42_004 ++ ridgeSupport42_suffix_005
def ridgeSupport42_suffix_003 : List Nat := ridgeSupport42_003 ++ ridgeSupport42_suffix_004
def ridgeSupport42_suffix_002 : List Nat := ridgeSupport42_002 ++ ridgeSupport42_suffix_003
def ridgeSupport42_suffix_001 : List Nat := ridgeSupport42_001 ++ ridgeSupport42_suffix_002
def ridgeSupport42_suffix_000 : List Nat := ridgeSupport42_000 ++ ridgeSupport42_suffix_001
theorem ridgeSupport42_source : candidateSupports 42 =
    (PackedRawNatGrowth.readList 13 341 ridgeSupport42_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
