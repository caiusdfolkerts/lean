module
prelude
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
def ridgeSupport546_009 : List Nat := [7506,7507,7527,7529,7533,7535,7539,7541,7922,7923,7924,7925,7926,7927,8047,8055,8059]
def ridgeSupport546_code : Nat := 0x1f7bfbbfdbfdefef6f7afbd3de7ef2ebaf5cfadfd6deb4f59faa7d52ea8f543a9bd4cdf56fa77cdbe5def6f77699b4ada4ed23683b3fd9becdb65db2cd946c9b64bb24d8b6c53627b12d85ec27603b00d7c6bdb5e5af0d77ebbb5c1aded6eeb735abad3d65eb2b585ac0d5e6aeb573ab8cf867bf3db9eccf567a73cf9e6cf2e7933c79e2cef67733b19d6ce9674339f9cece6e7333979cace367133819becdd66e336f9b6cdae6d33679b2ccfe67b33b99cccde66b30f986cc2e613303980cbde5eb2f3978cbae5d25d72e99724b8a5bf2dd96dcb665a92d2967cb365772b995a4aca55f2ad8cac65231918a8c346123071828b8c5c22bf15e8a6c53228914289f44f227713a894c4a222f116882c4121f90fa87b43d21e70f2870c38219f0ce7b9bdc9ee2f707b7bdb9ed4f687b23d89ebcf5c7adbd69eb2f587abbd59e86f427a0bd01e7ef3e795bca9e52f28793bc99e26f12788bc41e1ef0e77dbbe9df2ef877bbbd9dc6ee2770bb81dbeede765bb29d92ec8763bb19d8aec475fbaf9d72eb8759bac9d62eb0757bab9d5aeac753ba99d42ea01ab0d546a034e1a68d2c6943491a30d146863421a08d0067633919c0cd866a3341988cc065c32d1960cac64c3241918c8464031f18e0c6c6323181568aa854e2a61518a8453c29b14d0a5c5122861418a084fe21201a00cc062028
def ridgeSupport546_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport546_code
def ridgeSupport546_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport546_code
def ridgeSupport546_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport546_code
def ridgeSupport546_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport546_code
def ridgeSupport546_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport546_code
def ridgeSupport546_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport546_code
def ridgeSupport546_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport546_code
def ridgeSupport546_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport546_code
def ridgeSupport546_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport546_code
def ridgeSupport546_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport546_code
def ridgeSupport546_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport546_code
def ridgeSupport546_suffix_010 : List Nat := []
def ridgeSupport546_suffix_009 : List Nat := ridgeSupport546_009 ++ ridgeSupport546_suffix_010
def ridgeSupport546_suffix_008 : List Nat := ridgeSupport546_008 ++ ridgeSupport546_suffix_009
def ridgeSupport546_suffix_007 : List Nat := ridgeSupport546_007 ++ ridgeSupport546_suffix_008
def ridgeSupport546_suffix_006 : List Nat := ridgeSupport546_006 ++ ridgeSupport546_suffix_007
def ridgeSupport546_suffix_005 : List Nat := ridgeSupport546_005 ++ ridgeSupport546_suffix_006
def ridgeSupport546_suffix_004 : List Nat := ridgeSupport546_004 ++ ridgeSupport546_suffix_005
def ridgeSupport546_suffix_003 : List Nat := ridgeSupport546_003 ++ ridgeSupport546_suffix_004
def ridgeSupport546_suffix_002 : List Nat := ridgeSupport546_002 ++ ridgeSupport546_suffix_003
def ridgeSupport546_suffix_001 : List Nat := ridgeSupport546_001 ++ ridgeSupport546_suffix_002
def ridgeSupport546_suffix_000 : List Nat := ridgeSupport546_000 ++ ridgeSupport546_suffix_001
theorem ridgeSupport546_source : candidateSupports 546 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport546_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
