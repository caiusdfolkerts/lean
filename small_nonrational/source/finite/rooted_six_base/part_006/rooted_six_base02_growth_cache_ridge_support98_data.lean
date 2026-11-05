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
def ridgeSupport98_000 : List Nat := [37,47,48,49,527,616,617,620,621,626,628,629,632,633,638,640,641,644,645,650,772,773,775,776,777,778,780,781,783,784,786,787]
def ridgeSupport98_001 : List Nat := [793,794,796,797,798,799,801,802,804,805,807,808,814,815,817,818,819,820,822,823,825,826,828,829,3740,3741,3742,3743,3744,3745,3746,3747]
def ridgeSupport98_002 : List Nat := [3752,3753,3758,3759,3764,3765,3766,3767,3768,3769,3770,3771,3776,3777,3782,3783,3788,3789,3790,3791,3792,3793,3812,3813,3814,3815,3816,3817,3836,3837,3838,3839]
def ridgeSupport98_003 : List Nat := [3840,3841,3860,3861,3862,3863,3864,3865,3884,3885,3886,3887,3888,3889,3908,3909,3910,3911,3912,3913,3932,3933,3934,3935,3936,3937,3941,3943,3947,3949,3953,3955]
def ridgeSupport98_004 : List Nat := [4226,4227,4244,4245,4262,4263,4271,4273,4277,4279,4280,4281,4298,4299,4316,4317,4334,4335,4343,4345,4349,4351,4352,4353,4370,4371,4388,4389,4406,4407,4415,4417]
def ridgeSupport98_005 : List Nat := [4421,4423,4424,4425,4748,4750,4755,4757,4760,4762,4764,4766,4771,4773,4776,4778,4780,4782,4787,4789,4792,4794,6512,6513,6514,6515,6516,6517,6524,6525,6526,6527]
def ridgeSupport98_006 : List Nat := [6528,6529,6536,6537,6538,6539,6540,6541,6560,6561,6562,6563,6564,6565,6584,6585,6586,6587,6588,6589,6593,6595,6599,6601,6605,6607,6608,6609,6610,6611,6612,6613]
def ridgeSupport98_007 : List Nat := [6617,6619,6623,6625,6629,6631,6635,6636,6638,6639,6641,6642,6782,6783,6791,6793,6797,6799,6800,6801,6814,6816,6818,6819,6827,6829,6836,6837,6845,6847,6851,6853]
def ridgeSupport98_008 : List Nat := [6854,6855,6868,6870,6872,6873,6881,6883,6890,6891,6899,6901,6905,6907,6908,6909,6922,6924,6926,6927,6935,6937,7124,7127,7128,7131,7132,7135,7496,7497,7498,7499]
def ridgeSupport98_009 : List Nat := [7500,7501,7522,7524,7528,7530,7534,7536,7904,7905,7906,7907,7908,7909,8038,8042,8046]
def ridgeSupport98_code : Nat := 0x1f6efb57d9bdcbee4f71fb8bdc3ee0eb875bbad5d68eb2758ba9bd4cea5f52ba93d48defef737b7bd8debef53633b17d87ec3b619b0ad7eebf35f7af9d7aebcf5d7aead71eb875b3ad8d6b6b5358fac6d62eb0f57fabdd5aead355baabd51ea8b541a9ed48ea4351fa8dd44ea1f4ffa7ecf967c73df9eecf667af3cf9e5cf0e77f3b79d9ceae7533a79d2ce8e74339f9cdce4e71f3879c1cdee6f33779bacdce6e334b9a4cd1e68b3439a0cc6e63331798acc4e623303980cbfe5fb2fb97ccbae5d32e7972cb8e5c25752b895acace55d2ac9554aa254b2a394f4a7253529894aca4e51d28c8a4c52228f1458a0c4fe26f136892c492227112880c4021ff0fd87cc3de1df0ee86ec3721970ca85cc2e216f0b5858c2be14f0a684ac2521070827b9bdc5edaf6b7b3bd95ec2f607afbd79ebaf5c7a4bd21e8ef467a2bd11e62f30797bcb9e5af2c78cbc61e2ef1678abc51e02f0077fbbf9dfaefc774bba1dceee6772bb91da2ed0767bb39d9aecc763bb19d82ec075dbae9d72eb875bbad9d6aeb4757bab9d52ea8751ba89d42ea074fba79d3ae9c19e8cf067433919b8cd86683331990cc465e32e1940c9c64a3241910c8463e31e18e8c706343191898c4862030f1868c306143091840c1c60a3041450a1450828114009f84f227813a89d04e426d13609a44d020f01880c005e025
def ridgeSupport98_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport98_code
def ridgeSupport98_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport98_code
def ridgeSupport98_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport98_code
def ridgeSupport98_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport98_code
def ridgeSupport98_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport98_code
def ridgeSupport98_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport98_code
def ridgeSupport98_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport98_code
def ridgeSupport98_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport98_code
def ridgeSupport98_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport98_code
def ridgeSupport98_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport98_code
def ridgeSupport98_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport98_code
def ridgeSupport98_suffix_010 : List Nat := []
def ridgeSupport98_suffix_009 : List Nat := ridgeSupport98_009 ++ ridgeSupport98_suffix_010
def ridgeSupport98_suffix_008 : List Nat := ridgeSupport98_008 ++ ridgeSupport98_suffix_009
def ridgeSupport98_suffix_007 : List Nat := ridgeSupport98_007 ++ ridgeSupport98_suffix_008
def ridgeSupport98_suffix_006 : List Nat := ridgeSupport98_006 ++ ridgeSupport98_suffix_007
def ridgeSupport98_suffix_005 : List Nat := ridgeSupport98_005 ++ ridgeSupport98_suffix_006
def ridgeSupport98_suffix_004 : List Nat := ridgeSupport98_004 ++ ridgeSupport98_suffix_005
def ridgeSupport98_suffix_003 : List Nat := ridgeSupport98_003 ++ ridgeSupport98_suffix_004
def ridgeSupport98_suffix_002 : List Nat := ridgeSupport98_002 ++ ridgeSupport98_suffix_003
def ridgeSupport98_suffix_001 : List Nat := ridgeSupport98_001 ++ ridgeSupport98_suffix_002
def ridgeSupport98_suffix_000 : List Nat := ridgeSupport98_000 ++ ridgeSupport98_suffix_001
theorem ridgeSupport98_source : candidateSupports 98 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport98_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
