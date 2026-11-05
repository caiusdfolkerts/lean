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
def ridgeSupport162_000 : List Nat := [38,47,50,51,528,615,618,619,622,625,652,653,656,657,662,664,665,668,669,674,771,773,774,776,777,779,781,782,784,785,788,789]
def ridgeSupport162_001 : List Nat := [792,794,795,797,798,800,802,803,805,806,809,810,835,836,838,839,840,841,843,844,846,847,849,850,3740,3741,3746,3747,3748,3749,3750,3751]
def ridgeSupport162_002 : List Nat := [3754,3755,3760,3761,3764,3765,3770,3771,3772,3773,3774,3775,3778,3779,3784,3785,3794,3795,3796,3797,3798,3799,3818,3819,3820,3821,3822,3823,3842,3843,3844,3845]
def ridgeSupport162_003 : List Nat := [3846,3847,3866,3867,3868,3869,3870,3871,3890,3891,3892,3893,3894,3895,3914,3915,3916,3917,3918,3919,3935,3937,3938,3939,3940,3941,3942,3943,3945,3948,3951,3954]
def ridgeSupport162_004 : List Nat := [4228,4229,4246,4247,4264,4265,4269,4272,4275,4278,4282,4283,4300,4301,4318,4319,4336,4337,4341,4344,4347,4350,4354,4355,4442,4443,4460,4461,4478,4479,4487,4489]
def ridgeSupport162_005 : List Nat := [4493,4495,4496,4497,4749,4751,4754,4756,4761,4763,4796,4798,4803,4805,4808,4810,4812,4814,4819,4821,4824,4826,6512,6513,6518,6519,6520,6521,6524,6525,6530,6531]
def ridgeSupport162_006 : List Nat := [6532,6533,6542,6543,6544,6545,6546,6547,6566,6567,6568,6569,6570,6571,6587,6589,6590,6591,6592,6593,6594,6595,6597,6600,6603,6606,6611,6613,6614,6615,6616,6617]
def ridgeSupport162_007 : List Nat := [6618,6619,6621,6624,6627,6630,6632,6633,6638,6640,6641,6643,6784,6785,6789,6792,6795,6798,6802,6803,6812,6817,6820,6821,6825,6828,6838,6839,6843,6846,6849,6852]
def ridgeSupport162_008 : List Nat := [6856,6857,6866,6871,6874,6875,6879,6882,6944,6945,6953,6955,6959,6961,6962,6963,6976,6978,6980,6981,6989,6991,7125,7126,7136,7139,7140,7143,7496,7497,7502,7503]
def ridgeSupport162_009 : List Nat := [7504,7505,7520,7525,7526,7531,7540,7542,7910,7911,7912,7913,7914,7915,8039,8050,8054]
def ridgeSupport162_code : Nat := 0x1f76fb97d9fdd7eeaf74fba3dcfee6ebb75d3ad7d66eb2f583aa3d50ea7f53ba93d48df3ef937c7be0deb6f5769fb4dda2ed13685b40d99eccb663b2fd95eca7643b20d716b7f5b7adad6beb4b593ac8d626b0757dabbd5beadb559aa9d52ea93543a9cd49ea4b51da8bd446a17503a80cf9e7c73e19eecf4e7a33cd9e3cf067773b79dacece7633af9d6ceae74f39d9cbce467173879c2ce0e70337f9becdee6ef3579aacd4e6a334f9a6cc9e64b323990cc7e63b30b984cc1e60b2fb97ccbce5e32ef976cb8e5c25b52d896acb4e59d2cc9654b2258b2c395f4af253729994a4a4a51f28d8c8c64231f18d8c4c61e2ff17e8b6c5b22b715a881c40a1fd0fb87c43d61e30f086fc37a19b0cc85dc2ea16d0b385842b61530a884bc25a10b0847b93dbded8f697b3bd99ecaf647b1bd89ec2f5f7a7bd39e9af4c7a5bd29e6ef3679abcd1e66f3278fbc79e3af1c78dbc69e0ef06782bc11e06f02777bbb9ddaeec775bba9daeed676abb51da6ed2764bb21d86ec275fbaf9d7aebc75dbae9d6aeb4758bac1d56eaa753ba99d4aea4751ba89d3ae9c1a90d4469e34e1a60d2c6923481a38d186883431950ca464c3251918c8864031e18e8c6c63431818a8c506223101870c346163091840c1860a3031510a7453829914c0a585222901468a304e226e13589a84ce21001980c805e026
def ridgeSupport162_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport162_code
def ridgeSupport162_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport162_code
def ridgeSupport162_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport162_code
def ridgeSupport162_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport162_code
def ridgeSupport162_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport162_code
def ridgeSupport162_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport162_code
def ridgeSupport162_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport162_code
def ridgeSupport162_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport162_code
def ridgeSupport162_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport162_code
def ridgeSupport162_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport162_code
def ridgeSupport162_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport162_code
def ridgeSupport162_suffix_010 : List Nat := []
def ridgeSupport162_suffix_009 : List Nat := ridgeSupport162_009 ++ ridgeSupport162_suffix_010
def ridgeSupport162_suffix_008 : List Nat := ridgeSupport162_008 ++ ridgeSupport162_suffix_009
def ridgeSupport162_suffix_007 : List Nat := ridgeSupport162_007 ++ ridgeSupport162_suffix_008
def ridgeSupport162_suffix_006 : List Nat := ridgeSupport162_006 ++ ridgeSupport162_suffix_007
def ridgeSupport162_suffix_005 : List Nat := ridgeSupport162_005 ++ ridgeSupport162_suffix_006
def ridgeSupport162_suffix_004 : List Nat := ridgeSupport162_004 ++ ridgeSupport162_suffix_005
def ridgeSupport162_suffix_003 : List Nat := ridgeSupport162_003 ++ ridgeSupport162_suffix_004
def ridgeSupport162_suffix_002 : List Nat := ridgeSupport162_002 ++ ridgeSupport162_suffix_003
def ridgeSupport162_suffix_001 : List Nat := ridgeSupport162_001 ++ ridgeSupport162_suffix_002
def ridgeSupport162_suffix_000 : List Nat := ridgeSupport162_000 ++ ridgeSupport162_suffix_001
theorem ridgeSupport162_source : candidateSupports 162 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport162_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
