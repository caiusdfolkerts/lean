module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport42_000 : List Nat := [0,37,38,39,40,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641]
def ridgeSupport42_001 : List Nat := [642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673]
def ridgeSupport42_002 : List Nat := [674,675,676,677,678,679,680,681,682,683,684,685,686,4220,4221,4222,4223,4224,4225,4226,4227,4228,4229,4230,4231,4232,4233,4234,4235,4236,4237,4238]
def ridgeSupport42_003 : List Nat := [4239,4240,4241,4242,4243,4244,4245,4246,4247,4248,4249,4250,4251,4252,4253,4254,4255,4256,4257,4258,4259,4260,4261,4262,4263,4264,4265,4266,4267,4268,4269,4270]
def ridgeSupport42_004 : List Nat := [4271,4272,4273,4274,4275,4276,4277,4278,4279,4280,4281,4282,4283,4284,4285,4286,4287,4288,4289,4290,4291,4292,4293,4294,4295,4296,4297,4298,4299,4300,4301,4302]
def ridgeSupport42_005 : List Nat := [4303,4304,4305,4306,4307,4308,4309,4310,4311,4312,4313,4314,4315,4316,4317,4318,4319,4320,4321,4322,4323,4324,4325,4326,4327,4328,4329,4330,4331,4332,4333,4334]
def ridgeSupport42_006 : List Nat := [4335,4336,4337,4338,4339,4340,4341,4342,4343,4344,4345,4346,4347,4348,4349,4350,4351,4352,4353,4354,4355,4356,4357,4358,4359,4360,4361,4362,4363,4364,4365,4366]
def ridgeSupport42_007 : List Nat := [4367,4368,4369,4370,4371,4372,4373,4374,4375,4376,4377,4378,4379,4380,4381,4382,4383,4384,4385,4386,4387,4388,4389,4390,4391,4392,4393,4394,4395,4396,4397,4398]
def ridgeSupport42_008 : List Nat := [4399,4400,4401,4402,4403,4404,4405,4406,4407,4408,4409,4410,4411,4412,4413,4414,4415,4416,4417,4418,4419,4420,4421,4422,4423,4424,4425,4426,4427,4428,4429,4430]
def ridgeSupport42_009 : List Nat := [4431,4432,4433,4434,4435,4436,4437,4438,4439,4440,4441,4442,4443,4444,4445,4446,4447,4448,4449,4450,4451,4452,4453,4454,4455,4456,4457,4458,4459,4460,4461,4462]
def ridgeSupport42_010 : List Nat := [4463,4464,4465,4466,4467,4468,4469,4470,4471,4472,4473,4474,4475,4476,4477,4478,4479,4480,4481,4482,4483,4484,4485,4486,4487,4488,4489,4490,4491,4492,4493,4494]
def ridgeSupport42_011 : List Nat := [4495,4496,4497,4498,4499,4500,4501,4502,4503,4504,4505,4506,4507,5288,5289,5290,5291,5292,5293,5294,5295,5296,5297,5298,5299,5300,5301,5302,5303,5304,5305,5306]
def ridgeSupport42_012 : List Nat := [5307,5308,5309,5310,5311,5744,5745,5746,5747,5748,5749,5750,5751,5752,5753,5754,5755,5756,5757,5758,5759,5760,5761,5762,5763,5764,5765,5766,5767,6428,6429,6430]
def ridgeSupport42_013 : List Nat := [6431,6432,6433,6434,6435,6436,6437,6438,6439,6440,6441,6442,6443,6444,6445,6446,6447,6448,6449,6450,6451,6452,6453,6454,6455,6456,6457,6458,6459,6460,6461,6462]
def ridgeSupport42_014 : List Nat := [6463,6464,6465,6466,6467,6468,6469,6470,6471,6472,6473,6474,6475,6476,6477,6478,6479,6480,6481,6482,6483,6484,6485,6486,6487,6488,6489,6490,6491,6492,6493,6494]
def ridgeSupport42_015 : List Nat := [6495,6496,6497,6498,6499]
def ridgeSupport42_code : Nat := 0x1963cb165872c195fcaf65772b995bcad65672b1957cab65572a9953ca965472a194fca7653729994bca56527291947ca36517289943ca1650728193fc9f64f727993bc9d64e7271937c9b64d7269933c9964c726192fc9764b725992bc9564a7251927c936497249923c91648724191fc8f6477239687b435a16d09683b415a06d0167fb3f59f6cf967bb3d59e6cf1677b3b59d6ce9673b3959c6ce14bfa5f52f69794bba5d52e69714b7a5b52d69694b3a5952c69614afa5752b69594aba5552a695119b8cd46663311978cb46563291938c9464632118f8c7463631918b8c546263111878c346163091838c1460630117f8bf45f62f917b8bd45e62f11778bb45d62e91738b945c62e116f8b745b62d916b8b545a62d11678b345962c91638b145862c115f8af45762b915b8ad45662b11578ab45562a91538a945462a114f8a7453629914b8a545262911478a345162891438a1450628113f89f44f627913b89d44e627113789b44d626913389944c626112f89744b625912b89544a62511278934496249123891448624111f88f447623911b88d446623111788b4456229113889444622110f887443621910b8854426211107883441620910388144062010ff87f43f61f90fb87d43e61f10f787b43d61e90f387943c61e10ef87743b61d90eb87543a61d10e787343961c90e387143861c10df86f43761b90db86d43661b10d786b43561a90d386943461a10cf86743361990cb86543261910c786343161890c386143061810bf85f42f61790bb85d42e61710b785b42d61690b385942c61610af85742b61590ab85542a61510a785342961490a3851428614109f84f427613909b84d426613109784b4256129093849424612108f847423611908b84542261110878434216109083841420610107f83f41f60f82ae1568ab05562aa1548aa054e2a61528a905462a21508a8053e29e14e8a7053629a14c8a6052e29614a8a505262921488a4051e28e1468a3051628a1448a2050e2861428a105062821408a004fe27e13e89f04f627a13c89e04ee27613a89d04e627213889c04de26e13689b04d626a13489a04ce028013809804a000
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
def ridgeSupport42_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport42_code
def ridgeSupport42_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport42_code
def ridgeSupport42_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport42_code
def ridgeSupport42_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport42_code
def ridgeSupport42_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport42_code
def ridgeSupport42_rest_016 : Nat := PackedRawNatGrowth.drop 6305 ridgeSupport42_code
def ridgeSupport42_suffix_016 : List Nat := []
def ridgeSupport42_suffix_015 : List Nat := ridgeSupport42_015 ++ ridgeSupport42_suffix_016
def ridgeSupport42_suffix_014 : List Nat := ridgeSupport42_014 ++ ridgeSupport42_suffix_015
def ridgeSupport42_suffix_013 : List Nat := ridgeSupport42_013 ++ ridgeSupport42_suffix_014
def ridgeSupport42_suffix_012 : List Nat := ridgeSupport42_012 ++ ridgeSupport42_suffix_013
def ridgeSupport42_suffix_011 : List Nat := ridgeSupport42_011 ++ ridgeSupport42_suffix_012
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
    (PackedRawNatGrowth.readList 13 485 ridgeSupport42_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
