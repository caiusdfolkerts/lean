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
def kindSupport8_000 : List Nat := [4398,4399,4400,4401,4402,4403,4404,4405,4406,4407,4408,4409,4410,4411,4412,4413,4414,4415,4416,4417,4418,4419,4420,4421,4422,4423,4424,4425,4426,4427,4428,4429]
def kindSupport8_001 : List Nat := [4430,4431,4432,4433,4434,4435,4436,4437,4438,4439,4440,4441,4442,4443,4444,4445,4446,4447,4448,4449,4450,4451,4452,4453,4454,4455,4456,4457,4458,4459,4460,4461]
def kindSupport8_002 : List Nat := [4462,4463,4464,4465,4466,4467,4468,4469,4470,4471,4472,4473,4474,4475,4476,4477,4478,4479,4480,4481,4482,4483,4484,4485,4486,4487,4488,4489,4490,4491,4492,4493]
def kindSupport8_003 : List Nat := [4494,4495,4496,4497,4498,4499,4500,4501,4502,4503,4504,4505,4506,4507,4508,4509,4510,4511,4512,4513,4514,4515,4516,4517,4518,4519,4520,4521,4522,4523,4524,4525]
def kindSupport8_004 : List Nat := [4526,4527,4528,4529,4530,4531,4532,4533,4534,4535,4536,4537,4538,4539,4540,4541,4542,4543,4544,4545,4546,4547,4548,4549,4550,4551,4552,4553,4554,4555,4556,4557]
def kindSupport8_005 : List Nat := [4558,4559,4560,4561,4562,4563,4564,4565,4566,4567,4568,4569,4570,4571,4572,4573,4574,4575,4576,4577,4578,4579,4580,4581,4582,4583,4584,4585,4586,4587,4588,4589]
def kindSupport8_006 : List Nat := [4590,4591,4592,4593,4594,4595,4596,4597,4598,4599,4600,4601,4602,4603,4604,4605,4606,4607,4608,4609,4610,4611,4612,4613,4614,4615,4616,4617,4618,4619,4620,4621]
def kindSupport8_007 : List Nat := [4622,4623,4624,4625,4626,4627,4628,4629,4630,4631,4632,4633,4634,4635,4636,4637,4638,4639,4640,4641,4642,4643,4644,4645,4646,4647,4648,4649,4650,4651,4652,4653]
def kindSupport8_008 : List Nat := [4654,4655,4656,4657,4658,4659,4660,4661,4662,4663,4664,4665,4666,4667,4668,4669,4670,4671,4672,4673]
def kindSupport8_code : Nat := 0x920c90247f23e91ec8f247723a91cc8e246f23691ac8d2467232918c8c245f22e916c8b245722a914c8a244f226912c892447222910c88243f21e90ec87243721a90cc86242f21690ac852427212908c84241f20e906c83241720a904c82240f206902c812407202900c8023ff1fe8fec7f23f71fa8fcc7e23ef1f68fac7d23e71f28f8c7c23df1ee8f6c7b23d71ea8f4c7a23cf1e68f2c7923c71e28f0c7823bf1de8eec7723b71da8ecc7623af1d68eac7523a71d28e8c74239f1ce8e6c7323971ca8e4c72238f1c68e2c7123871c28e0c70237f1be8dec6f23771ba8dcc6e236f1b68dac6d23671b28d8c6c235f1ae8d6c6b23571aa8d4c6a234f1a68d2c6923471a28d0c68233f19e8cec67233719a8ccc66232f1968cac6523271928c8c64231f18e8c6c63231718a8c4c62230f1868c2c6123071828c0c6022ff17e8bec5f22f717a8bcc5e22ef1768bac5d22e71728b8c5c22df16e8b6c5b22d716a8b4c5a22cf1668b2c5922c71628b0c5822bf15e8aec5722b715a8acc5622af1568aac5522a71528a8c54229f14e8a6c53229714a8a4c52228f1468a2c5122871428a0c50227f13e89ec4f227713a89cc4e226f13689ac4d2267132898c4c225f12e
def kindSupport8_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport8_code
def kindSupport8_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport8_code
def kindSupport8_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport8_code
def kindSupport8_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport8_code
def kindSupport8_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport8_code
def kindSupport8_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport8_code
def kindSupport8_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport8_code
def kindSupport8_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport8_code
def kindSupport8_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport8_code
def kindSupport8_rest_009 : Nat := PackedRawNatGrowth.drop 3588 kindSupport8_code
def kindSupport8_suffix_009 : List Nat := []
def kindSupport8_suffix_008 : List Nat := kindSupport8_008 ++ kindSupport8_suffix_009
def kindSupport8_suffix_007 : List Nat := kindSupport8_007 ++ kindSupport8_suffix_008
def kindSupport8_suffix_006 : List Nat := kindSupport8_006 ++ kindSupport8_suffix_007
def kindSupport8_suffix_005 : List Nat := kindSupport8_005 ++ kindSupport8_suffix_006
def kindSupport8_suffix_004 : List Nat := kindSupport8_004 ++ kindSupport8_suffix_005
def kindSupport8_suffix_003 : List Nat := kindSupport8_003 ++ kindSupport8_suffix_004
def kindSupport8_suffix_002 : List Nat := kindSupport8_002 ++ kindSupport8_suffix_003
def kindSupport8_suffix_001 : List Nat := kindSupport8_001 ++ kindSupport8_suffix_002
def kindSupport8_suffix_000 : List Nat := kindSupport8_000 ++ kindSupport8_suffix_001
theorem kindSupport8_source : kindSupports 8 =
    (PackedRawNatGrowth.readList 13 276 kindSupport8_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
