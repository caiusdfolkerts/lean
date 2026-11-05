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
def kindSupport9_000 : List Nat := [4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696,4697,4698,4699,4700,4701,4702,4703,4704,4705]
def kindSupport9_001 : List Nat := [4706,4707,4708,4709,4710,4711,4712,4713,4714,4715,4716,4717,4718,4719,4720,4721,4722,4723,4724,4725,4726,4727,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737]
def kindSupport9_002 : List Nat := [4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756,4757,4758,4759,4760,4761,4762,4763,4764,4765,4766,4767,4768,4769]
def kindSupport9_003 : List Nat := [4770,4771,4772,4773,4774,4775,4776,4777,4778,4779,4780,4781,4782,4783,4784,4785,4786,4787,4788,4789,4790,4791,4792,4793,4794,4795,4796,4797,4798,4799,4800,4801]
def kindSupport9_004 : List Nat := [4802,4803,4804,4805,4806,4807,4808,4809,4810,4811,4812,4813,4814,4815,4816,4817,4818,4819,4820,4821,4822,4823,4824,4825,4826,4827,4828,4829,4830,4831,4832,4833]
def kindSupport9_005 : List Nat := [4834,4835,4836,4837,4838,4839,4840,4841,4842,4843,4844,4845,4846,4847,4848,4849,4850,4851,4852,4853,4854,4855,4856,4857,4858,4859,4860,4861,4862,4863,4864,4865]
def kindSupport9_006 : List Nat := [4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4886,4887,4888,4889,4890,4891,4892,4893,4894,4895,4896,4897]
def kindSupport9_007 : List Nat := [4898,4899,4900,4901,4902,4903,4904,4905,4906,4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4919,4920,4921,4922,4923,4924,4925,4926,4927,4928,4929]
def kindSupport9_008 : List Nat := [4930,4931,4932,4933,4934,4935,4936,4937,4938,4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4953,4954,4955,4956,4957,4958,4959,4960,4961]
def kindSupport9_009 : List Nat := [4962,4963,4964,4965,4966,4967,4968,4969,4970,4971,4972,4973,4974,4975,4976,4977,4978,4979,4980,4981,4982,4983,4984,4985,4986,4987,4988,4989,4990,4991,4992,4993]
def kindSupport9_010 : List Nat := [4994,4995,4996,4997,4998,4999,5000,5001,5002,5003,5004,5005,5006,5007,5008,5009,5010,5011,5012,5013,5014,5015,5016,5017,5018,5019,5020,5021,5022,5023,5024,5025]
def kindSupport9_011 : List Nat := [5026,5027,5028,5029,5030,5031,5032,5033,5034,5035,5036,5037,5038,5039,5040,5041,5042,5043,5044,5045,5046,5047,5048,5049,5050,5051,5052,5053,5054,5055,5056,5057]
def kindSupport9_012 : List Nat := [5058,5059,5060,5061,5062,5063,5064,5065,5066,5067,5068,5069,5070,5071,5072,5073,5074,5075,5076,5077,5078,5079,5080,5081,5082,5083,5084,5085,5086,5087,5088,5089]
def kindSupport9_013 : List Nat := [5090,5091,5092,5093,5094,5095,5096,5097,5098,5099,5100,5101,5102,5103,5104,5105,5106,5107,5108,5109,5110,5111,5112,5113,5114,5115,5116,5117,5118,5119,5120,5121]
def kindSupport9_014 : List Nat := [5122,5123,5124,5125,5126,5127,5128,5129,5130,5131,5132,5133,5134,5135,5136,5137,5138,5139,5140,5141,5142,5143,5144,5145,5146,5147,5148,5149,5150,5151,5152,5153]
def kindSupport9_015 : List Nat := [5154,5155,5156,5157,5158,5159,5160,5161,5162,5163,5164,5165,5166,5167,5168,5169,5170,5171,5172,5173,5174,5175,5176,5177,5178,5179,5180,5181,5182,5183,5184,5185]
def kindSupport9_016 : List Nat := [5186,5187,5188,5189,5190,5191,5192,5193,5194,5195,5196,5197,5198,5199,5200,5201,5202,5203,5204,5205,5206,5207,5208,5209,5210,5211,5212,5213,5214,5215,5216,5217]
def kindSupport9_017 : List Nat := [5218,5219,5220,5221,5222,5223,5224,5225,5226,5227,5228,5229,5230,5231,5232,5233,5234,5235,5236,5237]
def kindSupport9_code : Nat := 0xa3ad1d28e7472a38d1c28df46ea36d1b28d746aa34d1a28cf466a32d1928c7462a30d1828bf45ea2ed1728b745aa2cd1628af456a2ad1528a7452a28d14289f44ea26d13289744aa24d12288f446a22d112887442a20d10287f43ea1ed0f287743aa1cd0e286f436a1ad0d2867432a18d0c285f42ea16d0b285742aa14d0a284f426a12d092847422a10d08283f41ea0ed07283741aa0cd06282f416a0ad052827412a08d04281f40ea06d03281740aa04d02280f406a02d012807402a00d0027ff3fe9fecff27f73fa9fccfe27ef3f69facfd27e73f29f8cfc27df3ee9f6cfb27d73ea9f4cfa27cf3e69f2cf927c73e29f0cf827bf3de9eecf727b73da9eccf627af3d69eacf527a73d29e8cf4279f3ce9e6cf327973ca9e4cf2278f3c69e2cf127873c29e0cf0277f3be9decef27773ba9dccee276f3b69daced27673b29d8cec275f3ae9d6ceb27573aa9d4cea274f3a69d2ce927473a29d0ce8273f39e9cece7273739a9ccce6272f3969cace527273929c8ce4271f38e9c6ce3271738a9c4ce2270f3869c2ce127073829c0ce026ff37e9becdf26f737a9bccde26ef3769bacdd26e73729b8cdc26df36e9b6cdb26d736a9b4cda26cf3669b2cd926c73629b0cd826bf35e9aecd726b735a9accd626af3569aacd526a73529a8cd4269f34e9a6cd3269734a9a4cd2268f3469a2cd126873429a0cd0267f33e99eccf267733a99ccce266f33699accd2667332998ccc265f32e996ccb265732a994cca264f326992cc92647322990cc8263f31e98ecc7263731a98ccc6262f31698acc52627312988cc4261f30e986cc3261730a984cc2260f306982cc12607302980cc025ff2fe97ecbf25f72fa97ccbe25ef2f697acbd25e72f2978cbc25df2ee976cbb25d72ea974cba25cf2e6972cb925c72e2970cb825bf2de96ecb725b72da96ccb625af2d696acb525a72d2968cb4259f2ce966cb325972ca964cb2258f2c6962cb125872c2960cb0257f2be95ecaf25772ba95ccae256f2b695acad25672b2958cac255f2ae956cab25572aa954caa254f2a6952ca925472a2950ca8253f29e94eca7253729a94cca6252f29694aca52527292948ca4251f28e946ca3251728a944ca2250f286942ca12507282940ca024ff27e93ec9f24f727a93cc9e24ef27693ac9d24e7272938c9c24df26e936c9b24d726a934c9a24cf266932c9924c7262930c9824bf25e92ec9724b725a92cc9624af25692ac9524a7252928c94249f24e926c93249724a924c92248f246922c912487242
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 3744 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 4160 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 4576 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 4992 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 5408 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 5824 kindSupport9_code
def kindSupport9_rest_015 : Nat := PackedRawNatGrowth.drop 6240 kindSupport9_code
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 6656 kindSupport9_code
def kindSupport9_rest_017 : Nat := PackedRawNatGrowth.drop 7072 kindSupport9_code
def kindSupport9_rest_018 : Nat := PackedRawNatGrowth.drop 7332 kindSupport9_code
def kindSupport9_suffix_018 : List Nat := []
def kindSupport9_suffix_017 : List Nat := kindSupport9_017 ++ kindSupport9_suffix_018
def kindSupport9_suffix_016 : List Nat := kindSupport9_016 ++ kindSupport9_suffix_017
def kindSupport9_suffix_015 : List Nat := kindSupport9_015 ++ kindSupport9_suffix_016
def kindSupport9_suffix_014 : List Nat := kindSupport9_014 ++ kindSupport9_suffix_015
def kindSupport9_suffix_013 : List Nat := kindSupport9_013 ++ kindSupport9_suffix_014
def kindSupport9_suffix_012 : List Nat := kindSupport9_012 ++ kindSupport9_suffix_013
def kindSupport9_suffix_011 : List Nat := kindSupport9_011 ++ kindSupport9_suffix_012
def kindSupport9_suffix_010 : List Nat := kindSupport9_010 ++ kindSupport9_suffix_011
def kindSupport9_suffix_009 : List Nat := kindSupport9_009 ++ kindSupport9_suffix_010
def kindSupport9_suffix_008 : List Nat := kindSupport9_008 ++ kindSupport9_suffix_009
def kindSupport9_suffix_007 : List Nat := kindSupport9_007 ++ kindSupport9_suffix_008
def kindSupport9_suffix_006 : List Nat := kindSupport9_006 ++ kindSupport9_suffix_007
def kindSupport9_suffix_005 : List Nat := kindSupport9_005 ++ kindSupport9_suffix_006
def kindSupport9_suffix_004 : List Nat := kindSupport9_004 ++ kindSupport9_suffix_005
def kindSupport9_suffix_003 : List Nat := kindSupport9_003 ++ kindSupport9_suffix_004
def kindSupport9_suffix_002 : List Nat := kindSupport9_002 ++ kindSupport9_suffix_003
def kindSupport9_suffix_001 : List Nat := kindSupport9_001 ++ kindSupport9_suffix_002
def kindSupport9_suffix_000 : List Nat := kindSupport9_000 ++ kindSupport9_suffix_001
theorem kindSupport9_source : kindSupports 9 =
    (PackedRawNatGrowth.readList 13 564 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
