module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport22_000 : List Nat := [0,35,36,37,38,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649]
def ridgeSupport22_001 : List Nat := [650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681]
def ridgeSupport22_002 : List Nat := [682,683,684,685,686,687,688,689,690,691,692,693,694,4648,4649,4650,4651,4652,4653,4654,4655,4656,4657,4658,4659,4660,4661,4662,4663,4664,4665,4666]
def ridgeSupport22_003 : List Nat := [4667,4668,4669,4670,4671,4672,4673,4674,4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,4691,4692,4693,4694,4695,4696,4697,4698]
def ridgeSupport22_004 : List Nat := [4699,4700,4701,4702,4703,4704,4705,4706,4707,4708,4709,4710,4711,4712,4713,4714,4715,4716,4717,4718,4719,4720,4721,4722,4723,4724,4725,4726,4727,4728,4729,4730]
def ridgeSupport22_005 : List Nat := [4731,4732,4733,4734,4735,4736,4737,4738,4739,4740,4741,4742,4743,4744,4745,4746,4747,4748,4749,4750,4751,4752,4753,4754,4755,4756,4757,4758,4759,4760,4761,4762]
def ridgeSupport22_006 : List Nat := [4763,4764,4765,4766,4767,4768,4769,4770,4771,4772,4773,4774,4775,4776,4777,4778,4779,4780,4781,4782,4783,4784,4785,4786,4787,4788,4789,4790,4791,4792,4793,4794]
def ridgeSupport22_007 : List Nat := [4795,4796,4797,4798,4799,4800,4801,4802,4803,4804,4805,4806,4807,4808,4809,4810,4811,4812,4813,4814,4815,4816,4817,4818,4819,4820,4821,4822,4823,4824,4825,4826]
def ridgeSupport22_008 : List Nat := [4827,4828,4829,4830,4831,4832,4833,4834,4835,4836,4837,4838,4839,4840,4841,4842,4843,4844,4845,4846,4847,4848,4849,4850,4851,4852,4853,4854,4855,4856,4857,4858]
def ridgeSupport22_009 : List Nat := [4859,4860,4861,4862,4863,4864,4865,4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4886,4887,4888,4889,4890]
def ridgeSupport22_010 : List Nat := [4891,4892,4893,4894,4895,4896,4897,4898,4899,4900,4901,4902,4903,4904,4905,4906,4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4919,4920,4921,4922]
def ridgeSupport22_011 : List Nat := [4923,4924,4925,4926,4927,4928,4929,4930,4931,4932,4933,4934,4935,7408,7409,7410,7411,7412,7413,7414,7415,7416,7417,7418,7419,7420,7421,7422,7423,7424,7425,7426]
def ridgeSupport22_012 : List Nat := [7427,7428,7429,7430,7431,8272,8273,8274,8275,8276,8277,8278,8279,8280,8281,8282,8283,8284,8285,8286,8287,8288,8289,8290,8291,8292,8293,8294,8295,8296,8297,8298]
def ridgeSupport22_013 : List Nat := [8299,8300,8301,8302,8303,8304,8305,8306,8307,8308,8309,8310,8311,8312,8313,8314,8315,8316,8317,8318,8319,8320,8321,8322,8323,8324,8325,8326,8327,8328,8329,8330]
def ridgeSupport22_014 : List Nat := [8331,8332,8333,8334,8335,8336,8337,8338,8339,8340,8341,8342,8343]
def ridgeSupport22_code : Nat := 0x2097825a0958252093824a091824208f823a08d823208b822a0898222087821a0858212083820a081820207f81fa07d81f207b81ea07981e207781da07581d207381ca07181c206f81ba06d81b206b81aa06981a2067819a0658192063818a061818205f817a05d817205b816a0598162057815a0558152053814a0518141d077419d057411d037409d017401cff73f9cfd73f1cfb73e9cf973e1cf773d9cf573d1cf373c9cf173c13474d193454d113434d093414d0133f4cf933d4cf133b4ce93394ce13374cd93354cd13334cc93314cc132f4cb932d4cb132b4ca93294ca13274c993254c913234c893214c8131f4c7931d4c7131b4c693194c613174c593154c513134c493114c4130f4c3930d4c3130b4c293094c213074c193054c113034c093014c012ff4bf92fd4bf12fb4be92f94be12f74bd92f54bd12f34bc92f14bc12ef4bb92ed4bb12eb4ba92e94ba12e74b992e54b912e34b892e14b812df4b792dd4b712db4b692d94b612d74b592d54b512d34b492d14b412cf4b392cd4b312cb4b292c94b212c74b192c54b112c34b092c14b012bf4af92bd4af12bb4ae92b94ae12b74ad92b54ad12b34ac92b14ac12af4ab92ad4ab12ab4aa92a94aa12a74a992a54a912a34a892a14a8129f4a7929d4a7129b4a692994a612974a592954a512934a492914a4128f4a3928d4a3128b4a292894a212874a192854a112834a092814a0127f49f927d49f127b49e927949e127749d927549d127349c927149c126f49b926d49b126b49a926949a1267499926549912634989261498125f497925d497125b49692594961257495925549512534949251494124f493924d493124b49292494921247491924549112434909241490123f48f923d48f123b48e923948e123748d923548d123348c923148c122f48b922d48b122b48a922948a02b60ad42b40acc2b20ac42b00abc2ae0ab42ac0aac2aa0aa42a80a9c2a60a942a40a8c2a20a842a00a7c29e0a7429c0a6c29a0a642980a5c2960a542940a4c2920a442900a3c28e0a3428c0a2c28a0a242880a1c2860a142840a0c2820a0428009fc27e09f427c09ec27a09e427809dc27609d427409cc27209c427009bc0260094024008c000
def ridgeSupport22_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport22_code
def ridgeSupport22_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport22_code
def ridgeSupport22_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport22_code
def ridgeSupport22_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport22_code
def ridgeSupport22_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport22_code
def ridgeSupport22_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport22_code
def ridgeSupport22_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport22_code
def ridgeSupport22_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport22_code
def ridgeSupport22_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport22_code
def ridgeSupport22_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport22_code
def ridgeSupport22_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport22_code
def ridgeSupport22_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport22_code
def ridgeSupport22_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport22_code
def ridgeSupport22_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport22_code
def ridgeSupport22_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport22_code
def ridgeSupport22_rest_015 : Nat := PackedRawNatGrowth.drop 6454 ridgeSupport22_code
def ridgeSupport22_suffix_015 : List Nat := []
def ridgeSupport22_suffix_014 : List Nat := ridgeSupport22_014 ++ ridgeSupport22_suffix_015
def ridgeSupport22_suffix_013 : List Nat := ridgeSupport22_013 ++ ridgeSupport22_suffix_014
def ridgeSupport22_suffix_012 : List Nat := ridgeSupport22_012 ++ ridgeSupport22_suffix_013
def ridgeSupport22_suffix_011 : List Nat := ridgeSupport22_011 ++ ridgeSupport22_suffix_012
def ridgeSupport22_suffix_010 : List Nat := ridgeSupport22_010 ++ ridgeSupport22_suffix_011
def ridgeSupport22_suffix_009 : List Nat := ridgeSupport22_009 ++ ridgeSupport22_suffix_010
def ridgeSupport22_suffix_008 : List Nat := ridgeSupport22_008 ++ ridgeSupport22_suffix_009
def ridgeSupport22_suffix_007 : List Nat := ridgeSupport22_007 ++ ridgeSupport22_suffix_008
def ridgeSupport22_suffix_006 : List Nat := ridgeSupport22_006 ++ ridgeSupport22_suffix_007
def ridgeSupport22_suffix_005 : List Nat := ridgeSupport22_005 ++ ridgeSupport22_suffix_006
def ridgeSupport22_suffix_004 : List Nat := ridgeSupport22_004 ++ ridgeSupport22_suffix_005
def ridgeSupport22_suffix_003 : List Nat := ridgeSupport22_003 ++ ridgeSupport22_suffix_004
def ridgeSupport22_suffix_002 : List Nat := ridgeSupport22_002 ++ ridgeSupport22_suffix_003
def ridgeSupport22_suffix_001 : List Nat := ridgeSupport22_001 ++ ridgeSupport22_suffix_002
def ridgeSupport22_suffix_000 : List Nat := ridgeSupport22_000 ++ ridgeSupport22_suffix_001
theorem ridgeSupport22_source : candidateSupports 22 =
    (PackedRawNatGrowth.readList 14 461 ridgeSupport22_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
