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
def ridgeSupport56_000 : List Nat := [0,67,68,69,70,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015]
def ridgeSupport56_001 : List Nat := [1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047]
def ridgeSupport56_002 : List Nat := [1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,4844,4845,4846,4847,4848,4849,4850,4851,4852,4853,4854,4855,4856,4857,4858,4859,4860,4861,4862]
def ridgeSupport56_003 : List Nat := [4863,4864,4865,4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4886,4887,4888,4889,4890,4891,4892,4893,4894]
def ridgeSupport56_004 : List Nat := [4895,4896,4897,4898,4899,4900,4901,4902,4903,4904,4905,4906,4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4919,4920,4921,4922,4923,4924,4925,4926]
def ridgeSupport56_005 : List Nat := [4927,4928,4929,4930,4931,4932,4933,4934,4935,4936,4937,4938,4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4953,4954,4955,4956,4957,4958]
def ridgeSupport56_006 : List Nat := [4959,4960,4961,4962,4963,4964,4965,4966,4967,4968,4969,4970,4971,4972,4973,4974,4975,4976,4977,4978,4979,4980,4981,4982,4983,4984,4985,4986,4987,4988,4989,4990]
def ridgeSupport56_007 : List Nat := [4991,4992,4993,4994,4995,4996,4997,4998,4999,5000,5001,5002,5003,5004,5005,5006,5007,5008,5009,5010,5011,5012,5013,5014,5015,5016,5017,5018,5019,5020,5021,5022]
def ridgeSupport56_008 : List Nat := [5023,5024,5025,5026,5027,5028,5029,5030,5031,5032,5033,5034,5035,5036,5037,5038,5039,5040,5041,5042,5043,5044,5045,5046,5047,5048,5049,5050,5051,5052,5053,5054]
def ridgeSupport56_009 : List Nat := [5055,5056,5057,5058,5059,5060,5061,5062,5063,5064,5065,5066,5067,5068,5069,5070,5071,5072,5073,5074,5075,5076,5077,5078,5079,5080,5081,5082,5083,5084,5085,5086]
def ridgeSupport56_010 : List Nat := [5087,5088,5089,5090,5091,5092,5093,5094,5095,5096,5097,5098,5099,5100,5101,5102,5103,5104,5105,5106,5107,5108,5109,5110,5111,5112,5113,5114,5115,5116,5117,5118]
def ridgeSupport56_011 : List Nat := [5119,5120,5121,5122,5123,5124,5125,5126,5127,5128,5129,5130,5131,5324,5325,5326,5327,5328,5329,5330,5331,5332,5333,5334,5335,5336,5337,5338,5339,5340,5341,5342]
def ridgeSupport56_012 : List Nat := [5343,5344,5345,5346,5347,5828,5829,5830,5831,5832,5833,5834,5835,5836,5837,5838,5839,5840,5841,5842,5843,5844,5845,5846,5847,5848,5849,5850,5851,6548,6549,6550]
def ridgeSupport56_013 : List Nat := [6551,6552,6553,6554,6555,6556,6557,6558,6559,6560,6561,6562,6563,6564,6565,6566,6567,6568,6569,6570,6571,6572,6573,6574,6575,6576,6577,6578,6579,6580,6581,6582]
def ridgeSupport56_014 : List Nat := [6583,6584,6585,6586,6587,6588,6589,6590,6591,6592,6593,6594,6595,6596,6597,6598,6599,6600,6601,6602,6603,6604,6605,6606,6607,6608,6609,6610,6611,6612,6613,6614]
def ridgeSupport56_015 : List Nat := [6615,6616,6617,6618,6619]
def ridgeSupport56_code : Nat := 0x19dbced67673b19d7ceb67573a99d3ce967473a19cfce767373999cbce567273919c7ce367173899c3ce167073819bfcdf66f73799bbcdd66e73719b7cdb66d73699b3cd966c73619afcd766b73599abcd566a73519a7cd366973499a3cd1668734199fccf667733999bccd6667331997ccb66573296dbb6d5b66db16d7b6b5b56da96d3b695b46da16cfb675b36d996cbb655b26d916c7b635b16d894e3a7153869c14dfa6f53769b94dba6d53669b14d7a6b53569a94d3a6953469a14cfa67533699940ba055026811407a035016809403a0150068013ff9ff4ff67f93fb9fd4fe67f13f79fb4fd67e93f39f94fc67e13ef9f74fb67d93eb9f54fa67d13e79f34f967c93e39f14f867c13df9ef4f767b93db9ed4f667b13d79eb4f567a93d39e94f467a13cf9e74f367993cb9e54f267913c79e34f167893c39e14f067813bf9df4ef67793bb9dd4ee67713b79db4ed67693b39d94ec67613af9d74eb67593ab9d54ea67513a79d34e967493a39d14e8674139f9cf4e7673939b9cd4e667313979cb4e567293939c94e4672138f9c74e3671938b9c54e267113879c34e167093839c14e0670137f9bf4df66f937b9bd4de66f13779bb4dd66e93739b94dc66e136f9b74db66d936b9b54da66d13679b34d966c93639b14d866c135f9af4d766b935b9ad4d666b13579ab4d566a93539a94d466a134f9a74d3669934b9a54d266913479a34d166893439a14d0668133f99f4cf667933b99d4ce667133799b4cd66693339994cc666132f9974cb665932b9954ca66513279934c966493239914c8664131f98f4c7663931b98d4c6663131798b4c566293139894c4662130f9874c3661930b9854c266113079834c166093039814c066012ff97f4bf65f92fb97d4be65f12f797b4bd65e92f39794bc65e12ef9774bb65d8424211908884242020f907883a41c20d906883241820b905882a4142099048822410207903881a40c2059028812408203901880a40420190088024001ff8ff87fa3fc1fd8fe87f23f81fb8fd87ea3f41f98fc87e23f01f78fb87da3ec1f58fa87d23e81f38f987ca3e41f18f887c23e01ef8f787ba0460228110086000
def ridgeSupport56_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport56_code
def ridgeSupport56_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport56_code
def ridgeSupport56_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport56_code
def ridgeSupport56_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport56_code
def ridgeSupport56_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport56_code
def ridgeSupport56_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport56_code
def ridgeSupport56_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport56_code
def ridgeSupport56_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport56_code
def ridgeSupport56_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport56_code
def ridgeSupport56_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport56_code
def ridgeSupport56_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport56_code
def ridgeSupport56_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport56_code
def ridgeSupport56_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport56_code
def ridgeSupport56_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport56_code
def ridgeSupport56_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport56_code
def ridgeSupport56_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport56_code
def ridgeSupport56_rest_016 : Nat := PackedRawNatGrowth.drop 6305 ridgeSupport56_code
def ridgeSupport56_suffix_016 : List Nat := []
def ridgeSupport56_suffix_015 : List Nat := ridgeSupport56_015 ++ ridgeSupport56_suffix_016
def ridgeSupport56_suffix_014 : List Nat := ridgeSupport56_014 ++ ridgeSupport56_suffix_015
def ridgeSupport56_suffix_013 : List Nat := ridgeSupport56_013 ++ ridgeSupport56_suffix_014
def ridgeSupport56_suffix_012 : List Nat := ridgeSupport56_012 ++ ridgeSupport56_suffix_013
def ridgeSupport56_suffix_011 : List Nat := ridgeSupport56_011 ++ ridgeSupport56_suffix_012
def ridgeSupport56_suffix_010 : List Nat := ridgeSupport56_010 ++ ridgeSupport56_suffix_011
def ridgeSupport56_suffix_009 : List Nat := ridgeSupport56_009 ++ ridgeSupport56_suffix_010
def ridgeSupport56_suffix_008 : List Nat := ridgeSupport56_008 ++ ridgeSupport56_suffix_009
def ridgeSupport56_suffix_007 : List Nat := ridgeSupport56_007 ++ ridgeSupport56_suffix_008
def ridgeSupport56_suffix_006 : List Nat := ridgeSupport56_006 ++ ridgeSupport56_suffix_007
def ridgeSupport56_suffix_005 : List Nat := ridgeSupport56_005 ++ ridgeSupport56_suffix_006
def ridgeSupport56_suffix_004 : List Nat := ridgeSupport56_004 ++ ridgeSupport56_suffix_005
def ridgeSupport56_suffix_003 : List Nat := ridgeSupport56_003 ++ ridgeSupport56_suffix_004
def ridgeSupport56_suffix_002 : List Nat := ridgeSupport56_002 ++ ridgeSupport56_suffix_003
def ridgeSupport56_suffix_001 : List Nat := ridgeSupport56_001 ++ ridgeSupport56_suffix_002
def ridgeSupport56_suffix_000 : List Nat := ridgeSupport56_000 ++ ridgeSupport56_suffix_001
theorem ridgeSupport56_source : candidateSupports 56 =
    (PackedRawNatGrowth.readList 13 485 ridgeSupport56_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
