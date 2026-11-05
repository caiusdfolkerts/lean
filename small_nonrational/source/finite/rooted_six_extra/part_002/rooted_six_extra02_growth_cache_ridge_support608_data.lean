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
def ridgeSupport608_000 : List Nat := [49,79,89,98,99,639,640,641,642,649,650,792,794,796,798,800,805,806,808,811,813,815,817,819,821,826,827,829,832,1013,1014,1015]
def ridgeSupport608_001 : List Nat := [1016,1023,1024,1166,1168,1170,1172,1174,1179,1180,1182,1185,1187,1189,1191,1193,1195,1200,1201,1203,1206,1275,1277,1279,1281,1283,1288,1289,1291,1294,1296,1298]
def ridgeSupport608_002 : List Nat := [1300,1302,1304,1309,1310,1312,1315,1364,1365,1367,1368,1371,1372,1373,1375,1376,1378,1385,1386,3746,3751,3752,3757,3816,3817,3830,3831,3836,3838,3844,3845,3850]
def ridgeSupport608_003 : List Nat := [3851,3857,3859,3864,3865,3878,3879,3912,3913,3914,3919,3920,3925,3926,3927,3940,3941,3946,3947,3964,3965,3970,3971,3986,3991,3992,3997,4056,4057,4070,4071,4076]
def ridgeSupport608_004 : List Nat := [4078,4084,4085,4090,4091,4097,4099,4104,4105,4118,4119,4152,4153,4154,4159,4160,4165,4166,4167,4180,4181,4186,4187,4204,4205,4210,4211,4298,4303,4310,4315,4330]
def ridgeSupport608_005 : List Nat := [4331,4342,4343,4370,4375,4382,4387,4402,4403,4414,4415,4514,4519,4520,4525,4584,4585,4598,4599,4604,4606,4612,4613,4618,4619,4625,4627,4632,4633,4646,4647,4680]
def ridgeSupport608_006 : List Nat := [4681,4682,4687,4688,4693,4694,4695,4708,4709,4714,4715,4732,4733,4738,4739,4780,4781,4788,4789,4922,4927,4934,4939,4954,4955,4966,4967,4994,4999,5006,5011,5026]
def ridgeSupport608_007 : List Nat := [5027,5038,5039,5264,5266,5273,5275,5276,5278,5285,5287,5296,5297,5302,5303,5312,5314,5321,5323,5332,5333,5338,5339,5702,5703,5738,5739,5798,5799,6336,6337,6350]
def ridgeSupport608_008 : List Nat := [6351,6360,6361,6363,6364,6365,6367,6384,6385,6398,6399,6408,6409,6411,6412,6413,6415,6447,6448,6449,6450,6465,6466,6467,6468,6504,6505,6518,6519,6528,6529,6531]
def ridgeSupport608_009 : List Nat := [6532,6533,6535,6567,6568,6569,6570,6585,6586,6587,6588]
def ridgeSupport608_code : Nat := 0x66f33779bacdce6ab3539a8cd3e61f30b984cc1e607301977cbb65a72d1944ca1e50b283932c98e4c325f90fc86e433217909c8463ff1fd8f1c78637f1bb8dcc6de3671b18cfc6763071816a7b5359aecd5647b23536e9b54d5a6a532e9934c2a6052de96d4b1a58529e94b49ea4e526e933492a484ebe75d3a39d14e4e71d3879c14d9e6cd35b9ad4d2e68d33f99d4ad65692ad9564a0e50527d93e49ae4d5265932495e4ad255928493e495249924489e44d21990c484e42320b90548164091fe8fe47de3ed1e98f446b63511a78d144fe27d133899448e23d11788943de1ed0eb875436e1ad0cf86541ce0e506d836416e0b505582a411e08d04582040fe07503981c405e02d009804400e002ffb7fd3fd5fe8fee7f63f9dfccfd97ec3e75f30f977c93e0df04f7d7be3daded4f657b23d5deacf557a83d3de94f497a43c9de4cf1978c3c4de22f0b7853c15e08efe77e3bdddecee97743ab5d50ea775115a8ad25622b0157caba55c2ad9560aae5552aa148ca4051e28e9460a2c5142891440a1c50b2849420a0650127f93f49f64b625992c49604ab254929c94a4a3250927893849b24b125092449024710007fe3f81fb8fd87ea34019e8cec6743351998cc465e32d1958ca064c3251900c7863831a18c0a285122821408a004fe063031016409e031
def ridgeSupport608_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport608_code
def ridgeSupport608_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport608_code
def ridgeSupport608_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport608_code
def ridgeSupport608_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport608_code
def ridgeSupport608_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport608_code
def ridgeSupport608_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport608_code
def ridgeSupport608_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport608_code
def ridgeSupport608_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport608_code
def ridgeSupport608_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport608_code
def ridgeSupport608_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport608_code
def ridgeSupport608_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport608_code
def ridgeSupport608_suffix_010 : List Nat := []
def ridgeSupport608_suffix_009 : List Nat := ridgeSupport608_009 ++ ridgeSupport608_suffix_010
def ridgeSupport608_suffix_008 : List Nat := ridgeSupport608_008 ++ ridgeSupport608_suffix_009
def ridgeSupport608_suffix_007 : List Nat := ridgeSupport608_007 ++ ridgeSupport608_suffix_008
def ridgeSupport608_suffix_006 : List Nat := ridgeSupport608_006 ++ ridgeSupport608_suffix_007
def ridgeSupport608_suffix_005 : List Nat := ridgeSupport608_005 ++ ridgeSupport608_suffix_006
def ridgeSupport608_suffix_004 : List Nat := ridgeSupport608_004 ++ ridgeSupport608_suffix_005
def ridgeSupport608_suffix_003 : List Nat := ridgeSupport608_003 ++ ridgeSupport608_suffix_004
def ridgeSupport608_suffix_002 : List Nat := ridgeSupport608_002 ++ ridgeSupport608_suffix_003
def ridgeSupport608_suffix_001 : List Nat := ridgeSupport608_001 ++ ridgeSupport608_suffix_002
def ridgeSupport608_suffix_000 : List Nat := ridgeSupport608_000 ++ ridgeSupport608_suffix_001
theorem ridgeSupport608_source : candidateSupports 608 =
    (PackedRawNatGrowth.readList 13 299 ridgeSupport608_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
