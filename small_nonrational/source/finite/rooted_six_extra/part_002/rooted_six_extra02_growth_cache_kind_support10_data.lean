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
def kindSupport10_000 : List Nat := [5852,5853,5854,5855,5856,5857,5858,5859,5860,5861,5862,5863,5864,5865,5866,5867,5868,5869,5870,5871,5872,5873,5874,5875,5876,5877,5878,5879,5880,5881,5882,5883]
def kindSupport10_001 : List Nat := [5884,5885,5886,5887,5888,5889,5890,5891,5892,5893,5894,5895,5896,5897,5898,5899,5900,5901,5902,5903,5904,5905,5906,5907,5908,5909,5910,5911,5912,5913,5914,5915]
def kindSupport10_002 : List Nat := [5916,5917,5918,5919,5920,5921,5922,5923,5924,5925,5926,5927,5928,5929,5930,5931,5932,5933,5934,5935,5936,5937,5938,5939,5940,5941,5942,5943,5944,5945,5946,5947]
def kindSupport10_003 : List Nat := [5948,5949,5950,5951,5952,5953,5954,5955,5956,5957,5958,5959,5960,5961,5962,5963,5964,5965,5966,5967,5968,5969,5970,5971,5972,5973,5974,5975,5976,5977,5978,5979]
def kindSupport10_004 : List Nat := [5980,5981,5982,5983,5984,5985,5986,5987,5988,5989,5990,5991,5992,5993,5994,5995,5996,5997,5998,5999,6000,6001,6002,6003,6004,6005,6006,6007,6008,6009,6010,6011]
def kindSupport10_005 : List Nat := [6012,6013,6014,6015,6016,6017,6018,6019,6020,6021,6022,6023,6024,6025,6026,6027,6028,6029,6030,6031,6032,6033,6034,6035,6036,6037,6038,6039,6040,6041,6042,6043]
def kindSupport10_006 : List Nat := [6044,6045,6046,6047,6048,6049,6050,6051,6052,6053,6054,6055,6056,6057,6058,6059,6060,6061,6062,6063,6064,6065,6066,6067,6068,6069,6070,6071,6072,6073,6074,6075]
def kindSupport10_007 : List Nat := [6076,6077,6078,6079,6080,6081,6082,6083,6084,6085,6086,6087,6088,6089,6090,6091,6092,6093,6094,6095,6096,6097,6098,6099,6100,6101,6102,6103,6104,6105,6106,6107]
def kindSupport10_008 : List Nat := [6108,6109,6110,6111,6112,6113,6114,6115,6116,6117,6118,6119,6120,6121,6122,6123,6124,6125,6126,6127,6128,6129,6130,6131,6132,6133,6134,6135,6136,6137,6138,6139]
def kindSupport10_009 : List Nat := [6140,6141,6142,6143,6144,6145,6146,6147,6148,6149,6150,6151,6152,6153,6154,6155,6156,6157,6158,6159,6160,6161,6162,6163,6164,6165,6166,6167,6168,6169,6170,6171]
def kindSupport10_010 : List Nat := [6172,6173,6174,6175,6176,6177,6178,6179,6180,6181,6182,6183,6184,6185,6186,6187,6188,6189,6190,6191,6192,6193,6194,6195,6196,6197,6198,6199,6200,6201,6202,6203]
def kindSupport10_011 : List Nat := [6204,6205,6206,6207,6208,6209,6210,6211,6212,6213,6214,6215,6216,6217,6218,6219,6220,6221,6222,6223,6224,6225,6226,6227,6228,6229,6230,6231,6232,6233,6234,6235]
def kindSupport10_012 : List Nat := [6236,6237,6238,6239,6240,6241,6242,6243,6244,6245,6246,6247,6248,6249,6250,6251,6252,6253,6254,6255,6256,6257,6258,6259,6260,6261,6262,6263,6264,6265,6266,6267]
def kindSupport10_013 : List Nat := [6268,6269,6270,6271,6272,6273,6274,6275,6276,6277,6278,6279,6280,6281,6282,6283,6284,6285,6286,6287,6288,6289,6290,6291,6292,6293,6294,6295,6296,6297,6298,6299]
def kindSupport10_014 : List Nat := [6300,6301,6302,6303,6304,6305,6306,6307,6308,6309,6310,6311,6312,6313,6314,6315,6316,6317,6318,6319,6320,6321,6322,6323,6324,6325,6326,6327,6328,6329,6330,6331]
def kindSupport10_015 : List Nat := [6332,6333,6334,6335,6336,6337,6338,6339,6340,6341,6342,6343,6344,6345,6346,6347,6348,6349,6350,6351,6352,6353,6354,6355,6356,6357,6358,6359,6360,6361,6362,6363]
def kindSupport10_016 : List Nat := [6364,6365,6366,6367,6368,6369,6370,6371,6372,6373,6374,6375,6376,6377,6378,6379,6380,6381,6382,6383,6384,6385,6386,6387,6388,6389,6390,6391,6392,6393,6394,6395]
def kindSupport10_017 : List Nat := [6396,6397,6398,6399,6400,6401,6402,6403,6404,6405,6406,6407,6408,6409,6410,6411,6412,6413,6414,6415,6416,6417,6418,6419,6420,6421,6422,6423,6424,6425,6426,6427]
def kindSupport10_018 : List Nat := [6428,6429,6430,6431,6432,6433,6434,6435,6436,6437,6438,6439,6440,6441,6442,6443,6444,6445,6446,6447,6448,6449,6450,6451,6452,6453,6454,6455,6456,6457,6458,6459]
def kindSupport10_019 : List Nat := [6460,6461,6462,6463,6464,6465,6466,6467,6468,6469,6470,6471,6472,6473,6474,6475,6476,6477,6478,6479,6480,6481,6482,6483,6484,6485,6486,6487,6488,6489,6490,6491]
def kindSupport10_020 : List Nat := [6492,6493,6494,6495,6496,6497,6498,6499,6500,6501,6502,6503,6504,6505,6506,6507,6508,6509,6510,6511,6512,6513,6514,6515,6516,6517,6518,6519,6520,6521,6522,6523]
def kindSupport10_021 : List Nat := [6524,6525,6526,6527,6528,6529,6530,6531,6532,6533,6534,6535,6536,6537,6538,6539,6540,6541,6542,6543,6544,6545,6546,6547,6548,6549,6550,6551,6552,6553,6554,6555]
def kindSupport10_022 : List Nat := [6556,6557,6558,6559,6560,6561,6562,6563,6564,6565,6566,6567,6568,6569,6570,6571,6572,6573,6574,6575,6576,6577,6578,6579,6580,6581,6582,6583,6584,6585,6586,6587]
def kindSupport10_023 : List Nat := [6588,6589,6590,6591,6592,6593,6594,6595,6596,6597,6598,6599,6600,6601,6602,6603,6604,6605,6606,6607,6608,6609,6610,6611,6612,6613,6614,6615,6616,6617,6618,6619]
def kindSupport10_code : Nat := 0xcede76b3b39d8cebe75b3ab9d4ce9e74b3a39d0ce7e73b39b9ccce5e72b3939c8ce3e71b38b9c4ce1e70b3839c0cdfe6fb37b9bccdde6eb3739b8cdbe6db36b9b4cd9e6cb3639b0cd7e6bb35b9accd5e6ab3539a8cd3e69b34b9a4cd1e68b3439a0ccfe67b33b99cccde66b333998ccbe65b32b994cc9e64b323990cc7e63b31b98ccc5e62b313988cc3e61b30b984cc1e60b303980cbfe5fb2fb97ccbde5eb2f3978cbbe5db2eb974cb9e5cb2e3970cb7e5bb2db96ccb5e5ab2d3968cb3e59b2cb964cb1e58b2c3960cafe57b2bb95ccade56b2b3958cabe55b2ab954ca9e54b2a3950ca7e53b29b94cca5e52b293948ca3e51b28b944ca1e50b283940c9fe4fb27b93cc9de4eb273938c9be4db26b934c99e4cb263930c97e4bb25b92cc95e4ab253928c93e49b24b924c91e48b243920c8fe47b23b91cc8de46b233918c8be45b22b914c89e44b223910c87e43b21b90cc85e42b213908c83e41b20b904c81e40b203900c7fe3fb1fb8fcc7de3eb1f38f8c7be3db1eb8f4c79e3cb1e38f0c77e3bb1db8ecc75e3ab1d38e8c73e39b1cb8e4c71e38b1c38e0c6fe37b1bb8dcc6de36b1b38d8c6be35b1ab8d4c69e34b1a38d0c67e33b19b8ccc65e32b1938c8c63e31b18b8c4c61e30b1838c0c5fe2fb17b8bcc5de2eb1738b8c5be2db16b8b4c59e2cb1638b0c57e2bb15b8acc55e2ab1538a8c53e29b14b8a4c51e28b1438a0c4fe27b13b89cc4de26b133898c4be25b12b894c49e24b123890c47e23b11b88cc45e22b113888c43e21b10b884c41e20b103880c3fe1fb0fb87cc3de1eb0f3878c3be1db0eb874c39e1cb0e3870c37e1bb0db86cc35e1ab0d3868c33e19b0cb864c31e18b0c3860c2fe17b0bb85cc2de16b0b3858c2be15b0ab854c29e14b0a3850c27e13b09b84cc25e12b093848c23e11b08b844c21e10b083840c1fe0fb07b83cc1de0eb073838c1be0db06b834c19e0cb063830c17e0bb05b82cc15e0ab053828c13e09b04b824c11e08b043820c0fe07b03b81cc0de06b033818c0be05b02b814c09e04b023810c07e03b01b80cc05e02b013808c03e01b00b804c01e00b003800bffdffaffb7fcbfddfeaff37f8bfbdfdafeb7f4bf9dfcafe37f0bf7dfbafdb7ecbf5dfaafd37e8bf3df9afcb7e4bf1df8afc37e0befdf7afbb7dcbeddf6afb37d8bebdf5afab7d4be9df4afa37d0be7df3af9b7ccbe5df2af937c8be3df1af8b7c4be1df0af837c0bdfdefaf7b7bcbdddeeaf737b8bdbdedaf6b7b4bd9decaf637b0bd7debaf5b7acbd5deaaf537a8bd3de9af4b7a4bd1de8af437a0bcfde7af3b79cbcdde6af33798bcbde5af2b794bc9de4af23790bc7de3af1b78cbc5de2af13788bc3de1af0b784bc1de0af03780bbfddfaefb77cbbdddeaef3778bbbdddaeeb774bb9ddcaee3770bb7ddbaedb76cbb5ddaaed3768bb3dd9aecb764bb1dd8aec3760bafdd7aebb75cbaddd6aeb3758babdd5aeab754ba9dd4aea3750ba7dd3ae9b74cba5dd2ae93748ba3dd1ae8b744ba1dd0ae83740b9fdcfae7b73cb9ddceae73738b9bdcdae6b734b99dccae63730b97dcbae5b72cb95dcaae53728b93dc9ae4b724b91dc8ae43720b8fdc7ae3b71cb8ddc6ae33718b8bdc5ae2b714b89dc4ae23710b87dc3ae1b70cb85dc2ae13708b83dc1ae0b704b81dc0ae03700b7fdbfadfb6fcb7ddbeadf36f8b7bdbdadeb6f4b79dbcade36f0b77dbbaddb6ecb75dbaadd36e8b73db9adcb6e4b71db8adc36e0b6fdb7adbb6dc
def kindSupport10_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport10_code
def kindSupport10_rest_001 : Nat := PackedRawNatGrowth.drop 416 kindSupport10_code
def kindSupport10_rest_002 : Nat := PackedRawNatGrowth.drop 832 kindSupport10_code
def kindSupport10_rest_003 : Nat := PackedRawNatGrowth.drop 1248 kindSupport10_code
def kindSupport10_rest_004 : Nat := PackedRawNatGrowth.drop 1664 kindSupport10_code
def kindSupport10_rest_005 : Nat := PackedRawNatGrowth.drop 2080 kindSupport10_code
def kindSupport10_rest_006 : Nat := PackedRawNatGrowth.drop 2496 kindSupport10_code
def kindSupport10_rest_007 : Nat := PackedRawNatGrowth.drop 2912 kindSupport10_code
def kindSupport10_rest_008 : Nat := PackedRawNatGrowth.drop 3328 kindSupport10_code
def kindSupport10_rest_009 : Nat := PackedRawNatGrowth.drop 3744 kindSupport10_code
def kindSupport10_rest_010 : Nat := PackedRawNatGrowth.drop 4160 kindSupport10_code
def kindSupport10_rest_011 : Nat := PackedRawNatGrowth.drop 4576 kindSupport10_code
def kindSupport10_rest_012 : Nat := PackedRawNatGrowth.drop 4992 kindSupport10_code
def kindSupport10_rest_013 : Nat := PackedRawNatGrowth.drop 5408 kindSupport10_code
def kindSupport10_rest_014 : Nat := PackedRawNatGrowth.drop 5824 kindSupport10_code
def kindSupport10_rest_015 : Nat := PackedRawNatGrowth.drop 6240 kindSupport10_code
def kindSupport10_rest_016 : Nat := PackedRawNatGrowth.drop 6656 kindSupport10_code
def kindSupport10_rest_017 : Nat := PackedRawNatGrowth.drop 7072 kindSupport10_code
def kindSupport10_rest_018 : Nat := PackedRawNatGrowth.drop 7488 kindSupport10_code
def kindSupport10_rest_019 : Nat := PackedRawNatGrowth.drop 7904 kindSupport10_code
def kindSupport10_rest_020 : Nat := PackedRawNatGrowth.drop 8320 kindSupport10_code
def kindSupport10_rest_021 : Nat := PackedRawNatGrowth.drop 8736 kindSupport10_code
def kindSupport10_rest_022 : Nat := PackedRawNatGrowth.drop 9152 kindSupport10_code
def kindSupport10_rest_023 : Nat := PackedRawNatGrowth.drop 9568 kindSupport10_code
def kindSupport10_rest_024 : Nat := PackedRawNatGrowth.drop 9984 kindSupport10_code
def kindSupport10_suffix_024 : List Nat := []
def kindSupport10_suffix_023 : List Nat := kindSupport10_023 ++ kindSupport10_suffix_024
def kindSupport10_suffix_022 : List Nat := kindSupport10_022 ++ kindSupport10_suffix_023
def kindSupport10_suffix_021 : List Nat := kindSupport10_021 ++ kindSupport10_suffix_022
def kindSupport10_suffix_020 : List Nat := kindSupport10_020 ++ kindSupport10_suffix_021
def kindSupport10_suffix_019 : List Nat := kindSupport10_019 ++ kindSupport10_suffix_020
def kindSupport10_suffix_018 : List Nat := kindSupport10_018 ++ kindSupport10_suffix_019
def kindSupport10_suffix_017 : List Nat := kindSupport10_017 ++ kindSupport10_suffix_018
def kindSupport10_suffix_016 : List Nat := kindSupport10_016 ++ kindSupport10_suffix_017
def kindSupport10_suffix_015 : List Nat := kindSupport10_015 ++ kindSupport10_suffix_016
def kindSupport10_suffix_014 : List Nat := kindSupport10_014 ++ kindSupport10_suffix_015
def kindSupport10_suffix_013 : List Nat := kindSupport10_013 ++ kindSupport10_suffix_014
def kindSupport10_suffix_012 : List Nat := kindSupport10_012 ++ kindSupport10_suffix_013
def kindSupport10_suffix_011 : List Nat := kindSupport10_011 ++ kindSupport10_suffix_012
def kindSupport10_suffix_010 : List Nat := kindSupport10_010 ++ kindSupport10_suffix_011
def kindSupport10_suffix_009 : List Nat := kindSupport10_009 ++ kindSupport10_suffix_010
def kindSupport10_suffix_008 : List Nat := kindSupport10_008 ++ kindSupport10_suffix_009
def kindSupport10_suffix_007 : List Nat := kindSupport10_007 ++ kindSupport10_suffix_008
def kindSupport10_suffix_006 : List Nat := kindSupport10_006 ++ kindSupport10_suffix_007
def kindSupport10_suffix_005 : List Nat := kindSupport10_005 ++ kindSupport10_suffix_006
def kindSupport10_suffix_004 : List Nat := kindSupport10_004 ++ kindSupport10_suffix_005
def kindSupport10_suffix_003 : List Nat := kindSupport10_003 ++ kindSupport10_suffix_004
def kindSupport10_suffix_002 : List Nat := kindSupport10_002 ++ kindSupport10_suffix_003
def kindSupport10_suffix_001 : List Nat := kindSupport10_001 ++ kindSupport10_suffix_002
def kindSupport10_suffix_000 : List Nat := kindSupport10_000 ++ kindSupport10_suffix_001
theorem kindSupport10_source : kindSupports 10 =
    (PackedRawNatGrowth.readList 13 768 kindSupport10_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
