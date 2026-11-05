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
def kindSupport9_000 : List Nat := [5348,5349,5350,5351,5352,5353,5354,5355,5356,5357,5358,5359,5360,5361,5362,5363,5364,5365,5366,5367,5368,5369,5370,5371,5372,5373,5374,5375,5376,5377,5378,5379]
def kindSupport9_001 : List Nat := [5380,5381,5382,5383,5384,5385,5386,5387,5388,5389,5390,5391,5392,5393,5394,5395,5396,5397,5398,5399,5400,5401,5402,5403,5404,5405,5406,5407,5408,5409,5410,5411]
def kindSupport9_002 : List Nat := [5412,5413,5414,5415,5416,5417,5418,5419,5420,5421,5422,5423,5424,5425,5426,5427,5428,5429,5430,5431,5432,5433,5434,5435,5436,5437,5438,5439,5440,5441,5442,5443]
def kindSupport9_003 : List Nat := [5444,5445,5446,5447,5448,5449,5450,5451,5452,5453,5454,5455,5456,5457,5458,5459,5460,5461,5462,5463,5464,5465,5466,5467,5468,5469,5470,5471,5472,5473,5474,5475]
def kindSupport9_004 : List Nat := [5476,5477,5478,5479,5480,5481,5482,5483,5484,5485,5486,5487,5488,5489,5490,5491,5492,5493,5494,5495,5496,5497,5498,5499,5500,5501,5502,5503,5504,5505,5506,5507]
def kindSupport9_005 : List Nat := [5508,5509,5510,5511,5512,5513,5514,5515,5516,5517,5518,5519,5520,5521,5522,5523,5524,5525,5526,5527,5528,5529,5530,5531,5532,5533,5534,5535,5536,5537,5538,5539]
def kindSupport9_006 : List Nat := [5540,5541,5542,5543,5544,5545,5546,5547,5548,5549,5550,5551,5552,5553,5554,5555,5556,5557,5558,5559,5560,5561,5562,5563,5564,5565,5566,5567,5568,5569,5570,5571]
def kindSupport9_007 : List Nat := [5572,5573,5574,5575,5576,5577,5578,5579,5580,5581,5582,5583,5584,5585,5586,5587,5588,5589,5590,5591,5592,5593,5594,5595,5596,5597,5598,5599,5600,5601,5602,5603]
def kindSupport9_008 : List Nat := [5604,5605,5606,5607,5608,5609,5610,5611,5612,5613,5614,5615,5616,5617,5618,5619,5620,5621,5622,5623,5624,5625,5626,5627,5628,5629,5630,5631,5632,5633,5634,5635]
def kindSupport9_009 : List Nat := [5636,5637,5638,5639,5640,5641,5642,5643,5644,5645,5646,5647,5648,5649,5650,5651,5652,5653,5654,5655,5656,5657,5658,5659,5660,5661,5662,5663,5664,5665,5666,5667]
def kindSupport9_010 : List Nat := [5668,5669,5670,5671,5672,5673,5674,5675,5676,5677,5678,5679,5680,5681,5682,5683,5684,5685,5686,5687,5688,5689,5690,5691,5692,5693,5694,5695,5696,5697,5698,5699]
def kindSupport9_011 : List Nat := [5700,5701,5702,5703,5704,5705,5706,5707,5708,5709,5710,5711,5712,5713,5714,5715,5716,5717,5718,5719,5720,5721,5722,5723,5724,5725,5726,5727,5728,5729,5730,5731]
def kindSupport9_012 : List Nat := [5732,5733,5734,5735,5736,5737,5738,5739,5740,5741,5742,5743,5744,5745,5746,5747,5748,5749,5750,5751,5752,5753,5754,5755,5756,5757,5758,5759,5760,5761,5762,5763]
def kindSupport9_013 : List Nat := [5764,5765,5766,5767,5768,5769,5770,5771,5772,5773,5774,5775,5776,5777,5778,5779,5780,5781,5782,5783,5784,5785,5786,5787,5788,5789,5790,5791,5792,5793,5794,5795]
def kindSupport9_014 : List Nat := [5796,5797,5798,5799,5800,5801,5802,5803,5804,5805,5806,5807,5808,5809,5810,5811,5812,5813,5814,5815,5816,5817,5818,5819,5820,5821,5822,5823,5824,5825,5826,5827]
def kindSupport9_015 : List Nat := [5828,5829,5830,5831,5832,5833,5834,5835,5836,5837,5838,5839,5840,5841,5842,5843,5844,5845,5846,5847,5848,5849,5850,5851]
def kindSupport9_code : Nat := 0xb6ddb6adb36d8b6bdb5adab6d4b69db4ada36d0b67db3ad9b6ccb65db2ad936c8b63db1ad8b6c4b61db0ad836c0b5fdafad7b6bcb5ddaead736b8b5bdadad6b6b4b59dacad636b0b57dabad5b6acb55daaad536a8b53da9ad4b6a4b51da8ad436a0b4fda7ad3b69cb4dda6ad33698b4bda5ad2b694b49da4ad23690b47da3ad1b68cb45da2ad13688b43da1ad0b684b41da0ad03680b3fd9facfb67cb3dd9eacf3678b3bd9daceb674b39d9cace3670b37d9bacdb66cb35d9aacd3668b33d99accb664b31d98acc3660b2fd97acbb65cb2dd96acb3658b2bd95acab654b29d94aca3650b27d93ac9b64cb25d92ac93648b23d91ac8b644b21d90ac83640b1fd8fac7b63cb1dd8eac73638b1bd8dac6b634b19d8cac63630b17d8bac5b62cb15d8aac53628b13d89ac4b624b11d88ac43620b0fd87ac3b61cb0dd86ac33618b0bd85ac2b614b09d84ac23610b07d83ac1b60cb05d82ac13608b03d81ac0b604b01d80ac03600affd7fabfb5fcafdd7eabf35f8afbd7dabeb5f4af9d7cabe35f0af7d7babdb5ecaf5d7aabd35e8af3d79abcb5e4af1d78abc35e0aefd77abbb5dcaedd76abb35d8aebd75abab5d4ae9d74aba35d0ae7d73ab9b5ccae5d72ab935c8ae3d71ab8b5c4ae1d70ab835c0adfd6fab7b5bcaddd6eab735b8adbd6dab6b5b4ad9d6cab635b0ad7d6bab5b5acad5d6aab535a8ad3d69ab4b5a4ad1d68ab435a0acfd67ab3b59cacdd66ab33598acbd65ab2b594ac9d64ab23590ac7d63ab1b58cac5d62ab13588ac3d61ab0b584ac1d60ab03580abfd5faafb57cabdd5eaaf3578abbd5daaeb574ab9d5caae3570ab7d5baadb56cab5d5aaad3568ab3d59aacb564ab1d58aac3560aafd57aabb55caadd56aab3558aabd55aaab554aa9d54aaa3550aa7d53aa9b54caa5d52aa93548aa3d51aa8b544aa1d50aa83540a9fd4faa7b53ca9dd4eaa73538a9bd4daa6b534a99d4caa63530a97d4baa5b52ca95d4aaa53528a93d49aa4b524a91d48aa43520a8fd47aa3b51ca8dd46aa33518a8bd45aa2b514a89d44aa23510a87d43aa1b50ca85d42aa13508a83d41aa0b504a81d40aa03500a7fd3fa9fb4fca7dd3ea9f34f8a7bd3da9eb4f4a79d3ca9e34f0a77d3ba9db4eca75d3aa9d34e8a73d39a9cb4e4
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
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 6552 kindSupport9_code
def kindSupport9_suffix_016 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 504 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
