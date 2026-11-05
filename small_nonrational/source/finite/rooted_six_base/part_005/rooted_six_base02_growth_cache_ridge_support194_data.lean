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
def ridgeSupport194_000 : List Nat := [9,31,41,47,53,54,102,103,106,107,110,111,174,175,178,179,182,183,246,247,251,253,254,258,260,261,263,267,268,272,274,275]
def ridgeSupport194_001 : List Nat := [279,281,282,284,533,534,535,538,539,540,542,547,549,554,555,556,559,560,561,563,568,570,617,618,619,620,621,622,689,690,691,694]
def ridgeSupport194_002 : List Nat := [695,696,698,703,705,710,711,712,715,716,717,719,724,726,773,774,775,778,779,780,782,787,789,794,795,796,799,800,801,803,808,810]
def ridgeSupport194_003 : List Nat := [857,858,860,861,862,863,865,866,868,869,871,872,1401,1403,1407,1409,1460,1461,1466,1467,1487,1489,1493,1495,1500,1501,1506,1507,1508,1509,1514,1515]
def ridgeSupport194_004 : List Nat := [1556,1557,1562,1563,1569,1571,1575,1577,1596,1597,1602,1603,1620,1621,1626,1627,1905,1907,1911,1913,1916,1917,1922,1923,1964,1965,1970,1971,1991,1993,1997,1999]
def ridgeSupport194_005 : List Nat := [2004,2005,2010,2011,2012,2013,2018,2019,2025,2027,2031,2033,2060,2061,2066,2067,2084,2085,2090,2091,2109,2111,2139,2141,2154,2155,2172,2173,2181,2183,2211,2213]
def ridgeSupport194_006 : List Nat := [2226,2227,2244,2245,2673,2675,2679,2681,2684,2685,2690,2691,2732,2733,2738,2739,2759,2761,2765,2767,2772,2773,2778,2779,2780,2781,2786,2787,2793,2795,2799,2801]
def ridgeSupport194_007 : List Nat := [2828,2829,2834,2835,2852,2853,2858,2859,2877,2879,2907,2909,2922,2923,2940,2941,2949,2951,2979,2981,2994,2995,3012,3013,3777,3779,3783,3785,3788,3789,3794,3795]
def ridgeSupport194_008 : List Nat := [3836,3837,3842,3843,3863,3865,3869,3871,3876,3877,3882,3883,3884,3885,3890,3891,3897,3899,3903,3905,3932,3933,3938,3939,3956,3957,3962,3963,4233,4235,4245,4247]
def ridgeSupport194_009 : List Nat := [4278,4279,4290,4291,4305,4307,4317,4319,4350,4351,4362,4363,4754,4755,4762,4763,5135,5137,5139,5141,5159,5161,5165,5167,5172,5173,5178,5179,5180,5181,5186,5187]
def ridgeSupport194_010 : List Nat := [5220,5221,5226,5227,5228,5229,5234,5235,5241,5243,5247,5249,5259,5260,5262,5263,5411,5413,5415,5417,5420,5421,5426,5427,5447,5449,5453,5455,5460,5461,5466,5467]
def ridgeSupport194_011 : List Nat := [5468,5469,5474,5475,5481,5483,5487,5489,5508,5509,5514,5515,5516,5517,5519,5520,5529,5531,5538,5539,5556,5557,5559,5561,5574,5575,5576,5578,5583,5585,5592,5593]
def ridgeSupport194_012 : List Nat := [5610,5611,5613,5615,5628,5629,5630,5632,5891,5893,5895,5897,5900,5901,5906,5907,5927,5929,5933,5935,5940,5941,5946,5947,5948,5949,5954,5955,5961,5963,5967,5969]
def ridgeSupport194_013 : List Nat := [5988,5989,5994,5995,5996,5997,5999,6000,6009,6011,6018,6019,6036,6037,6039,6041,6054,6055,6056,6058,6063,6065,6072,6073,6090,6091,6093,6095,6108,6109,6110,6112]
def ridgeSupport194_014 : List Nat := [6527,6529,6531,6533,6536,6537,6542,6543,6563,6565,6569,6571,6576,6577,6582,6583,6584,6585,6590,6591,6597,6599,6603,6605,6624,6625,6630,6631,6632,6633,6635,6636]
def ridgeSupport194_015 : List Nat := [6789,6791,6798,6799,6801,6803,6810,6811,6812,6814,6818,6820,6843,6845,6852,6853,6855,6857,6864,6865,6866,6868,6872,6874,7126,7127,7367,7369,7371,7373,7390,7392]
def ridgeSupport194_016 : List Nat := [7394,7396,7401,7403,7407,7409,7438,7440,7442,7444,7449,7451,7455,7457,7498,7500,7502,7504,7520,7522,7526,7528,7614,7615,7676,7677,7772,7773,7928,7929]
def ridgeSupport194_code : Nat := 0x3df3ef8f2ef973bfbdfcedff6fbad1d66eb17583aa1d4eea6752ba43d1fe8df467a29d12e88743b9e3cefe75f3a79c9ce2e70737b99bccbe64f31f7afbd6d6d6b635a9ad2d68eb43593ac7d62eb1357babbd526a8b53da9cd4dea6b527a91d47ea3b50fa85cf667af3d39e8cf3e79b3c39e0ce6e72f38f9c5cdfe6fb3739b8cdbe6db3639b0cd5e6a734b9a3cc7e63b313988cc2e60f30397fbf05f7afbb7dcbe7df36f977cabdcdee2f637afbd55ea2f4f7a6bccde5ef2b794bc1de0aef7779bb85dbeedb76cbb5ddaaecb764ba8dd3ee97749ba1dd0ae7b73cb9ddceae6b734b97dcb6e53727b89dc4ae1b70cb84dc1ee0b703b0057fabfb5fcaf7d7b6bd75eaaecd762ba35cfae55722b8f5c6adcd6deb6b5b4ad1d68ab37599ac8563eb1b58cac5d62ab0b584ab8d5bead7569ab1d58aabb55caadd56aaab554aa7d536a93547a99d4caa5b52ca94d49ea4b523a47d23a91948ba40d1fe8f7479a39d1ca8db46ca35d1aa8cb464a21d10a87b43ca1dd0ea86b434a17d0b6853427a0ad04e82340f94dca6a527292885c42a1ff0fe86fc3761a70d1861c30a16f0b684bc2561170897bdbde9eeaf747b1bd89ebaf5c7a0bcfde76f39799bcc9e5af2c795bca9e4af2478fbc75e32f17781bc09dfaefc769bb49d9aecc764bb1dd86ec15e2af11766bb25d2ae8d70eb855beadf16d6b6a5aead6d67eb3d595aca964ab24589ac4961ab0c578abbd5d6ae9571ab895baadc56dab695aaad4567ab35592ac7559aac955aaac541aa094faa7c53ca9dd4e6a71462a3111668b2452a28d10e88543ea1f10d686a42ea16d07e83d415a0a904a824409a04901a80c3f89fbcfd67e93f19f88fba7dc3ed9f68faa7d43e79f34f927c73d99ec8f5a7ac3c19e08efa77c3bc9ddcee677132d9968caa6543219908c7a63c314989cc4662130d9868c2a6142f597a8bca5e42f19788bba5dc2eb9754ba25cf2dd96e8b6a5b42c095fcaf65791b40d9c6ca3641b10d846be35e1ae8d706b43591950ca06463211900c7c63831b18d0c5462630e1860c2c6143071830c145ac2d41678b345982cb1640b1c58c2c115f8ae85702b715b0acc5642b113709b44d826b13509a447423811988c446022f11608ac454225111887843821b10d085c42c21508e0468232117089844822010c085841c20a10408103f81fa0fb07b83d816e0b605982c815e0ae03781b80d606a033819806c03501780a403e009
def ridgeSupport194_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport194_code
def ridgeSupport194_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport194_code
def ridgeSupport194_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport194_code
def ridgeSupport194_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport194_code
def ridgeSupport194_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport194_code
def ridgeSupport194_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport194_code
def ridgeSupport194_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport194_code
def ridgeSupport194_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport194_code
def ridgeSupport194_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport194_code
def ridgeSupport194_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport194_code
def ridgeSupport194_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport194_code
def ridgeSupport194_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport194_code
def ridgeSupport194_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport194_code
def ridgeSupport194_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport194_code
def ridgeSupport194_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport194_code
def ridgeSupport194_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport194_code
def ridgeSupport194_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport194_code
def ridgeSupport194_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport194_code
def ridgeSupport194_suffix_017 : List Nat := []
def ridgeSupport194_suffix_016 : List Nat := ridgeSupport194_016 ++ ridgeSupport194_suffix_017
def ridgeSupport194_suffix_015 : List Nat := ridgeSupport194_015 ++ ridgeSupport194_suffix_016
def ridgeSupport194_suffix_014 : List Nat := ridgeSupport194_014 ++ ridgeSupport194_suffix_015
def ridgeSupport194_suffix_013 : List Nat := ridgeSupport194_013 ++ ridgeSupport194_suffix_014
def ridgeSupport194_suffix_012 : List Nat := ridgeSupport194_012 ++ ridgeSupport194_suffix_013
def ridgeSupport194_suffix_011 : List Nat := ridgeSupport194_011 ++ ridgeSupport194_suffix_012
def ridgeSupport194_suffix_010 : List Nat := ridgeSupport194_010 ++ ridgeSupport194_suffix_011
def ridgeSupport194_suffix_009 : List Nat := ridgeSupport194_009 ++ ridgeSupport194_suffix_010
def ridgeSupport194_suffix_008 : List Nat := ridgeSupport194_008 ++ ridgeSupport194_suffix_009
def ridgeSupport194_suffix_007 : List Nat := ridgeSupport194_007 ++ ridgeSupport194_suffix_008
def ridgeSupport194_suffix_006 : List Nat := ridgeSupport194_006 ++ ridgeSupport194_suffix_007
def ridgeSupport194_suffix_005 : List Nat := ridgeSupport194_005 ++ ridgeSupport194_suffix_006
def ridgeSupport194_suffix_004 : List Nat := ridgeSupport194_004 ++ ridgeSupport194_suffix_005
def ridgeSupport194_suffix_003 : List Nat := ridgeSupport194_003 ++ ridgeSupport194_suffix_004
def ridgeSupport194_suffix_002 : List Nat := ridgeSupport194_002 ++ ridgeSupport194_suffix_003
def ridgeSupport194_suffix_001 : List Nat := ridgeSupport194_001 ++ ridgeSupport194_suffix_002
def ridgeSupport194_suffix_000 : List Nat := ridgeSupport194_000 ++ ridgeSupport194_suffix_001
theorem ridgeSupport194_source : candidateSupports 194 =
    (PackedRawNatGrowth.readList 13 542 ridgeSupport194_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
