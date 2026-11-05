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
def ridgeSupport578_000 : List Nat := [11,33,43,49,54,55,126,127,130,131,134,135,198,199,202,203,206,207,267,269,271,273,275,280,281,283,286,288,290,292,294,296]
def ridgeSupport578_001 : List Nat := [301,302,304,307,553,555,557,558,560,562,563,567,572,574,576,578,579,581,583,584,588,593,641,642,643,644,645,646,709,711,713,714]
def ridgeSupport578_002 : List Nat := [716,718,719,723,728,730,732,734,735,737,739,740,744,749,793,795,797,798,800,802,803,807,812,814,816,818,819,821,823,824,828,833]
def ridgeSupport578_003 : List Nat := [856,857,859,860,863,864,865,867,868,870,877,878,1394,1399,1400,1405,1464,1465,1478,1479,1484,1486,1492,1493,1498,1499,1505,1507,1512,1513,1526,1527]
def ridgeSupport578_004 : List Nat := [1560,1561,1562,1567,1568,1573,1574,1575,1588,1589,1594,1595,1612,1613,1618,1619,1898,1903,1904,1909,1920,1921,1934,1935,1968,1969,1982,1983,1988,1990,1996,1997]
def ridgeSupport578_005 : List Nat := [2002,2003,2009,2011,2016,2017,2018,2023,2024,2029,2030,2031,2064,2065,2078,2079,2088,2089,2102,2103,2180,2185,2210,2215,2224,2225,2242,2243,2252,2257,2282,2287]
def ridgeSupport578_006 : List Nat := [2296,2297,2314,2315,2666,2671,2672,2677,2688,2689,2702,2703,2736,2737,2750,2751,2756,2758,2764,2765,2770,2771,2777,2779,2784,2785,2786,2791,2792,2797,2798,2799]
def ridgeSupport578_007 : List Nat := [2832,2833,2846,2847,2856,2857,2870,2871,2948,2953,2978,2983,2992,2993,3010,3011,3020,3025,3050,3055,3064,3065,3082,3083,3770,3775,3776,3781,3792,3793,3806,3807]
def ridgeSupport578_008 : List Nat := [3840,3841,3854,3855,3860,3862,3868,3869,3874,3875,3881,3883,3888,3889,3890,3895,3896,3901,3902,3903,3936,3937,3950,3951,3960,3961,3974,3975,4304,4309,4316,4321]
def ridgeSupport578_009 : List Nat := [4348,4349,4360,4361,4376,4381,4388,4393,4420,4421,4432,4433,4786,4787,4794,4795,5132,5134,5141,5143,5156,5158,5164,5165,5170,5171,5177,5179,5184,5185,5198,5199]
def ridgeSupport578_010 : List Nat := [5212,5213,5218,5219,5232,5233,5234,5239,5240,5245,5246,5247,5255,5257,5258,5260,5408,5410,5417,5419,5424,5425,5438,5439,5444,5446,5452,5453,5458,5459,5465,5467]
def ridgeSupport578_011 : List Nat := [5472,5473,5474,5479,5480,5485,5486,5487,5500,5501,5506,5507,5517,5518,5525,5526,5582,5587,5590,5591,5608,5609,5612,5617,5626,5627,5631,5634,5636,5641,5644,5645]
def ridgeSupport578_012 : List Nat := [5662,5663,5666,5671,5680,5681,5685,5688,5888,5890,5897,5899,5904,5905,5918,5919,5924,5926,5932,5933,5938,5939,5945,5947,5952,5953,5954,5959,5960,5965,5966,5967]
def ridgeSupport578_013 : List Nat := [5980,5981,5986,5987,5997,5998,6005,6006,6062,6067,6070,6071,6088,6089,6092,6097,6106,6107,6111,6114,6116,6121,6124,6125,6142,6143,6146,6151,6160,6161,6165,6168]
def ridgeSupport578_014 : List Nat := [6524,6526,6533,6535,6540,6541,6554,6555,6560,6562,6568,6569,6574,6575,6581,6583,6588,6589,6590,6595,6596,6601,6602,6603,6616,6617,6622,6623,6633,6634,6641,6642]
def ridgeSupport578_015 : List Nat := [6842,6847,6850,6851,6854,6859,6862,6863,6867,6870,6873,6876,6896,6901,6904,6905,6908,6913,6916,6917,6921,6924,6927,6930,7134,7135,7364,7366,7373,7375,7389,7391]
def ridgeSupport578_016 : List Nat := [7396,7398,7406,7411,7412,7417,7437,7439,7444,7446,7454,7459,7460,7465,7497,7499,7504,7506,7527,7530,7533,7536,7610,7611,7680,7681,7776,7777,7932,7933]
def ridgeSupport578_code : Nat := 0x3dfbefcf30f983c03e00eddf6ebae1d6deb5759faa5d50ea5f527a53d24e91f47ba2dd14e87f4379f3cf4e79f3bb9cdce4e6ff37799fccde6373137bfbded896c3f619b09d82ec13603afcd7cebe35ebaf0d6e6b675adad3d67eb3b597ac6d61eb0b57fabacf967c73d59e9cefe77b3b39d8ce5e72b3939c4ce1e6fb37b9bccdbe6d735f9aecd4e6a33459a0ccde66b31b98ccc3e6172fd97cc0c6057023810c03e00afff7febf6dfb2fd37e4bf15f7efb77dabe8df32f937c8bdbdedaf677aebbb5dd6edd76dbb1dd8aebb75cba7dd3ae9b748ba3dd0ae83740b9ddce6e67732b96dcb2e4d724b8fdc7ae23710b85dc26e05700b1c58d6c63630b13d88ac3f61eb06d832c13604b0157febf75faaf8d7b2bd35e8aebd75aba75ceacb5656b1d58dac1d60aafb57cab7d5baadb568ab3d58aac3560aadd566aa7552aa6d532a8d544a9fd4faa63530a95d4a6a45520a46522a913487a3fd1fa8fb478a3bd1ca8e3470a31d18a8bb45ca27d13a883440a1dd0e6867432a16d0b284d424a0bd05681d40c95dcaea5672b28a8c54228b144894c49223b118884c4221fb0fc870c3721ab0d07c3be19ef2f787b7bdb9ec2f6079fbcf9e7af3879bbcc9e62f30795bca5e46f2278ebc71e2cf14787bc39e02f0076fbb79da2ed0762bb01d7eeba605b0297f2bf85f7afa97a2bcc5e1af09762bb05d3ae89712b8459bacd9652b2858fac79622b10577abb95daae8573ab895c2ae056dab655a6ad2566ab3158cac455faaf9562ab0547aa39502a8053aa9c14dea6a485a4291f28f8477a3a91a28cc461a3091628b0453a28911288441ba0d905282840fa0790228103f79fb8fda7e83f39f88fc27e03ed9f64fa67d23e69f30f8c7c43df9ef8f627b03c79e38f027803ba9dc0ede76a3299948c9a64c31d98e8c6a6343139898c4a62030f9868c326182fb97d8bd25e82f19784bb65da2ea9750b9c5cc2e39718b725b82be95e0aee5721b70db46cc3641b18d846c035f1ae0d6c6b23581a08cf067033719a8ccc6643301970cb064e3231910c8063c31d18d8c645da2e81720b8c5c22df16f0b705b42d81698b3c59c2cc1650b2458e2c51430a145082831410a044a224c124091c48a243121090047c23c11b88cc46423011708b445622909984c025c12d0940498248122090047823611908c044c22210f086842c19e0ce065832818e0c6043821810608203f81f806e03601880ac04200b
def ridgeSupport578_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport578_code
def ridgeSupport578_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport578_code
def ridgeSupport578_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport578_code
def ridgeSupport578_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport578_code
def ridgeSupport578_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport578_code
def ridgeSupport578_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport578_code
def ridgeSupport578_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport578_code
def ridgeSupport578_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport578_code
def ridgeSupport578_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport578_code
def ridgeSupport578_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport578_code
def ridgeSupport578_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport578_code
def ridgeSupport578_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport578_code
def ridgeSupport578_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport578_code
def ridgeSupport578_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport578_code
def ridgeSupport578_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport578_code
def ridgeSupport578_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport578_code
def ridgeSupport578_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport578_code
def ridgeSupport578_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport578_code
def ridgeSupport578_suffix_017 : List Nat := []
def ridgeSupport578_suffix_016 : List Nat := ridgeSupport578_016 ++ ridgeSupport578_suffix_017
def ridgeSupport578_suffix_015 : List Nat := ridgeSupport578_015 ++ ridgeSupport578_suffix_016
def ridgeSupport578_suffix_014 : List Nat := ridgeSupport578_014 ++ ridgeSupport578_suffix_015
def ridgeSupport578_suffix_013 : List Nat := ridgeSupport578_013 ++ ridgeSupport578_suffix_014
def ridgeSupport578_suffix_012 : List Nat := ridgeSupport578_012 ++ ridgeSupport578_suffix_013
def ridgeSupport578_suffix_011 : List Nat := ridgeSupport578_011 ++ ridgeSupport578_suffix_012
def ridgeSupport578_suffix_010 : List Nat := ridgeSupport578_010 ++ ridgeSupport578_suffix_011
def ridgeSupport578_suffix_009 : List Nat := ridgeSupport578_009 ++ ridgeSupport578_suffix_010
def ridgeSupport578_suffix_008 : List Nat := ridgeSupport578_008 ++ ridgeSupport578_suffix_009
def ridgeSupport578_suffix_007 : List Nat := ridgeSupport578_007 ++ ridgeSupport578_suffix_008
def ridgeSupport578_suffix_006 : List Nat := ridgeSupport578_006 ++ ridgeSupport578_suffix_007
def ridgeSupport578_suffix_005 : List Nat := ridgeSupport578_005 ++ ridgeSupport578_suffix_006
def ridgeSupport578_suffix_004 : List Nat := ridgeSupport578_004 ++ ridgeSupport578_suffix_005
def ridgeSupport578_suffix_003 : List Nat := ridgeSupport578_003 ++ ridgeSupport578_suffix_004
def ridgeSupport578_suffix_002 : List Nat := ridgeSupport578_002 ++ ridgeSupport578_suffix_003
def ridgeSupport578_suffix_001 : List Nat := ridgeSupport578_001 ++ ridgeSupport578_suffix_002
def ridgeSupport578_suffix_000 : List Nat := ridgeSupport578_000 ++ ridgeSupport578_suffix_001
theorem ridgeSupport578_source : candidateSupports 578 =
    (PackedRawNatGrowth.readList 13 542 ridgeSupport578_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
