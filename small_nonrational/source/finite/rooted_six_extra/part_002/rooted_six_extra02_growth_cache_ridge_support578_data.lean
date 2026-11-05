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
def ridgeSupport578_000 : List Nat := [11,33,43,49,54,55,126,127,130,131,134,135,198,199,202,203,206,207,267,269,271,273,275,280,281,283,286,288,290,292,294,296]
def ridgeSupport578_001 : List Nat := [301,302,304,307,553,555,557,558,560,562,563,567,572,574,576,578,579,581,583,584,588,593,641,642,643,644,645,646,709,711,713,714]
def ridgeSupport578_002 : List Nat := [716,718,719,723,728,730,732,734,735,737,739,740,744,749,793,795,797,798,800,802,803,807,812,814,816,818,819,821,823,824,828,833]
def ridgeSupport578_003 : List Nat := [856,857,859,860,863,864,865,867,868,870,877,878,1394,1399,1400,1405,1464,1465,1478,1479,1484,1486,1492,1493,1498,1499,1505,1507,1512,1513,1526,1527]
def ridgeSupport578_004 : List Nat := [1560,1561,1562,1567,1568,1573,1574,1575,1588,1589,1594,1595,1612,1613,1618,1619,1898,1903,1904,1909,1920,1921,1934,1935,1968,1969,1982,1983,1988,1990,1996,1997]
def ridgeSupport578_005 : List Nat := [2002,2003,2009,2011,2016,2017,2018,2023,2024,2029,2030,2031,2064,2065,2078,2079,2088,2089,2102,2103,2180,2185,2210,2215,2224,2225,2242,2243,2252,2257,2282,2287]
def ridgeSupport578_006 : List Nat := [2296,2297,2314,2315,2666,2671,2672,2677,2688,2689,2702,2703,2736,2737,2750,2751,2756,2758,2764,2765,2770,2771,2777,2779,2784,2785,2786,2791,2792,2797,2798,2799]
def ridgeSupport578_007 : List Nat := [2832,2833,2846,2847,2856,2857,2870,2871,2948,2953,2978,2983,2992,2993,3010,3011,3020,3025,3050,3055,3064,3065,3082,3083,3770,3775,3776,3781,3792,3793,3806,3807]
def ridgeSupport578_008 : List Nat := [3840,3841,3854,3855,3860,3862,3868,3869,3874,3875,3881,3883,3888,3889,3890,3895,3896,3901,3902,3903,3936,3937,3950,3951,3960,3961,3974,3975,4304,4309,4316,4321]
def ridgeSupport578_009 : List Nat := [4348,4349,4360,4361,4376,4381,4388,4393,4420,4421,4432,4433,4786,4787,4794,4795,5132,5134,5141,5143,5157,5159,5164,5166,5174,5179,5180,5185,5205,5207,5212,5214]
def ridgeSupport578_010 : List Nat := [5222,5227,5228,5233,5265,5267,5272,5274,5295,5298,5301,5304,5378,5379,5448,5449,5544,5545,5700,5701,5856,5857,5870,5871,5880,5881,5883,5884,5885,5887,5948,5950]
def ridgeSupport578_011 : List Nat := [5969,5971,5988,5989,5991,5992,5993,5995,6021,6022,6023,6024,6039,6040,6041,6042,6116,6118,6137,6139,6156,6157,6159,6160,6161,6163,6189,6190,6191,6192,6207,6208]
def ridgeSupport578_012 : List Nat := [6209,6210,6332,6334,6353,6355,6372,6373,6375,6376,6377,6379,6459,6460,6461,6462,6477,6478,6479,6480]
def ridgeSupport578_code : Nat := 0xca8653f29d94dc9f64f727993bc75e3a71d18e7c72e3931a78d1c5f62f3085841c2060ff06182fc1760b7027811c08603f01b80cbfddfe6fcd7e4bcd5e66f31797bc45e1ef0d785bb5dda6ed1767bb2dd92ea7751b9f5cf2dff6fdb7e5beedf36f8b77dbbadc36e0b22d912b535a8aa4d522a07502a5c52d69654afa4d5262927491a38d1b28d7466a2f51728af455a20d0f2877436a1750b284f425a0bd05681d40c95dcaea5672b28a8c54228b144894c49223b118884c4221fb0fc870c3721ab0d07c3be19ef2f787b7bdb9ec2f6079fbcf9e7af3879bbcc9e62f30795bca5e46f2278ebc71e2cf14787bc39e02f0076fbb79da2ed0762bb01d7eeba605b0297f2bf85f7afa97a2bcc5e1af09762bb05d3ae89712b8459bacd9652b2858fac79622b10577abb95daae8573ab895c2ae056dab655a6ad2566ab3158cac455faaf9562ab0547aa39502a8053aa9c14dea6a485a4291f28f8477a3a91a28cc461a3091628b0453a28911288441ba0d905282840fa0790228103f79fb8fda7e83f39f88fc27e03ed9f64fa67d23e69f30f8c7c43df9ef8f627b03c79e38f027803ba9dc0ede76a3299948c9a64c31d98e8c6a6343139898c4a62030f9868c326182fb97d8bd25e82f19784bb65da2ea9750b9c5cc2e39718b725b82be95e0aee5721b70db46cc3641b18d846c035f1ae0d6c6b23581a08cf067033719a8ccc6643301970cb064e3231910c8063c31d18d8c645da2e81720b8c5c22df16f0b705b42d81698b3c59c2cc1650b2458e2c51430a145082831410a044a224c124091c48a243121090047c23c11b88cc46423011708b445622909984c025c12d0940498248122090047823611908c044c22210f086842c19e0ce065832818e0c6043821810608203f81f806e03601880ac04200b
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
def ridgeSupport578_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport578_code
def ridgeSupport578_suffix_013 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport578_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
