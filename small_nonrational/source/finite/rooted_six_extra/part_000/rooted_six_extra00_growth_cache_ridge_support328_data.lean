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
def ridgeSupport328_000 : List Nat := [26,50,70,100,106,111,113,214,215,216,217,224,225,370,371,372,373,380,381,514,516,518,520,522,527,528,530,533,556,557,561,563]
def ridgeSupport328_001 : List Nat := [564,568,570,571,573,791,792,795,796,799,800,851,853,855,857,859,864,865,867,870,893,894,898,900,901,905,907,908,910,1056,1057,1060]
def ridgeSupport328_002 : List Nat := [1061,1064,1065,1116,1118,1120,1122,1124,1129,1130,1132,1135,1158,1159,1163,1165,1166,1170,1172,1173,1175,1479,1480,1481,1482,1483,1484,1538,1540,1542,1543,1545]
def ridgeSupport328_003 : List Nat := [1547,1548,1552,1557,1581,1582,1583,1586,1587,1588,1590,1595,1597,1622,1624,1626,1627,1629,1631,1632,1636,1641,1665,1666,1667,1670,1671,1672,1674,1679,1681,1706]
def ridgeSupport328_004 : List Nat := [1708,1709,1711,1712,1714,1716,1717,1719,1720,1724,1725,2879,2881,2890,2895,2946,2947,2956,2957,2969,2972,2978,2979,2983,2985,2988,2989,2994,2995,3004,3005,3042]
def ridgeSupport328_005 : List Nat := [3043,3047,3049,3052,3053,3058,3063,3074,3075,3084,3085,3098,3099,3108,3109,3119,3121,3130,3135,3186,3187,3196,3197,3209,3212,3218,3219,3223,3225,3228,3229,3234]
def ridgeSupport328_006 : List Nat := [3235,3244,3245,3282,3283,3287,3289,3292,3293,3298,3303,3314,3315,3324,3325,3338,3339,3348,3349,3358,3363,3370,3375,3390,3391,3402,3403,3503,3505,3515,3517,3536]
def ridgeSupport328_007 : List Nat := [3537,3548,3549,3647,3649,3658,3663,3714,3715,3724,3725,3737,3740,3746,3747,3751,3753,3756,3757,3762,3763,3772,3773,3810,3811,3815,3817,3820,3821,3826,3831,3842]
def ridgeSupport328_008 : List Nat := [3843,3852,3853,3866,3867,3876,3877,3886,3891,3898,3903,3918,3919,3930,3931,4031,4033,4043,4045,4064,4065,4076,4077,4967,4969,4978,4983,4986,4987,4996,4997,5034]
def ridgeSupport328_009 : List Nat := [5035,5044,5045,5057,5060,5066,5067,5071,5073,5076,5077,5082,5083,5087,5089,5092,5093,5098,5103,5130,5131,5140,5141,5154,5155,5164,5165,5176,5181,5206,5211,5220]
def ridgeSupport328_010 : List Nat := [5221,5238,5239,5321,5323,5351,5353,5366,5367,5384,5385,5735,5737,5746,5751,5754,5755,5764,5765,5802,5803,5812,5813,5825,5828,5834,5835,5839,5841,5844,5845,5850]
def ridgeSupport328_011 : List Nat := [5851,5855,5857,5860,5861,5866,5871,5898,5899,5908,5909,5922,5923,5932,5933,5944,5949,5974,5979,5988,5989,6006,6007,6089,6091,6119,6121,6134,6135,6152,6153,6772]
def ridgeSupport328_012 : List Nat := [6777,6784,6789,6816,6817,6828,6829,6917,6919,6929,6931,6962,6963,6974,6975,7212,7213,7248,7249,7308,7309,7458,7459,7554,7555,7890,7891,7900,7901,7914,7915,7918]
def ridgeSupport328_013 : List Nat := [7920,7921,7922,7938,7939,7948,7949,7962,7963,7966,7968,7969,7970,7985,7986,7987,7988,8020,8022,8024,8025,8058,8059,8068,8069,8082,8083,8086,8088,8089,8090,8105]
def ridgeSupport328_014 : List Nat := [8106,8107,8108,8140,8142,8144,8145,8345,8348,8359,8361,8382,8383,8386,8388,8389,8390,8399,8400,8401,8402,8434,8436,8438,8439,8513,8516,8527,8529,8550,8551,8554]
def ridgeSupport328_015 : List Nat := [8556,8557,8558,8567,8568,8569,8570,8602,8604,8606,8607,8765,8766,8767,8768,8800,8802,8804,8805]
def ridgeSupport328_code : Nat := 0x22658992262898224088fe23e88f619f867a19c866a17a85e617885de16e85b616c85aa167859a151853e14485060f783da0f483ca0d283460d0833e0c683160c4830a0bf82fa0a9829e09c8265fd17f41fce7f31fac7eadfaa7ea5f9a7e65f987e59f937e49f857e11f7b7de9f597d61f567d51f347ccdf327cc5f227c85f207c79f1b7c69f0d7c31f037c09ef27bc5ef07bb9eeb7ba9edd7b71ed37b49d837609d237489c8d7231c517141c2d70b1b3f6cf9b336cc9b136c45b076c15aad6ab1aa16a81a856a01a7969d180960217f75fd97e95f9d7cb5f257775dd97655d9175b5d5973d5ce172d5cb17235c897155c5170b5c296ef5ba96e55b916e15b7d6db5b696d55b516d15b3d6cb5b296c45b056b55ad16ab5aa96855a1167b59e967759c9669599d50954214f753d94e9539d4cb532547751d9465519145b515943d50e142d50b14235089415505140b50293ef4fa93e54f913e14f7d3db4f693d54f513d14f3d3cb4f293c44f053b54ed13ab4ea93854e1137b4de93774dc93694d9cfed3fb0fe13f80fcd3f2cfc13efcf5b3d68f4f3d38f3f3ce8f333cb8f253c90f1b3c68f0d3c30f033c08ef73bc8eed3bb0ee93b9cee33b88ebd3af0eb33ac8ead3ab0ea93a9cea33a88e9c3a64e8d3a30e833a08e4f3928e4138fcddd3770dd13740dbd36ecdb136bcd4b3528d3f34f8d2f34a8d233478d153450d0b3428cfd33f0cf333c8ce73388cdd3370cd9335ccd33348cad32b0ca33288c9d3270c99325cc933248c8c3224c7d31f0c7331c8c3f30e8c3130bcc253090c1b3068c0d3030c033008bf72fc8bed2fb0be92f9cbe32f88bbd2ef0bb32ec8bad2eb0ba92e9cba32e88b9c2e64b8d2e30b832e08b4f2d28b412cfc6bd1af06b81adc6b51ad06b21ac06af1ab46ac1aa86911a3c68a1a206871a186831a0868119a4664198065f197465b1968658195863d18ec63618d063318c862f18b862d1854610183060b1824607181860418085cc172c5ca17245c8171c4971254494124848e123448b121c48611bc46c11a84691190462118045e117042910a04251090421108038e0e3038b0e243850e103820df837d0d983630d843600d6c3590d5c3550d4c3200c7c31c0c6c3180c5c23d08ec23a08e023408cc23108b422c0854212084020f08282080818204080817d05f017505d017305c80e103800d903600d7035807101bc06a019004600c801a
def ridgeSupport328_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport328_code
def ridgeSupport328_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport328_code
def ridgeSupport328_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport328_code
def ridgeSupport328_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport328_code
def ridgeSupport328_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport328_code
def ridgeSupport328_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport328_code
def ridgeSupport328_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport328_code
def ridgeSupport328_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport328_code
def ridgeSupport328_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport328_code
def ridgeSupport328_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport328_code
def ridgeSupport328_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport328_code
def ridgeSupport328_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport328_code
def ridgeSupport328_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport328_code
def ridgeSupport328_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport328_code
def ridgeSupport328_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport328_code
def ridgeSupport328_rest_015 : Nat := PackedRawNatGrowth.drop 6720 ridgeSupport328_code
def ridgeSupport328_rest_016 : Nat := PackedRawNatGrowth.drop 6986 ridgeSupport328_code
def ridgeSupport328_suffix_016 : List Nat := []
def ridgeSupport328_suffix_015 : List Nat := ridgeSupport328_015 ++ ridgeSupport328_suffix_016
def ridgeSupport328_suffix_014 : List Nat := ridgeSupport328_014 ++ ridgeSupport328_suffix_015
def ridgeSupport328_suffix_013 : List Nat := ridgeSupport328_013 ++ ridgeSupport328_suffix_014
def ridgeSupport328_suffix_012 : List Nat := ridgeSupport328_012 ++ ridgeSupport328_suffix_013
def ridgeSupport328_suffix_011 : List Nat := ridgeSupport328_011 ++ ridgeSupport328_suffix_012
def ridgeSupport328_suffix_010 : List Nat := ridgeSupport328_010 ++ ridgeSupport328_suffix_011
def ridgeSupport328_suffix_009 : List Nat := ridgeSupport328_009 ++ ridgeSupport328_suffix_010
def ridgeSupport328_suffix_008 : List Nat := ridgeSupport328_008 ++ ridgeSupport328_suffix_009
def ridgeSupport328_suffix_007 : List Nat := ridgeSupport328_007 ++ ridgeSupport328_suffix_008
def ridgeSupport328_suffix_006 : List Nat := ridgeSupport328_006 ++ ridgeSupport328_suffix_007
def ridgeSupport328_suffix_005 : List Nat := ridgeSupport328_005 ++ ridgeSupport328_suffix_006
def ridgeSupport328_suffix_004 : List Nat := ridgeSupport328_004 ++ ridgeSupport328_suffix_005
def ridgeSupport328_suffix_003 : List Nat := ridgeSupport328_003 ++ ridgeSupport328_suffix_004
def ridgeSupport328_suffix_002 : List Nat := ridgeSupport328_002 ++ ridgeSupport328_suffix_003
def ridgeSupport328_suffix_001 : List Nat := ridgeSupport328_001 ++ ridgeSupport328_suffix_002
def ridgeSupport328_suffix_000 : List Nat := ridgeSupport328_000 ++ ridgeSupport328_suffix_001
theorem ridgeSupport328_source : candidateSupports 328 =
    (PackedRawNatGrowth.readList 14 499 ridgeSupport328_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
