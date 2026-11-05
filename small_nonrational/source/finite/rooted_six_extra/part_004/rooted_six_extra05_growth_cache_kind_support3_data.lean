module
prelude
public import RootedSixExtra05GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [94,95,96,97,98,99,106,107,108,109,110,111,118,119,120,121,122,123,130,131,132,133,134,135,142,143,144,145,146,147,154,155]
def kindSupport3_001 : List Nat := [156,157,158,159,160,161,162,163,173,174,175,176,177,178,179,180,181,182,183,184,194,195,196,197,198,199,200,201,202,203,204,205]
def kindSupport3_002 : List Nat := [215,216,217,218,219,220,221,222,223,224,225,226,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,261,262,263,264]
def kindSupport3_003 : List Nat := [265,266,267,268,269,270,271,272,282,283,284,285,286,287,288,289,290,291,292,293,303,304,305,306,307,308,309,310,311,312,313,314]
def kindSupport3_004 : List Nat := [324,325,326,327,328,329,330,331,332,333,334,335,345,346,347,348,349,350,351,352,353,354,355,356,366,367,368,369,370,371,372,373]
def kindSupport3_005 : List Nat := [374,375,376,377,387,388,389,390,391,392,393,394,395,396,397,398,408,409,410,411,412,413,414,415,416,417,418,419,430,431,432,433]
def kindSupport3_006 : List Nat := [434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,458,459,460,461,462,463,464,465,466,467,468,469,479,480,481,482,483]
def kindSupport3_007 : List Nat := [484,485,486,487,488,489,490,500,501,502,503,504,505,506,507,508,509,510,511,521,522,523,524,525,526,527,528,529,530,531,532,542]
def kindSupport3_008 : List Nat := [543,544,545,546,547,548,549,550,551,552,553,563,564,565,566,567,568,569,570,571,572,573,574,584,585,586,587,588,589,590,591,592]
def kindSupport3_009 : List Nat := [593,594,595,605,606,607,608,609,610,611,612,613,614,615,616,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,651,652]
def kindSupport3_010 : List Nat := [653,654,655,656,657,658,659,660,661,662,672,673,674,675,676,677,678,679,680,681,682,683,693,694,695,696,697,698,699,700,701,702]
def kindSupport3_011 : List Nat := [703,704,714,715,716,717,718,719,720,721,722,723,724,725,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,757,758,759]
def kindSupport3_012 : List Nat := [760,761,762,769,770,771,772,773,774,781,782,783,784,785,786,793,794,795,796,797,798,805,806,807,808,809,810,817,818,819,820,821]
def kindSupport3_013 : List Nat := [822,832,833,834,835,836,837,838,839,840,841,842,843,853,854,855,856,857,858,859,860,861,862,863,864,874,875,876,877,878,879,880]
def kindSupport3_014 : List Nat := [881,882,883,884,885,895,896,897,898,899,900,901,902,903,904,905,906,916,917,918,919,920,921,922,923,924,925,926,927,937,938,939]
def kindSupport3_015 : List Nat := [940,941,942,943,944,945,946,947,948,958,959,960,961,962,963,964,965,966,967,968,969,979,980,981,982,983,984,985,986,987,988,989]
def kindSupport3_016 : List Nat := [990,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1046,1047,1048,1049]
def kindSupport3_017 : List Nat := [1050,1051,1052,1053,1054,1055,1056,1057,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099]
def kindSupport3_018 : List Nat := [1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149]
def kindSupport3_code : Nat := 0x47d47c47b47a47947847747647547447347247147046f46446346246146045f45e45d45c45b45a45945845745644b44a44944844744644544444344244144043643543443343243143042f42e42d42c42b42142041f41e41d41c41b41a41941841741640c40b40a4094084074064054044034024013f73f63f53f43f33f23f13f03ef3ee3ed3ec3eb3ea3e93de3dd3dc3db3da3d93d83d73d63d53d43d33c93c83c73c63c53c43c33c23c13c03bf3be3b43b33b23b13b03af3ae3ad3ac3ab3aa3a939f39e39d39c39b39a39939839739639539438a38938838738638538438338238138037f37537437337237137036f36e36d36c36b36a36035f35e35d35c35b35a35935835735635534b34a34934834734634534434334234134033633533433333233132a32932832732632531e31d31c31b31a31931231131030f30e30d3063053043033023012fa2f92f82f72f62f52ee2ed2ec2eb2ea2e92e82e72e62e52e42e32e22e12e02d52d42d32d22d12d02cf2ce2cd2cc2cb2ca2c02bf2be2bd2bc2bb2ba2b92b82b72b62b52ab2aa2a92a82a72a62a52a42a32a22a12a029629529429329229129028f28e28d28c28b28128027f27e27d27c27b27a27927827727627527427326826726626526426326226126025f25e25d25325225125024f24e24d24c24b24a24924823e23d23c23b23a23923823723623523423322922822722622522422322222122021f21e21421321221121020f20e20d20c20b20a2091ff1fe1fd1fc1fb1fa1f91f81f71f61f51f41ea1e91e81e71e61e51e41e31e21e11e01df1d51d41d31d21d11d01cf1ce1cd1cc1cb1ca1c01bf1be1bd1bc1bb1ba1b91b81b71b61b51b41b31b21b11b01af1ae1a31a21a11a019f19e19d19c19b19a19919818e18d18c18b18a18918818718618518418317917817717617517417317217117016f16e16416316216116015f15e15d15c15b15a15914f14e14d14c14b14a14914814714614514413a13913813713613513413313213113012f12512412312212112011f11e11d11c11b11a11010f10e10d10c10b10a1091081071061050fb0fa0f90f80f70f60f50f40f30f20f10f00ef0ee0ed0ec0e20e10e00df0de0dd0dc0db0da0d90d80d70cd0cc0cb0ca0c90c80c70c60c50c40c30c20b80b70b60b50b40b30b20b10b00af0ae0ad0a30a20a10a009f09e09d09c09b09a09309209109008f08e08708608508408308207b07a07907807707606f06e06d06c06b06a06306206106005f05e
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport3_code
def kindSupport3_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport3_code
def kindSupport3_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport3_code
def kindSupport3_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport3_code
def kindSupport3_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport3_code
def kindSupport3_rest_015 : Nat := PackedRawNatGrowth.drop 5760 kindSupport3_code
def kindSupport3_rest_016 : Nat := PackedRawNatGrowth.drop 6144 kindSupport3_code
def kindSupport3_rest_017 : Nat := PackedRawNatGrowth.drop 6528 kindSupport3_code
def kindSupport3_rest_018 : Nat := PackedRawNatGrowth.drop 6912 kindSupport3_code
def kindSupport3_rest_019 : Nat := PackedRawNatGrowth.drop 7272 kindSupport3_code
def kindSupport3_suffix_019 : List Nat := []
def kindSupport3_suffix_018 : List Nat := kindSupport3_018 ++ kindSupport3_suffix_019
def kindSupport3_suffix_017 : List Nat := kindSupport3_017 ++ kindSupport3_suffix_018
def kindSupport3_suffix_016 : List Nat := kindSupport3_016 ++ kindSupport3_suffix_017
def kindSupport3_suffix_015 : List Nat := kindSupport3_015 ++ kindSupport3_suffix_016
def kindSupport3_suffix_014 : List Nat := kindSupport3_014 ++ kindSupport3_suffix_015
def kindSupport3_suffix_013 : List Nat := kindSupport3_013 ++ kindSupport3_suffix_014
def kindSupport3_suffix_012 : List Nat := kindSupport3_012 ++ kindSupport3_suffix_013
def kindSupport3_suffix_011 : List Nat := kindSupport3_011 ++ kindSupport3_suffix_012
def kindSupport3_suffix_010 : List Nat := kindSupport3_010 ++ kindSupport3_suffix_011
def kindSupport3_suffix_009 : List Nat := kindSupport3_009 ++ kindSupport3_suffix_010
def kindSupport3_suffix_008 : List Nat := kindSupport3_008 ++ kindSupport3_suffix_009
def kindSupport3_suffix_007 : List Nat := kindSupport3_007 ++ kindSupport3_suffix_008
def kindSupport3_suffix_006 : List Nat := kindSupport3_006 ++ kindSupport3_suffix_007
def kindSupport3_suffix_005 : List Nat := kindSupport3_005 ++ kindSupport3_suffix_006
def kindSupport3_suffix_004 : List Nat := kindSupport3_004 ++ kindSupport3_suffix_005
def kindSupport3_suffix_003 : List Nat := kindSupport3_003 ++ kindSupport3_suffix_004
def kindSupport3_suffix_002 : List Nat := kindSupport3_002 ++ kindSupport3_suffix_003
def kindSupport3_suffix_001 : List Nat := kindSupport3_001 ++ kindSupport3_suffix_002
def kindSupport3_suffix_000 : List Nat := kindSupport3_000 ++ kindSupport3_suffix_001
theorem kindSupport3_source : kindSupports 3 =
    (PackedRawNatGrowth.readList 12 606 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
