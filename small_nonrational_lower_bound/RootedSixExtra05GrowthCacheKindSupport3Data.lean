module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_kindSupport_code_3 3
cert_kindSupport_rest_4 3 000 0
cert_kindSupport_rest_4 3 001 384
cert_kindSupport_rest_4 3 002 768
cert_kindSupport_rest_4 3 003 1152
cert_kindSupport_rest_4 3 004 1536
cert_kindSupport_rest_4 3 005 1920
cert_kindSupport_rest_4 3 006 2304
cert_kindSupport_rest_4 3 007 2688
cert_kindSupport_rest_4 3 008 3072
cert_kindSupport_rest_4 3 009 3456
cert_kindSupport_rest_4 3 010 3840
cert_kindSupport_rest_4 3 011 4224
cert_kindSupport_rest_4 3 012 4608
cert_kindSupport_rest_4 3 013 4992
cert_kindSupport_rest_4 3 014 5376
cert_kindSupport_rest_4 3 015 5760
cert_kindSupport_rest_4 3 016 6144
cert_kindSupport_rest_4 3 017 6528
cert_kindSupport_rest_4 3 018 6912
cert_kindSupport_rest_4 3 019 7272
cert_kindSupport_suffix_6 3 019
cert_kindSupport_suffix_7 3 018 019
cert_kindSupport_suffix_7 3 017 018
cert_kindSupport_suffix_7 3 016 017
cert_kindSupport_suffix_7 3 015 016
cert_kindSupport_suffix_7 3 014 015
cert_kindSupport_suffix_7 3 013 014
cert_kindSupport_suffix_7 3 012 013
cert_kindSupport_suffix_7 3 011 012
cert_kindSupport_suffix_7 3 010 011
cert_kindSupport_suffix_7 3 009 010
cert_kindSupport_suffix_7 3 008 009
cert_kindSupport_suffix_7 3 007 008
cert_kindSupport_suffix_7 3 006 007
cert_kindSupport_suffix_7 3 005 006
cert_kindSupport_suffix_7 3 004 005
cert_kindSupport_suffix_7 3 003 004
cert_kindSupport_suffix_7 3 002 003
cert_kindSupport_suffix_7 3 001 002
cert_kindSupport_suffix_7 3 000 001
cert_kindSupport_source_4 3 12 606
end Papers.RationalityTen.RootedCaches.RootedSixExtra05
