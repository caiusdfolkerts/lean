module
prelude
public import RootedSixBase00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport9_000 : List Nat := [21352,21353,21354,21355,21356,21357,21358,21359,21360,21361,21362,21363,21364,21365,21366,21367,21368,21369,21370,21371,21372,21373,21374,21375,21376,21377,21378,21379,21380,21381,21382,21383]
def kindSupport9_001 : List Nat := [21384,21385,21386,21387,21388,21389,21390,21391,21392,21393,21394,21395,21396,21397,21398,21399,21400,21401,21402,21403,21404,21405,21406,21407,21408,21409,21410,21411,21412,21413,21414,21415]
def kindSupport9_002 : List Nat := [21416,21417,21418,21419,21420,21421,21422,21423,21424,21425,21426,21427,21428,21429,21430,21431,21432,21433,21434,21435,21436,21437,21438,21439,21440,21441,21442,21443,21444,21445,21446,21447]
def kindSupport9_003 : List Nat := [21448,21449,21450,21451,21452,21453,21454,21455,21456,21457,21458,21459,21460,21461,21462,21463,21464,21465,21466,21467,21468,21469,21470,21471,21472,21473,21474,21475,21476,21477,21478,21479]
def kindSupport9_004 : List Nat := [21480,21481,21482,21483,21484,21485,21486,21487,21488,21489,21490,21491,21492,21493,21494,21495,21496,21497,21498,21499,21500,21501,21502,21503,21504,21505,21506,21507,21508,21509,21510,21511]
def kindSupport9_005 : List Nat := [21512,21513,21514,21515,21516,21517,21518,21519,21520,21521,21522,21523,21524,21525,21526,21527,21528,21529,21530,21531,21532,21533,21534,21535,21536,21537,21538,21539,21540,21541,21542,21543]
def kindSupport9_006 : List Nat := [21544,21545,21546,21547,21548,21549,21550,21551,21552,21553,21554,21555,21556,21557,21558,21559,21560,21561,21562,21563,21564,21565,21566,21567,21568,21569,21570,21571,21572,21573,21574,21575]
def kindSupport9_007 : List Nat := [21576,21577,21578,21579,21580,21581,21582,21583,21584,21585,21586,21587,21588,21589,21590,21591,21592,21593,21594,21595,21596,21597,21598,21599,21600,21601,21602,21603,21604,21605,21606,21607]
def kindSupport9_008 : List Nat := [21608,21609,21610,21611,21612,21613,21614,21615,21616,21617,21618,21619,21620,21621,21622,21623,21624,21625,21626,21627,21628,21629,21630,21631,21632,21633,21634,21635,21636,21637,21638,21639]
def kindSupport9_009 : List Nat := [21640,21641,21642,21643,21644,21645,21646,21647,21648,21649,21650,21651,21652,21653,21654,21655,21656,21657,21658,21659,21660,21661,21662,21663,21664,21665,21666,21667,21668,21669,21670,21671]
def kindSupport9_010 : List Nat := [21672,21673,21674,21675,21676,21677,21678,21679,21680,21681,21682,21683,21684,21685,21686,21687,21688,21689,21690,21691,21692,21693,21694,21695,21696,21697,21698,21699,21700,21701,21702,21703]
def kindSupport9_011 : List Nat := [21704,21705,21706,21707,21708,21709,21710,21711,21712,21713,21714,21715,21716,21717,21718,21719,21720,21721,21722,21723,21724,21725,21726,21727,21728,21729,21730,21731,21732,21733,21734,21735]
def kindSupport9_012 : List Nat := [21736,21737,21738,21739,21740,21741,21742,21743,21744,21745,21746,21747,21748,21749,21750,21751,21752,21753,21754,21755,21756,21757,21758,21759,21760,21761,21762,21763,21764,21765,21766,21767]
def kindSupport9_013 : List Nat := [21768,21769,21770,21771,21772,21773,21774,21775,21776,21777,21778,21779,21780,21781,21782,21783,21784,21785,21786,21787,21788,21789,21790,21791,21792,21793,21794,21795,21796,21797,21798,21799]
def kindSupport9_014 : List Nat := [21800,21801,21802,21803,21804,21805,21806,21807,21808,21809,21810,21811,21812,21813,21814,21815,21816,21817,21818,21819,21820,21821,21822,21823,21824,21825,21826,21827,21828,21829,21830,21831]
def kindSupport9_015 : List Nat := [21832,21833,21834,21835,21836,21837,21838,21839,21840,21841,21842,21843,21844,21845,21846,21847,21848,21849,21850,21851,21852,21853,21854,21855,21856,21857,21858,21859,21860,21861,21862,21863]
def kindSupport9_016 : List Nat := [21864,21865,21866,21867,21868,21869,21870,21871,21872,21873,21874,21875,21876,21877,21878,21879,21880,21881,21882,21883,21884,21885,21886,21887,21888,21889,21890,21891,21892,21893,21894,21895]
def kindSupport9_017 : List Nat := [21896,21897,21898,21899,21900,21901,21902,21903,21904,21905,21906,21907,21908,21909,21910,21911,21912,21913,21914,21915,21916,21917,21918,21919,21920,21921,21922,21923,21924,21925,21926,21927]
def kindSupport9_018 : List Nat := [21928,21929,21930,21931,21932,21933,21934,21935,21936,21937,21938,21939,21940,21941,21942,21943,21944,21945,21946,21947,21948,21949,21950,21951,21952,21953,21954,21955,21956,21957,21958,21959]
def kindSupport9_019 : List Nat := [21960,21961,21962,21963,21964,21965,21966,21967,21968,21969,21970,21971,21972,21973,21974,21975]
def kindSupport9_code : Nat := 0xabaf575aaead5d4aba7574aae8d5d0ab9f573aae6d5ccab97572aae4d5c8ab8f571aae2d5c4ab87570aae0d5c0ab7f56faaded5bcab7756eaadcd5b8ab6f56daadad5b4ab6756caad8d5b0ab5f56baad6d5acab5756aaad4d5a8ab4f569aad2d5a4ab47568aad0d5a0ab3f567aaced59cab37566aaccd598ab2f565aacad594ab27564aac8d590ab1f563aac6d58cab17562aac4d588ab0f561aac2d584ab07560aac0d580aaff55faabed57caaf755eaabcd578aaef55daabad574aae755caab8d570aadf55baab6d56caad755aaab4d568aacf559aab2d564aac7558aab0d560aabf557aaaed55caab7556aaacd558aaaf555aaaad554aaa7554aaa8d550aa9f553aaa6d54caa97552aaa4d548aa8f551aaa2d544aa87550aaa0d540aa7f54faa9ed53caa7754eaa9cd538aa6f54daa9ad534aa6754caa98d530aa5f54baa96d52caa5754aaa94d528aa4f549aa92d524aa47548aa90d520aa3f547aa8ed51caa37546aa8cd518aa2f545aa8ad514aa27544aa88d510aa1f543aa86d50caa17542aa84d508aa0f541aa82d504aa07540aa80d500a9ff53faa7ed4fca9f753eaa7cd4f8a9ef53daa7ad4f4a9e753caa78d4f0a9df53baa76d4eca9d753aaa74d4e8a9cf539aa72d4e4a9c7538aa70d4e0a9bf537aa6ed4dca9b7536aa6cd4d8a9af535aa6ad4d4a9a7534aa68d4d0a99f533aa66d4cca997532aa64d4c8a98f531aa62d4c4a987530aa60d4c0a97f52faa5ed4bca97752eaa5cd4b8a96f52daa5ad4b4a96752caa58d4b0a95f52baa56d4aca95752aaa54d4a8a94f529aa52d4a4a947528aa50d4a0a93f527aa4ed49ca937526aa4cd498a92f525aa4ad494a927524aa48d490a91f523aa46d48ca917522aa44d488a90f521aa42d484a907520aa40d480a8ff51faa3ed47ca8f751eaa3cd478a8ef51daa3ad474a8e751caa38d470a8df51baa36d46ca8d751aaa34d468a8cf519aa32d464a8c7518aa30d460a8bf517aa2ed45ca8b7516aa2cd458a8af515aa2ad454a8a7514aa28d450a89f513aa26d44ca897512aa24d448a88f511aa22d444a887510aa20d440a87f50faa1ed43ca87750eaa1cd438a86f50daa1ad434a86750caa18d430a85f50baa16d42ca85750aaa14d428a84f509aa12d424a847508aa10d420a83f507aa0ed41ca837506aa0cd418a82f505aa0ad414a827504aa08d410a81f503aa06d40ca817502aa04d408a80f501aa02d404a807500aa00d400a7ff4ffa9fed3fca7f74fea9fcd3f8a7ef4fda9fad3f4a7e74fca9f8d3f0a7df4fba9f6d3eca7d74faa9f4d3e8a7cf4f9a9f2d3e4a7c74f8a9f0d3e0a7bf4f7a9eed3dca7b74f6a9ecd3d8a7af4f5a9ead3d4a7a74f4a9e8d3d0a79f4f3a9e6d3cca7974f2a9e4d3c8a78f4f1a9e2d3c4a7874f0a9e0d3c0a77f4efa9ded3bca7774eea9dcd3b8a76f4eda9dad3b4a7674eca9d8d3b0a75f4eba9d6d3aca7574eaa9d4d3a8a74f4e9a9d2d3a4a7474e8a9d0d3a0a73f4e7a9ced39ca7374e6a9ccd398a72f4e5a9cad394a7274e4a9c8d390a71f4e3a9c6d38ca7174e2a9c4d388a70f4e1a9c2d384a7074e0a9c0d380a6ff4dfa9bed37ca6f74dea9bcd378a6ef4dda9bad374a6e74dca9b8d370a6df4dba9b6d36ca6d74daa9b4d368
def kindSupport9_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport9_code
def kindSupport9_rest_001 : Nat := PackedRawNatGrowth.drop 480 kindSupport9_code
def kindSupport9_rest_002 : Nat := PackedRawNatGrowth.drop 960 kindSupport9_code
def kindSupport9_rest_003 : Nat := PackedRawNatGrowth.drop 1440 kindSupport9_code
def kindSupport9_rest_004 : Nat := PackedRawNatGrowth.drop 1920 kindSupport9_code
def kindSupport9_rest_005 : Nat := PackedRawNatGrowth.drop 2400 kindSupport9_code
def kindSupport9_rest_006 : Nat := PackedRawNatGrowth.drop 2880 kindSupport9_code
def kindSupport9_rest_007 : Nat := PackedRawNatGrowth.drop 3360 kindSupport9_code
def kindSupport9_rest_008 : Nat := PackedRawNatGrowth.drop 3840 kindSupport9_code
def kindSupport9_rest_009 : Nat := PackedRawNatGrowth.drop 4320 kindSupport9_code
def kindSupport9_rest_010 : Nat := PackedRawNatGrowth.drop 4800 kindSupport9_code
def kindSupport9_rest_011 : Nat := PackedRawNatGrowth.drop 5280 kindSupport9_code
def kindSupport9_rest_012 : Nat := PackedRawNatGrowth.drop 5760 kindSupport9_code
def kindSupport9_rest_013 : Nat := PackedRawNatGrowth.drop 6240 kindSupport9_code
def kindSupport9_rest_014 : Nat := PackedRawNatGrowth.drop 6720 kindSupport9_code
def kindSupport9_rest_015 : Nat := PackedRawNatGrowth.drop 7200 kindSupport9_code
def kindSupport9_rest_016 : Nat := PackedRawNatGrowth.drop 7680 kindSupport9_code
def kindSupport9_rest_017 : Nat := PackedRawNatGrowth.drop 8160 kindSupport9_code
def kindSupport9_rest_018 : Nat := PackedRawNatGrowth.drop 8640 kindSupport9_code
def kindSupport9_rest_019 : Nat := PackedRawNatGrowth.drop 9120 kindSupport9_code
def kindSupport9_rest_020 : Nat := PackedRawNatGrowth.drop 9360 kindSupport9_code
def kindSupport9_suffix_020 : List Nat := []
def kindSupport9_suffix_019 : List Nat := kindSupport9_019 ++ kindSupport9_suffix_020
def kindSupport9_suffix_018 : List Nat := kindSupport9_018 ++ kindSupport9_suffix_019
def kindSupport9_suffix_017 : List Nat := kindSupport9_017 ++ kindSupport9_suffix_018
def kindSupport9_suffix_016 : List Nat := kindSupport9_016 ++ kindSupport9_suffix_017
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
theorem kindSupport9_source : kindRows 9 =
    (PackedRawNatGrowth.readList 15 624 kindSupport9_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase00
