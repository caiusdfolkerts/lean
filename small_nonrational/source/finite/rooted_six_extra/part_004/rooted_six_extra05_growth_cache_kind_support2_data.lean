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
def kindSupport2_000 : List Nat := [88,89,90,91,92,93,100,101,102,103,104,105,112,113,114,115,116,117,124,125,126,127,128,129,136,137,138,139,140,141,148,149]
def kindSupport2_001 : List Nat := [150,151,152,153,164,165,166,167,168,169,170,171,172,185,186,187,188,189,190,191,192,193,206,207,208,209,210,211,212,213,214,227]
def kindSupport2_002 : List Nat := [228,229,230,231,232,233,234,235,252,253,254,255,256,257,258,259,260,273,274,275,276,277,278,279,280,281,294,295,296,297,298,299]
def kindSupport2_003 : List Nat := [300,301,302,315,316,317,318,319,320,321,322,323,336,337,338,339,340,341,342,343,344,357,358,359,360,361,362,363,364,365,378,379]
def kindSupport2_004 : List Nat := [380,381,382,383,384,385,386,399,400,401,402,403,404,405,406,407,420,421,422,423,424,425,426,427,428,429,449,450,451,452,453,454]
def kindSupport2_005 : List Nat := [455,456,457,470,471,472,473,474,475,476,477,478,491,492,493,494,495,496,497,498,499,512,513,514,515,516,517,518,519,520,533,534]
def kindSupport2_006 : List Nat := [535,536,537,538,539,540,541,554,555,556,557,558,559,560,561,562,575,576,577,578,579,580,581,582,583,596,597,598,599,600,601,602]
def kindSupport2_007 : List Nat := [603,604,617,618,619,620,621,622,623,624,625,626,642,643,644,645,646,647,648,649,650,663,664,665,666,667,668,669,670,671,684,685]
def kindSupport2_008 : List Nat := [686,687,688,689,690,691,692,705,706,707,708,709,710,711,712,713,726,727,728,729,730,731,732,733,734,735,751,752,753,754,755,756]
def kindSupport2_009 : List Nat := [763,764,765,766,767,768,775,776,777,778,779,780,787,788,789,790,791,792,799,800,801,802,803,804,811,812,813,814,815,816,823,824]
def kindSupport2_010 : List Nat := [825,826,827,828,829,830,831,844,845,846,847,848,849,850,851,852,865,866,867,868,869,870,871,872,873,886,887,888,889,890,891,892]
def kindSupport2_011 : List Nat := [893,894,907,908,909,910,911,912,913,914,915,928,929,930,931,932,933,934,935,936,949,950,951,952,953,954,955,956,957,970,971,972]
def kindSupport2_012 : List Nat := [973,974,975,976,977,978,991,992,993,994,995,996,997,998,999,1000,1016,1017,1018,1019,1020,1021,1022,1023,1024,1037,1038,1039,1040,1041,1042,1043]
def kindSupport2_013 : List Nat := [1044,1045,1058,1059,1060,1061,1062,1063,1064,1065,1066,1079,1080,1081,1082,1083,1084,1085,1086,1087,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1125,1126]
def kindSupport2_014 : List Nat := [1127,1128,1129,1130,1131,1132,1133,1134]
def kindSupport2_code : Nat := 0x46e46d46c46b46a46946846746646545545445345245145044f44e44d44c43f43e43d43c43b43a43943843742a42942842742642542442342241541441341241141040f40e40d4003ff3fe3fd3fc3fb3fa3f93f83e83e73e63e53e43e33e23e13e03df3d23d13d03cf3ce3cd3cc3cb3ca3bd3bc3bb3ba3b93b83b73b63b53a83a73a63a53a43a33a23a13a039339239139038f38e38d38c38b37e37d37c37b37a37937837737636936836736636536436336236135435335235135034f34e34d34c33f33e33d33c33b33a33933833733032f32e32d32c32b32432332232132031f31831731631531431330c30b30a3093083073002ff2fe2fd2fc2fb2f42f32f22f12f02ef2df2de2dd2dc2db2da2d92d82d72d62c92c82c72c62c52c42c32c22c12b42b32b22b12b02af2ae2ad2ac29f29e29d29c29b29a29929829728a28928828728628528428328227227127026f26e26d26c26b26a26925c25b25a25925825725625525424724624524424324224124023f23223123022f22e22d22c22b22a21d21c21b21a2192182172162152082072062052042032022012001f31f21f11f01ef1ee1ed1ec1eb1de1dd1dc1db1da1d91d81d71d61c91c81c71c61c51c41c31c21c11ad1ac1ab1aa1a91a81a71a61a51a419719619519419319219119018f18218118017f17e17d17c17b17a16d16c16b16a16916816716616515815715615515415315215115014314214114013f13e13d13c13b12e12d12c12b12a1291281271261191181171161151141131121111041031021011000ff0fe0fd0fc0eb0ea0e90e80e70e60e50e40e30d60d50d40d30d20d10d00cf0ce0c10c00bf0be0bd0bc0bb0ba0b90ac0ab0aa0a90a80a70a60a50a409909809709609509408d08c08b08a08908808108007f07e07d07c07507407307207107006906806706606506405d05c05b05a059058
def kindSupport2_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport2_code
def kindSupport2_rest_001 : Nat := PackedRawNatGrowth.drop 384 kindSupport2_code
def kindSupport2_rest_002 : Nat := PackedRawNatGrowth.drop 768 kindSupport2_code
def kindSupport2_rest_003 : Nat := PackedRawNatGrowth.drop 1152 kindSupport2_code
def kindSupport2_rest_004 : Nat := PackedRawNatGrowth.drop 1536 kindSupport2_code
def kindSupport2_rest_005 : Nat := PackedRawNatGrowth.drop 1920 kindSupport2_code
def kindSupport2_rest_006 : Nat := PackedRawNatGrowth.drop 2304 kindSupport2_code
def kindSupport2_rest_007 : Nat := PackedRawNatGrowth.drop 2688 kindSupport2_code
def kindSupport2_rest_008 : Nat := PackedRawNatGrowth.drop 3072 kindSupport2_code
def kindSupport2_rest_009 : Nat := PackedRawNatGrowth.drop 3456 kindSupport2_code
def kindSupport2_rest_010 : Nat := PackedRawNatGrowth.drop 3840 kindSupport2_code
def kindSupport2_rest_011 : Nat := PackedRawNatGrowth.drop 4224 kindSupport2_code
def kindSupport2_rest_012 : Nat := PackedRawNatGrowth.drop 4608 kindSupport2_code
def kindSupport2_rest_013 : Nat := PackedRawNatGrowth.drop 4992 kindSupport2_code
def kindSupport2_rest_014 : Nat := PackedRawNatGrowth.drop 5376 kindSupport2_code
def kindSupport2_rest_015 : Nat := PackedRawNatGrowth.drop 5472 kindSupport2_code
def kindSupport2_suffix_015 : List Nat := []
def kindSupport2_suffix_014 : List Nat := kindSupport2_014 ++ kindSupport2_suffix_015
def kindSupport2_suffix_013 : List Nat := kindSupport2_013 ++ kindSupport2_suffix_014
def kindSupport2_suffix_012 : List Nat := kindSupport2_012 ++ kindSupport2_suffix_013
def kindSupport2_suffix_011 : List Nat := kindSupport2_011 ++ kindSupport2_suffix_012
def kindSupport2_suffix_010 : List Nat := kindSupport2_010 ++ kindSupport2_suffix_011
def kindSupport2_suffix_009 : List Nat := kindSupport2_009 ++ kindSupport2_suffix_010
def kindSupport2_suffix_008 : List Nat := kindSupport2_008 ++ kindSupport2_suffix_009
def kindSupport2_suffix_007 : List Nat := kindSupport2_007 ++ kindSupport2_suffix_008
def kindSupport2_suffix_006 : List Nat := kindSupport2_006 ++ kindSupport2_suffix_007
def kindSupport2_suffix_005 : List Nat := kindSupport2_005 ++ kindSupport2_suffix_006
def kindSupport2_suffix_004 : List Nat := kindSupport2_004 ++ kindSupport2_suffix_005
def kindSupport2_suffix_003 : List Nat := kindSupport2_003 ++ kindSupport2_suffix_004
def kindSupport2_suffix_002 : List Nat := kindSupport2_002 ++ kindSupport2_suffix_003
def kindSupport2_suffix_001 : List Nat := kindSupport2_001 ++ kindSupport2_suffix_002
def kindSupport2_suffix_000 : List Nat := kindSupport2_000 ++ kindSupport2_suffix_001
theorem kindSupport2_source : kindSupports 2 =
    (PackedRawNatGrowth.readList 12 456 kindSupport2_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
