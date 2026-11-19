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
cert_kindSupport_code_3 2
cert_kindSupport_rest_4 2 000 0
cert_kindSupport_rest_4 2 001 384
cert_kindSupport_rest_4 2 002 768
cert_kindSupport_rest_4 2 003 1152
cert_kindSupport_rest_4 2 004 1536
cert_kindSupport_rest_4 2 005 1920
cert_kindSupport_rest_4 2 006 2304
cert_kindSupport_rest_4 2 007 2688
cert_kindSupport_rest_4 2 008 3072
cert_kindSupport_rest_4 2 009 3456
cert_kindSupport_rest_4 2 010 3840
cert_kindSupport_rest_4 2 011 4224
cert_kindSupport_rest_4 2 012 4608
cert_kindSupport_rest_4 2 013 4992
cert_kindSupport_rest_4 2 014 5376
cert_kindSupport_rest_4 2 015 5472
cert_kindSupport_suffix_6 2 015
cert_kindSupport_suffix_7 2 014 015
cert_kindSupport_suffix_7 2 013 014
cert_kindSupport_suffix_7 2 012 013
cert_kindSupport_suffix_7 2 011 012
cert_kindSupport_suffix_7 2 010 011
cert_kindSupport_suffix_7 2 009 010
cert_kindSupport_suffix_7 2 008 009
cert_kindSupport_suffix_7 2 007 008
cert_kindSupport_suffix_7 2 006 007
cert_kindSupport_suffix_7 2 005 006
cert_kindSupport_suffix_7 2 004 005
cert_kindSupport_suffix_7 2 003 004
cert_kindSupport_suffix_7 2 002 003
cert_kindSupport_suffix_7 2 001 002
cert_kindSupport_suffix_7 2 000 001
cert_kindSupport_source_4 2 12 456
end Papers.RationalityTen.RootedCaches.RootedSixExtra05
