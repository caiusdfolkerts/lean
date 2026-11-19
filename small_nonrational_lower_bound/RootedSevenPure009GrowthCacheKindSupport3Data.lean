module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure009GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure009
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [89,90,91,92,93,94,101,102,103,104,105,106,113,114,115,116,117,118,125,126,127,128,129,130,137,138,139,140,141,142,149,150]
def kindSupport3_001 : List Nat := [151,152,153,154,164,165,166,167,168,169,170,171,172,173,174,175,182,183,184,185,186,187,194,195,196,197,198,199,206,207,208,209]
def kindSupport3_002 : List Nat := [210,211,221,222,223,224,225,226,227,228,229,230,231,232,242,243,244,245,246,247,248,249,250,251,252,253,260,261,262,263,264,265]
def kindSupport3_003 : List Nat := [272,273,274,275,276,277,284,285,286,287,288,289,299,300,301,302,303,304,305,306,307,308,309,310,317,318,319,320,321,322,329,330]
def kindSupport3_004 : List Nat := [331,332,333,334,341,342,343,344,345,346,356,357,358,359,360,361,362,363,364,365,366,367,374,375,376,377,378,379,386,387,388,389]
def kindSupport3_005 : List Nat := [390,391,398,399,400,401,402,403,413,414,415,416,417,418,419,420,421,422,423,424,434,435,436,437,438,439,440,441,442,443,444,445]
def kindSupport3_006 : List Nat := [452,453,454,455,456,457,464,465,466,467,468,469,476,477,478,479,480,481,491,492,493,494,495,496,497,498,499,500,501,502,509,510]
def kindSupport3_007 : List Nat := [511,512,513,514,521,522,523,524,525,526,533,534,535,536,537,538,548,549,550,551,552,553,554,555,556,557,558,559,569,570,571,572]
def kindSupport3_008 : List Nat := [573,574,575,576,577,578,579,580,587,588,589,590,591,592,599,600,601,602,603,604,611,612,613,614,615,616,626,627,628,629,630,631]
def kindSupport3_009 : List Nat := [632,633,634,635,636,637,647,648,649,650,651,652,653,654,655,656,657,658,665,666,667,668,669,670,677,678,679,680,681,682,689,690]
def kindSupport3_010 : List Nat := [691,692,693,694,704,705,706,707,708,709,710,711,712,713,714,715,725,726,727,728,729,730,731,732,733,734,735,736,746,747,748,749]
def kindSupport3_011 : List Nat := [750,751,752,753,754,755,756,757]
cert_kindSupport_code 3
cert_kindSupport_rest_2 3 000 0
cert_kindSupport_rest_2 3 001 320
cert_kindSupport_rest_2 3 002 640
cert_kindSupport_rest_2 3 003 960
cert_kindSupport_rest_2 3 004 1280
cert_kindSupport_rest_2 3 005 1600
cert_kindSupport_rest_2 3 006 1920
cert_kindSupport_rest_2 3 007 2240
cert_kindSupport_rest_2 3 008 2560
cert_kindSupport_rest_2 3 009 2880
cert_kindSupport_rest_2 3 010 3200
cert_kindSupport_rest_2 3 011 3520
cert_kindSupport_rest_2 3 012 3600
cert_kindSupport_suffix_2 3 012
cert_kindSupport_suffix_3 3 011 012
cert_kindSupport_suffix_3 3 010 011
cert_kindSupport_suffix_3 3 009 010
cert_kindSupport_suffix_3 3 008 009
cert_kindSupport_suffix_3 3 007 008
cert_kindSupport_suffix_3 3 006 007
cert_kindSupport_suffix_3 3 005 006
cert_kindSupport_suffix_3 3 004 005
cert_kindSupport_suffix_3 3 003 004
cert_kindSupport_suffix_3 3 002 003
cert_kindSupport_suffix_3 3 001 002
cert_kindSupport_suffix_3 3 000 001
cert_kindSupport_source 3 10 360
end Papers.RationalityTen.RootedCaches.RootedSevenPure009
