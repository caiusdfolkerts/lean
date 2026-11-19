module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure018GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure018
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [80,81,82,83,84,85,92,93,94,95,96,97,104,105,106,107,108,109,110,111,112,122,123,124,125,126,127,128,129,130,131,132]
def kindSupport3_001 : List Nat := [133,140,141,142,143,144,145,152,153,154,155,156,157,164,165,166,167,168,169,179,180,181,182,183,184,185,186,187,188,189,190,197]
def kindSupport3_002 : List Nat := [198,199,200,201,202,209,210,211,212,213,214,221,222,223,224,225,226,236,237,238,239,240,241,242,243,244,245,246,247,257,258,259]
def kindSupport3_003 : List Nat := [260,261,262,263,264,265,266,267,268,275,276,277,278,279,280,287,288,289,290,291,292,299,300,301,302,303,304,314,315,316,317,318]
def kindSupport3_004 : List Nat := [319,320,321,322,323,324,325,332,333,334,335,336,337,344,345,346,347,348,349,356,357,358,359,360,361,371,372,373,374,375,376,377]
def kindSupport3_005 : List Nat := [378,379,380,381,382,392,393,394,395,396,397,398,399,400,401,402,403,413,414,415,416,417,418,419,420,421,422,423,424,431,432,433]
def kindSupport3_006 : List Nat := [434,435,436,443,444,445,446,447,448,455,456,457,458,459,460,470,471,472,473,474,475,476,477,478,479,480,481,488,489,490,491,492]
def kindSupport3_007 : List Nat := [493,500,501,502,503,504,505,512,513,514,515,516,517,527,528,529,530,531,532,533,534,535,536,537,538,548,549,550,551,552,553,554]
def kindSupport3_008 : List Nat := [555,556,557,558,559,566,567,568,569,570,571,578,579,580,581,582,583,590,591,592,593,594,595,605,606,607,608,609,610,611,612,613]
def kindSupport3_009 : List Nat := [614,615,616,626,627,628,629,630,631,632,633,634,635,636,637,647,648,649,650,651,652,653,654,655,656,657,658]
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
cert_kindSupport_rest_2 3 010 3150
cert_kindSupport_suffix_2 3 010
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
cert_kindSupport_source 3 10 315
end Papers.RationalityTen.RootedCaches.RootedSevenPure018
