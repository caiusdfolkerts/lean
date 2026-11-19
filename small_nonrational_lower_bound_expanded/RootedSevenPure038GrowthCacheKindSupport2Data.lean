module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure038GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure038
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [1,2,3,4,5,6,13,14,15,16,17,18,25,26,27,28,29,30,40,41,42,43,44,45,46,47,48,61,62,63,64,65]
def kindSupport2_001 : List Nat := [66,73,74,75,76,77,78,85,86,87,88,89,90,97,98,99,100,101,102,103,104,105,118,119,120,121,122,123,124,125,126,139]
def kindSupport2_002 : List Nat := [140,141,142,143,144,151,152,153,154,155,156,163,164,165,166,167,168,175,176,177,178,179,180,181,182,183,196,197,198,199,200,201]
def kindSupport2_003 : List Nat := [208,209,210,211,212,213,220,221,222,223,224,225,232,233,234,235,236,237,238,239,240,253,254,255,256,257,258,265,266,267,268,269]
def kindSupport2_004 : List Nat := [270,277,278,279,280,281,282,289,290,291,292,293,294,295,296,297,310,311,312,313,314,315,316,317,318,331,332,333,334,335,336,343]
def kindSupport2_005 : List Nat := [344,345,346,347,348,355,356,357,358,359,360,367,368,369,370,371,372,373,374,375,388,389,390,391,392,393,394,395,396,409,410,411]
def kindSupport2_006 : List Nat := [412,413,414,421,422,423,424,425,426,433,434,435,436,437,438,445,446,447,448,449,450,451,452,453,466,467,468,469,470,471,472,473]
def kindSupport2_007 : List Nat := [474,487,488,489,490,491,492,499,500,501,502,503,504,511,512,513,514,515,516,523,524,525,526,527,528,529,530,531,544,545,546,547]
cert_kindSupport 2 548 549 550 551 552 565 566 567 568 569 570 571 572 573
cert_kindSupport_code 2
cert_kindSupport_rest_2 2 000 0
cert_kindSupport_rest_2 2 001 320
cert_kindSupport_rest_2 2 002 640
cert_kindSupport_rest_2 2 003 960
cert_kindSupport_rest_2 2 004 1280
cert_kindSupport_rest_2 2 005 1600
cert_kindSupport_rest_2 2 006 1920
cert_kindSupport_rest_2 2 007 2240
cert_kindSupport_rest_2 2 008 2560
cert_kindSupport_rest_2 2 009 2700
cert_kindSupport_suffix_2 2 009
cert_kindSupport_suffix_3 2 008 009
cert_kindSupport_suffix_3 2 007 008
cert_kindSupport_suffix_3 2 006 007
cert_kindSupport_suffix_3 2 005 006
cert_kindSupport_suffix_3 2 004 005
cert_kindSupport_suffix_3 2 003 004
cert_kindSupport_suffix_3 2 002 003
cert_kindSupport_suffix_3 2 001 002
cert_kindSupport_suffix_3 2 000 001
cert_kindSupport_source 2 10 270
end Papers.RationalityTen.RootedCaches.RootedSevenPure038
