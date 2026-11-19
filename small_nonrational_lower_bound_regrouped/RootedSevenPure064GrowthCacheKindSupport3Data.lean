module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure064GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure064
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [71,72,73,74,75,76,83,84,85,86,87,88,95,96,97,98,99,100,101,102,103,113,114,115,116,117,118,119,120,121,122,123]
def kindSupport3_001 : List Nat := [124,131,132,133,134,135,136,143,144,145,146,147,148,155,156,157,158,159,160,170,171,172,173,174,175,176,177,178,179,180,181,191]
def kindSupport3_002 : List Nat := [192,193,194,195,196,197,198,199,200,201,202,203,204,205,215,216,217,218,219,220,221,222,223,224,225,226,233,234,235,236,237,238]
def kindSupport3_003 : List Nat := [245,246,247,248,249,250,257,258,259,260,261,262,272,273,274,275,276,277,278,279,280,281,282,283,293,294,295,296,297,298,299,300]
def kindSupport3_004 : List Nat := [301,302,303,304,311,312,313,314,315,316,323,324,325,326,327,328,335,336,337,338,339,340,350,351,352,353,354,355,356,357,358,359]
def kindSupport3_005 : List Nat := [360,361,371,372,373,374,375,376,377,378,379,380,381,382,389,390,391,392,393,394,401,402,403,404,405,406,413,414,415,416,417,418]
def kindSupport3_006 : List Nat := [428,429,430,431,432,433,434,435,436,437,438,439,446,447,448,449,450,451,458,459,460,461,462,463,470,471,472,473,474,475,485,486]
def kindSupport3_007 : List Nat := [487,488,489,490,491,492,493,494,495,496,506,507,508,509,510,511,512,513,514,515,516,517,527,528,529,530,531,532,533,534,535,536]
cert_kindSupport 3 537 538 548 549 550 551 552 553 554 555 556 557 558 559
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
cert_kindSupport_rest_2 3 009 2700
cert_kindSupport_suffix_2 3 009
cert_kindSupport_suffix_3 3 008 009
cert_kindSupport_suffix_3 3 007 008
cert_kindSupport_suffix_3 3 006 007
cert_kindSupport_suffix_3 3 005 006
cert_kindSupport_suffix_3 3 004 005
cert_kindSupport_suffix_3 3 003 004
cert_kindSupport_suffix_3 3 002 003
cert_kindSupport_suffix_3 3 001 002
cert_kindSupport_suffix_3 3 000 001
cert_kindSupport_source 3 10 270
end Papers.RationalityTen.RootedCaches.RootedSevenPure064
