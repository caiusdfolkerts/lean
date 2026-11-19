module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure004GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure004
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [74,75,76,77,78,79,86,87,88,89,90,91,98,99,100,101,102,103,113,114,115,116,117,118,119,120,121,134,135,136,137,138]
def kindSupport2_001 : List Nat := [139,146,147,148,149,150,151,158,159,160,161,162,163,170,171,172,173,174,175,176,177,178,191,192,193,194,195,196,197,198,199,212]
def kindSupport2_002 : List Nat := [213,214,215,216,217,224,225,226,227,228,229,236,237,238,239,240,241,248,249,250,251,252,253,254,255,256,269,270,271,272,273,274]
def kindSupport2_003 : List Nat := [275,276,277,290,291,292,293,294,295,302,303,304,305,306,307,314,315,316,317,318,319,326,327,328,329,330,331,332,333,334,347,348]
def kindSupport2_004 : List Nat := [349,350,351,352,359,360,361,362,363,364,371,372,373,374,375,376,383,384,385,386,387,388,389,390,391,404,405,406,407,408,409,416]
def kindSupport2_005 : List Nat := [417,418,419,420,421,428,429,430,431,432,433,440,441,442,443,444,445,446,447,448,461,462,463,464,465,466,467,468,469,482,483,484]
def kindSupport2_006 : List Nat := [485,486,487,494,495,496,497,498,499,506,507,508,509,510,511,518,519,520,521,522,523,524,525,526,539,540,541,542,543,544,545,546]
def kindSupport2_007 : List Nat := [547,560,561,562,563,564,565,572,573,574,575,576,577,584,585,586,587,588,589,596,597,598,599,600,601,602,603,604,617,618,619,620]
cert_kindSupport 2 621 622 623 624 625 638 639 640 641 642 643 644 645 646
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure004
