module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure017GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure017
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,124]
def kindSupport3_002 : List Nat := [125,126,127,128,129,136,137,138,139,140,141,148,149,150,151,152,153,163,164,165,166,167,168,169,170,171,172,173,174,184,185,186]
def kindSupport3_003 : List Nat := [187,188,189,190,191,192,193,194,195,202,203,204,205,206,207,214,215,216,217,218,219,226,227,228,229,230,231,241,242,243,244,245]
def kindSupport3_004 : List Nat := [246,247,248,249,250,251,252,259,260,261,262,263,264,271,272,273,274,275,276,283,284,285,286,287,288,298,299,300,301,302,303,304]
def kindSupport3_005 : List Nat := [305,306,307,308,309,319,320,321,322,323,324,325,326,327,328,329,330,340,341,342,343,344,345,346,347,348,349,350,351,358,359,360]
def kindSupport3_006 : List Nat := [361,362,363,370,371,372,373,374,375,382,383,384,385,386,387,397,398,399,400,401,402,403,404,405,406,407,408,415,416,417,418,419]
def kindSupport3_007 : List Nat := [420,427,428,429,430,431,432,439,440,441,442,443,444,454,455,456,457,458,459,460,461,462,463,464,465,475,476,477,478,479,480,481]
def kindSupport3_008 : List Nat := [482,483,484,485,486,493,494,495,496,497,498,505,506,507,508,509,510,517,518,519,520,521,522,532,533,534,535,536,537,538,539,540]
def kindSupport3_009 : List Nat := [541,542,543,553,554,555,556,557,558,559,560,561,562,563,564,574,575,576,577,578,579,580,581,582,583,584,585]
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure017
