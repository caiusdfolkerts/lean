module
prelude
public import RootedSevenPure002GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure002
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,136,137,138,145,146,147,148,149,150,157,158,159,160,161,162,169,170,171,172,173,174,184,185,186]
def kindSupport3_003 : List Nat := [187,188,189,190,191,192,193,194,195,205,206,207,208,209,210,211,212,213,214,215,216,223,224,225,226,227,228,235,236,237,238,239]
def kindSupport3_004 : List Nat := [240,247,248,249,250,251,252,262,263,264,265,266,267,268,269,270,271,272,273,280,281,282,283,284,285,292,293,294,295,296,297,304]
def kindSupport3_005 : List Nat := [305,306,307,308,309,319,320,321,322,323,324,325,326,327,328,329,330,337,338,339,340,341,342,349,350,351,352,353,354,361,362,363]
def kindSupport3_006 : List Nat := [364,365,366,376,377,378,379,380,381,382,383,384,385,386,387,397,398,399,400,401,402,403,404,405,406,407,408,415,416,417,418,419]
def kindSupport3_007 : List Nat := [420,427,428,429,430,431,432,439,440,441,442,443,444,454,455,456,457,458,459,460,461,462,463,464,465,475,476,477,478,479,480,481]
def kindSupport3_008 : List Nat := [482,483,484,485,486,493,494,495,496,497,498,505,506,507,508,509,510,517,518,519,520,521,522,532,533,534,535,536,537,538,539,540]
def kindSupport3_009 : List Nat := [541,542,543,553,554,555,556,557,558,559,560,561,562,563,564,574,575,576,577,578,579,580,581,582,583,584,585]
def kindSupport3_code : Nat := 0x2499224791a459124390a419023f8fa348ce328c6308be2e8b62c8ae2a8a61f87a1d8721b86a198621785a158520a8260881e06815fe7f5fc7edfa7e5f27c5f07bdee7b5e6795e478de2785e077dde775dc76dd1741cf739cd731cb729c9721c7719bc6edba6e5b86ddb06bdae6b5ac6ada468da2685a067d9865d966559464d926459063d8e63583609816017f5f97d5f17b5e9795e16e5b56c5ad6a5a5625856057d5e575565555454d525454a5254851d465154450d42505404fd354d1334c9314c1294a127499254911d4711b46919461114410f4390d4310b4290942107418fc3ecfa3e4f83dcf03bcee3b4ec3ace438ce2384e037cd835cd6354d434cd2344d033cce334c3308c1300bf2f8bd2f0bb2e8b92e0ae2b4ac2acaa2a4a2284a027c9e274962549424c922448a2248821c862148420c82204801fc751d0731c8711c06f1b86d1b06b1a86017c5e1745c16c5414c521445013c4811c461144410c3c0ec3a0e4380dc360d4340cc320c4270982509023088210801f0601705815050130300b0280902007
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 2880 kindSupport3_code
def kindSupport3_rest_010 : Nat := PackedRawNatGrowth.drop 3150 kindSupport3_code
def kindSupport3_suffix_010 : List Nat := []
def kindSupport3_suffix_009 : List Nat := kindSupport3_009 ++ kindSupport3_suffix_010
def kindSupport3_suffix_008 : List Nat := kindSupport3_008 ++ kindSupport3_suffix_009
def kindSupport3_suffix_007 : List Nat := kindSupport3_007 ++ kindSupport3_suffix_008
def kindSupport3_suffix_006 : List Nat := kindSupport3_006 ++ kindSupport3_suffix_007
def kindSupport3_suffix_005 : List Nat := kindSupport3_005 ++ kindSupport3_suffix_006
def kindSupport3_suffix_004 : List Nat := kindSupport3_004 ++ kindSupport3_suffix_005
def kindSupport3_suffix_003 : List Nat := kindSupport3_003 ++ kindSupport3_suffix_004
def kindSupport3_suffix_002 : List Nat := kindSupport3_002 ++ kindSupport3_suffix_003
def kindSupport3_suffix_001 : List Nat := kindSupport3_001 ++ kindSupport3_suffix_002
def kindSupport3_suffix_000 : List Nat := kindSupport3_000 ++ kindSupport3_suffix_001
theorem kindSupport3_source : kindRows 3 =
    (PackedRawNatGrowth.readList 10 315 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenPure002
