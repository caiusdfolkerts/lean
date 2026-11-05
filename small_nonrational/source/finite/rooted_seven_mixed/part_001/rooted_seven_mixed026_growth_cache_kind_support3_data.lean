module
prelude
public import RootedSevenMixed026GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed026
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport3_000 : List Nat := [7,8,9,10,11,12,19,20,21,22,23,24,31,32,33,34,35,36,37,38,39,49,50,51,52,53,54,55,56,57,58,59]
def kindSupport3_001 : List Nat := [60,67,68,69,70,71,72,79,80,81,82,83,84,91,92,93,94,95,96,106,107,108,109,110,111,112,113,114,115,116,117,127]
def kindSupport3_002 : List Nat := [128,129,130,131,132,133,134,135,136,137,138,139,140,141,151,152,153,154,155,156,157,158,159,160,161,162,169,170,171,172,173,174]
def kindSupport3_003 : List Nat := [181,182,183,184,185,186,193,194,195,196,197,198,208,209,210,211,212,213,214,215,216,217,218,219,229,230,231,232,233,234,235,236]
def kindSupport3_004 : List Nat := [237,238,239,240,247,248,249,250,251,252,259,260,261,262,263,264,271,272,273,274,275,276,286,287,288,289,290,291,292,293,294,295]
def kindSupport3_005 : List Nat := [296,297,307,308,309,310,311,312,313,314,315,316,317,318,325,326,327,328,329,330,337,338,339,340,341,342,349,350,351,352,353,354]
def kindSupport3_006 : List Nat := [364,365,366,367,368,369,370,371,372,373,374,375,382,383,384,385,386,387,394,395,396,397,398,399,406,407,408,409,410,411,421,422]
def kindSupport3_007 : List Nat := [423,424,425,426,427,428,429,430,431,432,442,443,444,445,446,447,448,449,450,451,452,453,463,464,465,466,467,468,469,470,471,472]
def kindSupport3_008 : List Nat := [473,474,484,485,486,487,488,489,490,491,492,493,494,495]
def kindSupport3_code : Nat := 0x7bdee7b5ec7adea7a5e879de6795e4769d9761d7759d5751d3749d1741cf715c470dc2705c06fdbe6f5bc6edba6c1af6b9ad6b1ab6a9a96a1a7699a566d9a6659865d9663d8e6358c62d8a60d82605805fd7e5dd765d5745cd725c5705bd6e5b56c589615815f5795d5595555153549515294952147519454f93d4f13b4e9394e1374d9354d1334a52849d264952448d224852047d1e45113449114410f4210741905411033f0fb3e8f93e0f73c0ef3b8ed3b0eb3a8e93a0e7398e536cda364d835cd6354d434cd2344d0318c5310c3308c12e8b92e0b72d8b52b8ad2b0ab2a8a9288a12809f2789d2709b26899260972348c22c8a2248821c862148420c82204801fc751d0731c8711c06f1b86d1b06b1a86017c5e1745c16c5414c521445013c4811c461144410c3c0ec3a0e4380dc360d4340cc320c4270982509023088210801f0601705815050130300b0280902007
def kindSupport3_rest_000 : Nat := PackedRawNatGrowth.drop 0 kindSupport3_code
def kindSupport3_rest_001 : Nat := PackedRawNatGrowth.drop 320 kindSupport3_code
def kindSupport3_rest_002 : Nat := PackedRawNatGrowth.drop 640 kindSupport3_code
def kindSupport3_rest_003 : Nat := PackedRawNatGrowth.drop 960 kindSupport3_code
def kindSupport3_rest_004 : Nat := PackedRawNatGrowth.drop 1280 kindSupport3_code
def kindSupport3_rest_005 : Nat := PackedRawNatGrowth.drop 1600 kindSupport3_code
def kindSupport3_rest_006 : Nat := PackedRawNatGrowth.drop 1920 kindSupport3_code
def kindSupport3_rest_007 : Nat := PackedRawNatGrowth.drop 2240 kindSupport3_code
def kindSupport3_rest_008 : Nat := PackedRawNatGrowth.drop 2560 kindSupport3_code
def kindSupport3_rest_009 : Nat := PackedRawNatGrowth.drop 2700 kindSupport3_code
def kindSupport3_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 10 270 kindSupport3_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSevenMixed026
