module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public meta import CertificateNumbers
public import RootedSevenPure033GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure033
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def kindSupport2_000 : List Nat := [83,84,85,86,87,88,95,96,97,98,99,100,107,108,109,110,111,112,119,120,121,122,123,124,131,132,133,134,135,136,143,144]
def kindSupport2_001 : List Nat := [145,146,147,148,155,156,157,158,159,160,161,162,163,176,177,178,179,180,181,188,189,190,191,192,193,200,201,202,203,204,205,212]
def kindSupport2_002 : List Nat := [213,214,215,216,217,218,219,220,233,234,235,236,237,238,245,246,247,248,249,250,257,258,259,260,261,262,269,270,271,272,273,274]
def kindSupport2_003 : List Nat := [275,276,277,290,291,292,293,294,295,296,297,298,311,312,313,314,315,316,323,324,325,326,327,328,335,336,337,338,339,340,347,348]
def kindSupport2_004 : List Nat := [349,350,351,352,353,354,355,368,369,370,371,372,373,380,381,382,383,384,385,392,393,394,395,396,397,404,405,406,407,408,409,410]
def kindSupport2_005 : List Nat := [411,412,425,426,427,428,429,430,431,432,433,446,447,448,449,450,451,458,459,460,461,462,463,470,471,472,473,474,475,482,483,484]
def kindSupport2_006 : List Nat := [485,486,487,488,489,490,503,504,505,506,507,508,515,516,517,518,519,520,527,528,529,530,531,532,539,540,541,542,543,544,545,546]
def kindSupport2_007 : List Nat := [547,560,561,562,563,564,565,566,567,568,581,582,583,584,585,586,593,594,595,596,597,598,605,606,607,608,609,610,617,618,619,620]
def kindSupport2_008 : List Nat := [621,622,623,624,625,638,639,640,641,642,643,650,651,652,653,654,655,662,663,664,665,666,667,674,675,676,677,678,679,680,681,682]
def kindSupport2_009 : List Nat := [695,696,697,698,699,700,701,702,703,716,717,718,719,720,721,722,723,724,737,738,739,740,741,742,743,744,745]
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
cert_kindSupport_rest_2 2 009 2880
cert_kindSupport_rest_2 2 010 3150
cert_kindSupport_suffix_2 2 010
cert_kindSupport_suffix_3 2 009 010
cert_kindSupport_suffix_3 2 008 009
cert_kindSupport_suffix_3 2 007 008
cert_kindSupport_suffix_3 2 006 007
cert_kindSupport_suffix_3 2 005 006
cert_kindSupport_suffix_3 2 004 005
cert_kindSupport_suffix_3 2 003 004
cert_kindSupport_suffix_3 2 002 003
cert_kindSupport_suffix_3 2 001 002
cert_kindSupport_suffix_3 2 000 001
cert_kindSupport_source 2 10 315
end Papers.RationalityTen.RootedCaches.RootedSevenPure033
