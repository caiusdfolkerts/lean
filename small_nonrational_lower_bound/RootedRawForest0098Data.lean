module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure064GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0098
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 560
abbrev nodeCount : Nat := 2209
abbrev leafCount : Nat := 36
cert_widths_2 10 12 6
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩)
 (.leaf ⟨(certNat% 10),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨(certNat% 12),(certNat% 13)⟩)
 (.branch 8
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩)
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)))
 (.branch 15
 (.branch 14
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩)
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩))
 (.branch 16
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)
 (.branch 17
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩))))))
def counterTable : Table Nat :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 3
 (.leaf (certNat% 38))
 (.leaf (certNat% 39))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 7
 (.leaf (certNat% 42))
 (.branch 8
 (.leaf (certNat% 43))
 (.leaf (certNat% 44))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf (certNat% 45))
 (.leaf (certNat% 46)))
 (.branch 12
 (.leaf (certNat% 47))
 (.leaf (certNat% 48))))
 (.branch 15
 (.branch 14
 (.leaf (certNat% 49))
 (.leaf (certNat% 50)))
 (.branch 16
 (.leaf (certNat% 51))
 (.branch 17
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))))))
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 18
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf [0,32,66,101,138,204,234,370,396,449])
 (.leaf [0,39,66,101,138,204,248,302,331,399,464]))
 (.branch 3
 (.leaf [0,8,69,101,184,204,248,302,330,399,464])
 (.leaf [0,42,74,101,136,204,231,330,426,469])))
 (.branch 6
 (.branch 5
 (.leaf [0,46,99,101,119,139,204,230,331,396,544])
 (.leaf [0,55,99,101,119,139,204,231,331,399,469]))
 (.branch 7
 (.leaf [0,31,78,101,126,205,246,370,384,461])
 (.branch 8
 (.leaf [0,39,78,101,126,205,236,304,332,387,465])
 (.leaf [0,9,81,101,183,205,236,304,329,387,465])))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf [0,41,86,101,148,205,243,329,425,468])
 (.leaf [0,46,100,101,120,127,205,242,332,384,543]))
 (.branch 12
 (.leaf [0,55,100,101,120,127,205,243,332,387,468])
 (.leaf [0,32,65,102,150,203,233,369,408,448])))
 (.branch 15
 (.branch 14
 (.leaf [0,39,65,102,150,203,260,300,319,411,452])
 (.leaf [0,7,70,102,184,203,260,300,318,411,452]))
 (.branch 16
 (.leaf [0,42,73,102,135,203,232,318,427,457])
 (.branch 17
 (.leaf [0,47,87,102,121,151,203,229,319,408,544])
 (.leaf [0,55,87,102,121,151,203,232,319,411,457]))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf [0,47,88,102,122,128,205,254,320,383,542])
 (.leaf [0,55,88,102,122,128,205,255,320,388,456]))
 (.branch 21
 (.leaf [0,30,90,102,125,205,258,369,383,473])
 (.leaf [0,39,90,102,125,205,235,303,320,388,453])))
 (.branch 24
 (.branch 23
 (.leaf [0,9,93,102,182,205,235,303,317,388,453])
 (.leaf [0,40,98,102,160,205,255,317,425,456]))
 (.branch 25
 (.leaf [0,48,75,103,123,152,203,241,307,407,543])
 (.branch 26
 (.leaf [0,55,75,103,123,152,203,244,307,412,445])
 (.leaf [0,31,77,103,149,203,245,368,407,460])))))
 (.branch 31
 (.branch 29
 (.branch 28
 (.leaf [0,39,77,103,149,203,259,299,307,412,440])
 (.leaf [0,7,82,103,183,203,259,299,306,412,440]))
 (.branch 30
 (.leaf [0,41,85,103,147,203,244,306,427,445])
 (.leaf [0,48,76,103,124,140,204,253,308,395,542])))
 (.branch 33
 (.branch 32
 (.leaf [0,55,76,103,124,140,204,256,308,400,444])
 (.leaf [0,30,89,103,137,204,257,368,395,472]))
 (.branch 34
 (.leaf [0,39,89,103,137,204,247,301,308,400,441])
 (.branch 35
 (.leaf [0,8,94,103,182,204,247,301,305,400,441])
 (.leaf [0,40,97,103,159,204,256,305,426,444])))))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 5 4
cert_nodeTest_2 064
cert_nodeTest_sound_2 064
cert_leafTest_2 064
end Papers.RationalityTen.RootedForests.RootedRawForest0098
