module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public meta import CertificateNumbers
public import HexNatLiteral
public import RootedSevenPure057GrowthCacheData
public import IdentityRawMaps
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0091
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 560
abbrev nodeCount : Nat := 1999
abbrev leafCount : Nat := 12
cert_widths_2 10 11 4
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 8
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
 (.leaf ⟨(certNat% 14),(certNat% 15)⟩))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ⟨(certNat% 16),(certNat% 17)⟩)
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩))
 (.branch 11
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩)
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)))
 (.branch 14
 (.branch 13
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))
 (.branch 15
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩)))))
def counterTable : Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 32))
 (.leaf (certNat% 33)))
 (.branch 3
 (.leaf (certNat% 34))
 (.leaf (certNat% 35))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 36))
 (.leaf (certNat% 37)))
 (.branch 7
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (certNat% 40))
 (.leaf (certNat% 41)))
 (.branch 11
 (.leaf (certNat% 42))
 (.leaf (certNat% 43))))
 (.branch 14
 (.branch 13
 (.leaf (certNat% 44))
 (.leaf (certNat% 45)))
 (.branch 15
 (.leaf (certNat% 46))
 (.leaf (certNat% 47))))))
cert_codes_2
cert_counters_2
cert_rawNodes_2
def leafTable : Table (List Nat) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf [0,32,66,101,138,204,262,279,365,399,485])
 (.branch 2
 (.leaf [0,52,99,101,119,139,204,230,331,396,539])
 (.leaf [0,31,78,101,126,205,261,278,365,387,486])))
 (.branch 4
 (.leaf [0,51,100,101,120,127,205,242,332,384,539])
 (.branch 5
 (.leaf [0,32,65,102,150,203,250,281,366,411,473])
 (.leaf [0,52,87,102,121,151,203,229,319,408,540]))))
 (.branch 9
 (.branch 7
 (.leaf [0,50,88,102,122,128,205,254,320,383,540])
 (.branch 8
 (.leaf [0,30,90,102,125,205,249,280,366,388,474])
 (.leaf [0,51,75,103,123,152,203,241,307,407,541])))
 (.branch 10
 (.leaf [0,31,77,103,149,203,238,283,367,412,461])
 (.branch 11
 (.leaf [0,50,76,103,124,140,204,253,308,395,541])
 (.leaf [0,30,89,103,137,204,237,282,367,400,462])))))
cert_rawLeaves_2
cert_leaves_2
cert_quota_2 1 0 5 4
cert_nodeTest_2 057
cert_nodeTest_sound_2 057
cert_leafTest_2 057
end Papers.RationalityTen.RootedForests.RootedRawForest0091
