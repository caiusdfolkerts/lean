module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0349
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 15246
abbrev nodeCount : Nat := 2371
abbrev leafCount : Nat := 5
cert_widths_3 14 12 6 3
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)))
 (.branch 6
 (.branch 5
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩)
 (.leaf ⟨((certNat% 10)),(certNat% 11)⟩))
 (.branch 7
 (.leaf ⟨((certNat% 12)),(certNat% 13)⟩)
 (.branch 8
 (.leaf ⟨((certNat% 14)),(certNat% 15)⟩)
 (.leaf ⟨((certNat% 16)),(certNat% 17)⟩)))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨((certNat% 18)),(certNat% 19)⟩)
 (.leaf ⟨((certNat% 20)),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨((certNat% 22)),(certNat% 23)⟩)
 (.branch 13
 (.leaf ⟨((certNat% 24)),(certNat% 25)⟩)
 (.leaf ⟨((certNat% 26)),(certNat% 27)⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨((certNat% 28)),(certNat% 29)⟩)
 (.leaf ⟨((certNat% 30)),(certNat% 31)⟩))
 (.branch 17
 (.leaf ⟨((certNat% 32)),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨((certNat% 34)),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩))))))
def counterTable : Table Nat :=
(.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 38))
 (.leaf (certNat% 39)))
 (.branch 3
 (.leaf (certNat% 40))
 (.leaf (certNat% 41))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 42))
 (.leaf (certNat% 43)))
 (.branch 7
 (.leaf (certNat% 44))
 (.branch 8
 (.leaf (certNat% 45))
 (.leaf (certNat% 46))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (certNat% 47))
 (.leaf (certNat% 48)))
 (.branch 12
 (.leaf (certNat% 49))
 (.branch 13
 (.leaf (certNat% 50))
 (.leaf (certNat% 51)))))
 (.branch 16
 (.branch 15
 (.leaf (certNat% 52))
 (.leaf (certNat% 53)))
 (.branch 17
 (.leaf (certNat% 54))
 (.branch 18
 (.leaf (certNat% 55))
 (.leaf (certNat% 56)))))))
cert_codes_3
cert_counters_3 55
cert_rawNodes_3
def leafTable : Table (List Nat) :=
(.branch 2
 (.branch 1
 (.leaf [0,1,249,261,359,613,768,920,965,1167,1434,1617])
 (.leaf [0,35,150,224,319,409,766,858,1003,1122,1366]))
 (.branch 3
 (.leaf [0,71,185,224,415,633,766,920,988,1450,1519])
 (.branch 4
 (.leaf [0,71,152,257,413,609,768,920,988,1363,1517])
 (.leaf [0,35,116,259,339,384,768,878,1026,1146,1363]))))
cert_rawLeaves_3
cert_leaves_3
cert_quota_3 0 1 0 0 0 0 0 0 3 7
cert_nodeTest_5 48 01
cert_nodeTest_sound_4 48 01
cert_leafTest_4 01
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0349
