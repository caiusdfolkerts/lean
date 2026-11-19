module
prelude
public meta import CertificateNumbers
public import RootedSmallCacheData
public import RootedSmallGeneratorWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallRawForest02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 3436
abbrev nodeCount : Nat := 4925
abbrev leafCount : Nat := 1
def widths : PackedRawNatGrowth.Widths := ⟨12,13,11,1⟩
def blocks : Table PackedRawNatGrowth.Block :=
(.branch 19
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
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf ⟨(certNat% 18),(certNat% 19)⟩)
 (.leaf ⟨(certNat% 20),(certNat% 21)⟩))
 (.branch 12
 (.leaf ⟨(certNat% 22),(certNat% 23)⟩)
 (.branch 13
 (.leaf ⟨(certNat% 24),(certNat% 25)⟩)
 (.leaf ⟨(certNat% 26),(certNat% 27)⟩))))
 (.branch 16
 (.branch 15
 (.leaf ⟨(certNat% 28),(certNat% 29)⟩)
 (.leaf ⟨(certNat% 30),(certNat% 31)⟩))
 (.branch 17
 (.leaf ⟨(certNat% 32),(certNat% 33)⟩)
 (.branch 18
 (.leaf ⟨(certNat% 34),(certNat% 35)⟩)
 (.leaf ⟨(certNat% 36),(certNat% 37)⟩))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf ⟨(certNat% 38),(certNat% 39)⟩)
 (.leaf ⟨(certNat% 40),(certNat% 41)⟩))
 (.branch 22
 (.leaf ⟨(certNat% 42),(certNat% 43)⟩)
 (.branch 23
 (.leaf ⟨(certNat% 44),(certNat% 45)⟩)
 (.leaf ⟨(certNat% 46),(certNat% 47)⟩))))
 (.branch 26
 (.branch 25
 (.leaf ⟨(certNat% 48),(certNat% 49)⟩)
 (.leaf ⟨(certNat% 50),(certNat% 51)⟩))
 (.branch 27
 (.leaf ⟨(certNat% 52),(certNat% 53)⟩)
 (.branch 28
 (.leaf ⟨(certNat% 54),(certNat% 55)⟩)
 (.leaf ⟨(certNat% 56),(certNat% 57)⟩)))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf ⟨(certNat% 58),(certNat% 59)⟩)
 (.leaf ⟨(certNat% 60),(certNat% 61)⟩))
 (.branch 32
 (.leaf ⟨(certNat% 62),(certNat% 63)⟩)
 (.branch 33
 (.leaf ⟨(certNat% 64),(certNat% 65)⟩)
 (.leaf ⟨(certNat% 66),(certNat% 67)⟩))))
 (.branch 36
 (.branch 35
 (.leaf ⟨(certNat% 68),(certNat% 69)⟩)
 (.leaf ⟨(certNat% 70),(certNat% 71)⟩))
 (.branch 37
 (.leaf ⟨(certNat% 72),(certNat% 73)⟩)
 (.branch 38
 (.leaf ⟨(certNat% 74),(certNat% 75)⟩)
 (.leaf ⟨(certNat% 76),(certNat% 77)⟩)))))))
def counterTable : Table Nat :=
(.branch 19
 (.branch 9
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 78))
 (.leaf (certNat% 79)))
 (.branch 3
 (.leaf (certNat% 80))
 (.leaf (certNat% 81))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 82))
 (.leaf (certNat% 83)))
 (.branch 7
 (.leaf (certNat% 84))
 (.branch 8
 (.leaf (certNat% 85))
 (.leaf (certNat% 86))))))
 (.branch 14
 (.branch 11
 (.branch 10
 (.leaf (certNat% 87))
 (.leaf (certNat% 88)))
 (.branch 12
 (.leaf (certNat% 89))
 (.branch 13
 (.leaf (certNat% 90))
 (.leaf (certNat% 91)))))
 (.branch 16
 (.branch 15
 (.leaf (certNat% 92))
 (.leaf (certNat% 93)))
 (.branch 17
 (.leaf (certNat% 94))
 (.branch 18
 (.leaf (certNat% 95))
 (.leaf (certNat% 96)))))))
 (.branch 29
 (.branch 24
 (.branch 21
 (.branch 20
 (.leaf (certNat% 97))
 (.leaf (certNat% 98)))
 (.branch 22
 (.leaf (certNat% 99))
 (.branch 23
 (.leaf (certNat% 100))
 (.leaf (certNat% 101)))))
 (.branch 26
 (.branch 25
 (.leaf (certNat% 102))
 (.leaf (certNat% 103)))
 (.branch 27
 (.leaf (certNat% 104))
 (.branch 28
 (.leaf (certNat% 105))
 (.leaf (certNat% 106))))))
 (.branch 34
 (.branch 31
 (.branch 30
 (.leaf (certNat% 107))
 (.leaf (certNat% 108)))
 (.branch 32
 (.leaf (certNat% 109))
 (.branch 33
 (.leaf (certNat% 110))
 (.leaf (certNat% 111)))))
 (.branch 36
 (.branch 35
 (.leaf (certNat% 112))
 (.leaf (certNat% 113)))
 (.branch 37
 (.leaf (certNat% 114))
 (.branch 38
 (.leaf (certNat% 115))
 (.leaf (certNat% 116))))))))
def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload
def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))
def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)
def leafTable : Table (List Nat) :=
(.leaf [0,204,336,690,822,1550,1709,1841,2570,3140])
def rawLeaves := leafTable.get
def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves
def quota : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 9
  | 3 => 0
  | 4 => 0
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  CounterGrowthReplay.check widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1440 leafCount nodeCount (rawNodes i) = true ∧
      RawNatGrowthCheck.nodeCheck RootedSmallCache.candidateMasks RootedSmallCache.badMasks
        RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
        RootedSmallGeneratorWords.rawMaps rawLeaves rawNodes i = true :=
  CounterGrowthReplay.check_sound widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.Small.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.SmallRawForests.SmallRawForest02
