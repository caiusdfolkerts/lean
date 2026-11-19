module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public meta import CertificateNumbers
public import RootedSevenTwoSix13GrowthCacheData
public import RootedSevenTwoSix13FastWordsData
public import CounterGrowthReplay
public import RawNatGrowthCompleteness
public import FiniteChecks
public import SubsumedClassification

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0471
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

abbrev cellCount : Nat := 2038
abbrev nodeCount : Nat := 95
abbrev leafCount : Nat := 1
cert_widths_3 11 7 6 1
cert_blocks_9
cert_counterTable_6
cert_codes_3
cert_counters_3 25
cert_rawNodes_3
cert_leafTable_3
cert_rawLeaves_3
cert_leaves_3
def quota : Nat → Nat
  | 0 => 1
  | 1 => 0
  | 2 => 6
  | 3 => 1
  | 4 => 2
  | _ => 0

def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 36 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.keys Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords.rawMaps rawLeaves codes counters i
theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 36 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.badMasks
        Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.keys Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 36 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.keys Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords.rawMaps rawLeaves codes counters i h
def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSevenTwoSix13.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0471
