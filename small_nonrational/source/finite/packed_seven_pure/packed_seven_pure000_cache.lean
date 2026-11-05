module
prelude
public import PackedSevenPure000Cells
public import PackedSevenPure000Ridges
public import PackedSevenPure000Kinds

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenPure000
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem cell_facts (a : Fin 758) :
    (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (badMasks a.val = RawNatGrowthCheck.mask (badRows a.val)) = true) ∧ ((badRows a.val).all (fun c => !(ConcreteGrowth.compatible (rawCells a.val) (rawCells c))) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt
theorem ridge_facts (q : Fin 1024) :
    (decide (candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val)) = true) ∧ ((candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true) := by
  simpa only [ridgeTest, Bool.and_eq_true_iff] using ridgeTest_complete q.val (Nat.zero_le _) q.isLt
noncomputable def cache : Cache ridgeList literalCompatible kind :=
  FastRawCacheCertificate.ofChecks rawCells candidateMasks badMasks kindMasks
    candidateRows badRows kindRows keys
    (fun c => (cell_facts c).1)
    (fun q => of_decide_eq_true (ridge_facts q).1)
    (fun c => (cell_facts c).2.1)
    (fun q => (ridge_facts q).2)
    (fun c => of_decide_eq_true (cell_facts c).2.2.1)
    (fun c => (cell_facts c).2.2.2.1)
    (by
      intro j hj
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).1)
    (by
      intro j hj
      exact (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).2)
theorem raw_kind_exact (c : Fin 758) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.2.2
#print axioms cache

end Papers.RationalityTen.PackedReplay.PackedSevenPure000
