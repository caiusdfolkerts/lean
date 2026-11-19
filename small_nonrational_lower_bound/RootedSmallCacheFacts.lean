module
prelude
public import RootedSmallCacheCellsChecked
public import RootedSmallCacheRidgesChecked
public import RootedSmallCacheEdgesChecked
public import RootedSmallCacheKindsChecked

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness

theorem cell_facts (a : Fin 3436) : (RawFacetEmbedding.wellFormedCheck (rawCells a.val) = true) ∧ ((rawCells a.val).edges.all (fun e => decide (Nat.land e (rawCells a.val).vertices = e)) = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ ((rawCells a.val).edges.all (fun e => (edgeMasks e).testBit a.val) = true) ∧ ((List.finRange 10).all (fun v => decide ((vertexMasks v.val).testBit a.val = (rawCells a.val).vertices.testBit v.val)) = true) ∧ (decide (fastKind a.val = (rawCells a.val).kind) = true) ∧ ((missing a.val).all (fun e => decide (Nat.land e (rawCells a.val).vertices = e) && decide (e ∉ (rawCells a.val).edges)) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using
    cellTest_complete a.val (Nat.zero_le _) a.isLt

theorem ridge_facts (a : Fin 1024) : (decide (candidateMasks a.val = RawNatGrowthCheck.mask (candidateSupports a.val)) = true) ∧ ((candidateSupports a.val).all (fun c => hasNat (rawCells c).ridgeMasks a.val) = true) := by
  simpa only [ridgeTest, Bool.and_eq_true_iff] using
    ridgeTest_complete a.val (Nat.zero_le _) a.isLt

theorem edge_facts (a : Fin 1024) : (decide (edgeMasks a.val = RawNatGrowthCheck.mask (edgeSupports a.val)) = true) ∧ ((edgeSupports a.val).all (fun c => hasNat (rawCells c).edges a.val) = true) := by
  simpa only [edgeTest, Bool.and_eq_true_iff] using
    edgeTest_complete a.val (Nat.zero_le _) a.isLt

theorem kind_facts (a : Fin 5) : (decide (kindMasks a.val = RawNatGrowthCheck.mask (kindSupports a.val)) = true) ∧ ((kindSupports a.val).all (fun c => decide ((rawCells c).kind = a.val)) = true) := by
  simpa only [kindTest, Bool.and_eq_true_iff] using
    kindTest_complete a.val (Nat.zero_le _) a.isLt

def facts : RawSharedCache.Facts data where
  wellFormed c := (cell_facts c).1
  edgeWithin c e he := of_decide_eq_true (List.all_eq_true.mp (cell_facts c).2.1 e he)
  vertexExact v c := of_decide_eq_true
    (List.all_eq_true.mp (cell_facts c).2.2.2.2.1 v (List.mem_finRange v))
  candidateMasks q := of_decide_eq_true (ridge_facts q).1
  candidateCoverage c := (cell_facts c).2.2.1
  candidateSound q := (ridge_facts q).2
  edgeMasks e := of_decide_eq_true (edge_facts e).1
  edgeCoverage c := (cell_facts c).2.2.2.1
  edgeSound e := (edge_facts e).2
  kindMasks k hk := of_decide_eq_true (kind_facts ⟨k,List.mem_range.mp hk⟩).1
  kindSound k hk := (kind_facts ⟨k,List.mem_range.mp hk⟩).2
  kindExact c := of_decide_eq_true (cell_facts c).2.2.2.2.2.1
  missingSound c e he := by
    have h := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (cell_facts c).2.2.2.2.2.2 e he)
    exact ⟨of_decide_eq_true h.1,of_decide_eq_true h.2⟩
def badTest (i : Nat) : Bool :=
  decide (badMasks i = RawSharedCache.justifiedBad data facts (Fin.ofNat cellCount i))
#print axioms facts

end Papers.RationalityTen.RootedSmallCache
