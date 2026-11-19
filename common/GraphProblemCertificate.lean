module
prelude
public import GraphGrowthConstraints
public import GrowthCacheCertificate

@[expose] public section

/-! Sparse row certificates used to construct a literal graph problem. -/

namespace Papers.RationalityTen.GraphProblemCertificate

open GrowthDAG SparseGrowthDAG GrowthBitsets ConcreteGrowth

variable {n e : Nat}

theorem incidence_exact
    (lists : Fin n → List (Fin e)) (masks : Fin n → Nat)
    (rows : Fin e → List (Fin n)) (rowMasks : Fin e → Nat)
    (hmasks : ∀ c, masks c = PrimitiveBitsetGrowth.mask (lists c))
    (hrowMasks : ∀ q, rowMasks q = PrimitiveBitsetGrowth.mask (rows q))
    (hcoverage : ∀ c, (lists c).all (fun q => has (rows q) c) = true)
    (hsound : ∀ q, (rows q).all (fun c => has (lists c) q) = true)
    (q : Fin e) (c : Fin n) :
    (rowMasks q).testBit c.val = (masks c).testBit q.val := by
  have h := GrowthCacheCertificate.candidate_exact lists rows rowMasks
    (fun q => (hrowMasks q).trans (PrimitiveBitsetGrowth.mask_eq _))
    hcoverage hsound q c
  calc
    (rowMasks q).testBit c.val = bitAt (rowMasks q) c.val :=
      (bitAt_eq_testBit _ _).symm
    _ = has (lists c) q := h
    _ = bitAt (masks c) q.val := by
      rw [hmasks, PrimitiveBitsetGrowth.mask_eq, bitAt_ofList_eq_has]
    _ = (masks c).testBit q.val := bitAt_eq_testBit _ _

theorem kind_exact (kind : Fin n → Nat)
    (lists : Nat → List (Fin n)) (masks : Nat → Nat) (k : Nat)
    (hmasks : ∀ j, j < k → masks j = PrimitiveBitsetGrowth.mask (lists j))
    (hcoverage : ∀ c, has (lists (kind c)) c = true)
    (hsound : ∀ j, j < k → (lists j).all (fun c => decide (kind c = j)) = true)
    (j : Fin k) (c : Fin n) :
    (masks j.val).testBit c.val = decide (kind c = j.val) := by
  rw [hmasks j.val j.isLt, PrimitiveBitsetGrowth.mask_eq,
    ← bitAt_eq_testBit, bitAt_ofList_eq_has]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact List.all_eq_true.mp (hsound j.val j.isLt) c ((has_true _ _).mp h)
  · intro h
    have heq := of_decide_eq_true h
    simpa only [heq] using hcoverage c

#print axioms incidence_exact
#print axioms kind_exact

end Papers.RationalityTen.GraphProblemCertificate
