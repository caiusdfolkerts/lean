module
prelude
public import GraphGrowthConstraints

@[expose] public section

/-! Soundness of every graph-conditioned branching rule. -/

namespace Papers.RationalityTen.GraphGrowthConstraints

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning

variable {n r e v k : Nat}

theorem list_subset_of_included (S B : List (Fin n))
    (hsub : Included (family S) (family B)) : S ⊆ B := by
  intro c hc
  exact (has_true B c).mp (hsub c ((has_true S c).mpr hc))

theorem union_bit_mono (features : Fin n → Nat) (S B : List (Fin n))
    (hsub : Included (family S) (family B)) (q : Nat)
    (hq : (unionValues features S).testBit q = true) :
    (unionValues features B).testBit q = true := by
  obtain ⟨c, hc, hcq⟩ := (bitAt_unionValues features S q).mp
    ((bitAt_eq_testBit _ _).trans hq)
  exact (bitAt_eq_testBit _ _).symm.trans
    ((bitAt_unionValues features B q).mpr
      ⟨c, list_subset_of_included S B hsub hc, hcq⟩)

theorem missing_union_witness (features : Fin n → Nat)
    (S B : List (Fin n)) (q : Nat)
    (hB : (unionValues features B).testBit q = true)
    (hS : (unionValues features S).testBit q = false) :
    ∃ c, c ∈ B ∧ c ∉ S ∧ (features c).testBit q = true := by
  obtain ⟨c, hc, hcq⟩ := (bitAt_unionValues features B q).mp
    ((bitAt_eq_testBit _ _).trans hB)
  refine ⟨c, hc, ?_, (bitAt_eq_testBit _ _).symm.trans hcq⟩
  intro hcS
  have hh := (bitAt_unionValues features S q).mpr ⟨c, hcS, hcq⟩
  exact Bool.noConfusion (((bitAt_eq_testBit _ _).symm.trans hh).symm.trans hS)

theorem kind_capacity (D : Problem n r e v k) (S B : List (Fin n))
    (available : Nat) (hB : Target D B) (havail : Available S B available)
    (j : Fin k) :
    D.quota j.val ≤ kindCount D.kind S j.val +
      FiniteMaskSets.card n (Nat.land available (D.cache.kinds j.val)) := by
  have hsub : (B.filter fun c => decide (D.kind c = j.val)) ⊆
      (S.filter fun c => decide (D.kind c = j.val)) ++
        FiniteMaskSets.elements n (Nat.land available (D.cache.kinds j.val)) := by
    intro c hc
    obtain ⟨hcB, hcKind⟩ := List.mem_filter.mp hc
    by_cases hcS : c ∈ S
    · exact List.mem_append_left _ (List.mem_filter.mpr ⟨hcS, hcKind⟩)
    · apply List.mem_append_right
      apply (FiniteMaskSets.mem_elements c).mpr
      rw [FiniteMaskSets.testBit_land, havail c hcB hcS, D.kind_exact]
      simpa only [Bool.true_and] using hcKind
  have hlen := List.Nodup.length_le_of_subset (hB.nodup.filter _) hsub
  rw [List.length_append] at hlen
  change kindCount D.kind B j.val ≤ kindCount D.kind S j.val +
    FiniteMaskSets.card n (Nat.land available (D.cache.kinds j.val)) at hlen
  rw [hB.exactQuota j] at hlen
  exact hlen

/-- This finite inequality is supplied by the generic incidence-capacity
theorem.  It contains no geometric or catalogue assumption. -/
def VertexCapacitySound (D : Problem n r e v k) : Prop :=
  ∀ S B available, Target D B → S.Nodup →
    Included (family S) (family B) → Available S B available →
    ∀ a, vertexCount D B a ≤ vertexUpper D S available a

/-- A checked rule supplies an actual missing target cell among its candidates.
Capacity rules have an empty candidate mask and therefore prove impossibility.
-/
theorem ruleCheck_sound (D : Problem n r e v k)
    (hvertex : VertexCapacitySound D)
    (S B : List (Fin n)) (selected available : Nat)
    (hselected : selected = ofList S)
    (hB : Target D B) (hnd : S.Nodup)
    (hsub : Included (family S) (family B))
    (havail : Available S B available) (rule : Rule r e v k)
    (hcheck : ruleCheck D S selected available rule = true) :
    ∃ c, c ∈ B ∧ c ∉ S ∧ (candidates D rule).testBit c.val = true := by
  cases rule with
  | ridge q owner =>
    obtain ⟨howner, hopen⟩ := Bool.and_eq_true_iff.mp hcheck
    let a : Fin n := ⟨owner, of_decide_eq_true howner⟩
    have hm : Nat.land selected (D.cache.candidates q) = 2^a.val := by
      simpa only [a, ← PrimitiveBitsetGrowth.singleton_eq, PrimitiveBitsetGrowth.singleton]
        using of_decide_eq_true hopen
    obtain ⟨c, hcB, hcS, hcq⟩ := missing_cell (fun c => has (D.ridgeList c))
      (family B) (family S) q a hsub hB.boundary.mates
      (openCheck_sound _ _ _ _
        (FastBatchedGrowth.openCheck_of_mask D.cache S selected hselected q a hm))
    refine ⟨c, (has_true B c).mp hcB, ?_, ?_⟩
    · intro hc
      exact Bool.noConfusion (hcS.symm.trans ((has_true S c).mpr hc))
    · simpa only [candidates, bitAt_eq_testBit] using
        (D.cache.candidates_exact q c).trans hcq
  | edge q =>
    obtain ⟨hreq, hnot⟩ := Bool.and_eq_true_iff.mp hcheck
    have hfalse : (edgeUnion D S).testBit q.val = false := by
      cases hx : (edgeUnion D S).testBit q.val <;> simp_all only [Bool.not_true, Bool.false_eq_true]
    obtain ⟨c, hcB, hcS, hcq⟩ := missing_union_witness D.edges S B q.val
      (hB.edgeCover q hreq) hfalse
    exact ⟨c, hcB, hcS, (D.edgeRows_exact q c).trans hcq⟩
  | nonedge q possible =>
    obtain ⟨hpossible, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
    obtain ⟨hcount, hbits⟩ := Bool.and_eq_true_iff.mp hrest
    obtain ⟨hbit, hnot⟩ := Bool.and_eq_true_iff.mp hbits
    have hsubPossible := possibleMissingCheck_sound D S B available possible havail hpossible
    have hcard : FiniteMaskSets.card e possible ≤
        FiniteMaskSets.card e (missingUnion D B) := by
      rw [of_decide_eq_true hcount, hB.missingCard]
      exact Nat.le_refl _
    have hBbit := FiniteMaskSets.bit_imp_of_card_le hsubPossible hcard q hbit
    have hfalse : (missingUnion D S).testBit q.val = false := by
      cases hx : (missingUnion D S).testBit q.val <;> simp_all only [Bool.not_true, Bool.false_eq_true]
    obtain ⟨c, hcB, hcS, hcq⟩ := missing_union_witness D.missing S B q.val hBbit hfalse
    exact ⟨c, hcB, hcS, (D.missingRows_exact q c).trans hcq⟩
  | kindCapacity j =>
    have hbound := kind_capacity D S B available hB havail j
    have hbad := of_decide_eq_true hcheck
    exact False.elim (Nat.not_lt_of_ge hbound hbad)
  | vertexCapacity a =>
    have hbound := hvertex S B available hB hnd hsub havail a
    have hlower := hB.incidence a
    have hbad : vertexUpper D S available a < D.minimumIncidence := of_decide_eq_true hcheck
    exact False.elim (by omega)
  | nonedgeCapacity possible =>
    obtain ⟨hpossible, hbad⟩ := Bool.and_eq_true_iff.mp hcheck
    have hupper := FiniteMaskSets.card_le_of_bit_imp
      (possibleMissingCheck_sound D S B available possible havail hpossible)
    have hlower := FiniteMaskSets.card_le_of_bit_imp (n := e)
      (fun q : Fin e => union_bit_mono D.missing S B hsub q.val)
    change FiniteMaskSets.card e (missingUnion D S) ≤
      FiniteMaskSets.card e (missingUnion D B) at hlower
    rw [hB.missingCard] at hupper hlower
    rcases Bool.or_eq_true_iff.mp hbad with hbad | hbad
    · have hbad' := of_decide_eq_true hbad
      exact False.elim (Nat.not_lt_of_ge hlower hbad')
    · have hbad' := of_decide_eq_true hbad
      exact False.elim (Nat.not_lt_of_ge hupper hbad')

#print axioms ruleCheck_sound

end Papers.RationalityTen.GraphGrowthConstraints
