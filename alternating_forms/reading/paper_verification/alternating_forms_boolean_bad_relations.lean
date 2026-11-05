module

public import PaperVerification.AlternatingFormsBooleanGoodSubsets
public import PaperVerification.AlternatingFormsBooleanPolynomialRelations
public import PaperVerification.AlternatingFormsPolynomialMinors
public import PaperVerification.AlternatingFormsWeights

/-!
# One genuine polynomial relation for every bad Boolean monomial

The two orientations use the same pair of parameter-dependent linear forms.
For each excluded subset, its first wall violation gives an actual central
prefix.  The corresponding normalized relation specializes at zero to that
subset's monomial.  Consequently the complete bad-by-bad coefficient minor
is nonzero, uniformly in the number of variables and the degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanBadRelations

open scoped BigOperators Classical
open MvPolynomial BooleanWalks BooleanCoefficients BooleanPolynomialRelations

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
variable {m q : ℕ}

def orientation (m : ℕ) : Bool → Equiv.Perm (Fin m)
  | false => Equiv.refl _
  | true => Fin.revPerm

def prefixSet (e : Equiv.Perm (Fin m)) (r : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ (e i).val < r

@[simp] theorem mem_prefixSet (e : Equiv.Perm (Fin m)) (r : ℕ) (i : Fin m) :
    i ∈ prefixSet e r ↔ (e i).val < r := by simp [prefixSet]

theorem prefixSet_card (e : Equiv.Perm (Fin m)) (r : ℕ) (hr : r ≤ m) :
    (prefixSet e r).card = r := by
  let E : (prefixSet e r) ≃ Fin r :=
    { toFun := fun i ↦ ⟨(e i.val).val, (mem_prefixSet e r i.val).mp i.property⟩
      invFun := fun j ↦ ⟨e.symm ⟨j.val, lt_of_lt_of_le j.isLt hr⟩, by
        simp only [mem_prefixSet, Equiv.apply_symm_apply]
        exact j.isLt⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply e.injective
        simp only [Equiv.apply_symm_apply]
      right_inv := by intro j; apply Fin.ext; simp }
  rw [← Fintype.card_coe, Fintype.card_congr E, Fintype.card_fin]

/-- A prefix in one of the two actual orders; its selected positions are
kept as a subset of the original variable set. -/
structure CentralPrefix (S : Finset (Fin m)) where
  reflected : Bool
  half : ℕ
  length_le : 2*half+1 ≤ m
  cardinality : (S.filter fun i ↦
    (orientation m reflected i).val < 2*half+1).card = half+1

theorem exists_centralPrefix (S : FixedSubsets (Fin m) q) (hS : ¬Good S) :
    Nonempty (CentralPrefix S.val) := by
  rcases bad_has_central_prefix S hS with h | h
  · obtain ⟨r, hr, hc⟩ := h
    exact ⟨⟨false, r, hr, hc⟩⟩
  · obtain ⟨r, hr, hc⟩ := h
    refine ⟨⟨true, r, hr, ?_⟩⟩
    unfold prefixCount reverse at hc
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ (fun i j h ↦ Fin.rev_inj.mp h)] at hc
    exact hc

namespace CentralPrefix

variable {S : Finset (Fin m)}

def vertices (c : CentralPrefix S) : Finset (Fin m) :=
  prefixSet (orientation m c.reflected) (2*c.half+1)

theorem vertices_card (c : CentralPrefix S) : c.vertices.card = 2*c.half+1 :=
  prefixSet_card _ _ c.length_le

def selected (c : CentralPrefix S) : FixedSubsets c.vertices (c.half+1) :=
  ⟨S.subtype (fun i ↦ i ∈ c.vertices), by
    rw [Finset.card_subtype]
    simpa only [vertices, mem_prefixSet] using c.cardinality⟩

def tail (c : CentralPrefix S) : Finset (Fin m) := S.filter fun i ↦ i ∉ c.vertices

def weight (c : CentralPrefix S) (i : Fin m) : ℕ :=
  2^((orientation m c.reflected i).val+1)

/-- The cost of every correction is strictly larger than that of the
original selected prefix.  The injective coordinate map prevents duplicate
positions from being silently dropped by the finite-set image. -/
theorem correction_pos (c : CentralPrefix S)
    (j : {i : Fin m // i ∉ c.vertices}) (T : FixedSubsets c.vertices c.half) :
    0 < correctionExponent c.weight c.vertices c.selected.val T.val j.val := by
  let e := orientation m c.reflected
  let f : c.vertices → ℕ := fun i ↦ (e i.val).val
  have hinj : Function.Injective f := by
    intro i k h
    apply Subtype.ext
    exact e.injective (Fin.ext h)
  have hprefix : c.selected.val.image f ⊆ Finset.range (2*c.half+1) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr ((mem_prefixSet e _ i.val).mp i.property)
  have hlate : 2*c.half+1 ≤ (e j.val).val := by
    have hn : ¬(e j.val).val < 2*c.half+1 := by
      intro h
      exact j.property ((mem_prefixSet e _ j.val).mpr h)
    omega
  have hc := replacement_pair_cost_strict (c.selected.val.image f) (T.val.image f)
    (2*c.half+1) (e j.val).val hprefix hlate
  rw [Finset.sum_image (fun a ha b hb h ↦ hinj h),
    Finset.sum_image (fun a ha b hb h ↦ hinj h)] at hc
  apply Nat.sub_pos_iff_lt.mpr
  change cost c.weight c.vertices c.selected.val <
    c.weight j.val + cost c.weight c.vertices T.val
  simpa only [cost, weight, f, e, Nat.add_comm] using hc

def relation (c : CentralPrefix S) : MvPolynomial (Fin m) (Polynomial K) :=
  normalizedRelation c.weight c.vertices c.half c.selected c.tail

theorem relation_at_zero (c : CentralPrefix S) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : K)) c.relation =
      subsetMonomial S := by
  rw [relation, normalizedRelation_at_zero _ _ _ _ _ c.correction_pos,
    subsetMonomial_eq_prod]
  have hprod : (∏ i ∈ c.selected.val, (X i.val : MvPolynomial (Fin m) K)) =
      ∏ i ∈ S.filter (fun i ↦ i ∈ c.vertices), X i := by
    rw [← Finset.subtype_map (fun i ↦ i ∈ c.vertices)]
    simp only [Finset.prod_map]
    rfl
  rw [hprod]
  exact Finset.prod_filter_mul_prod_filter_not S (fun i ↦ i ∈ c.vertices) X

end CentralPrefix

abbrev BadSubset (m q : ℕ) := {S : FixedSubsets (Fin m) q // ¬Good S}

instance badSubsetFintype (m q : ℕ) : Fintype (BadSubset m q) := Fintype.ofFinite _

def chosenPrefix (S : BadSubset m q) : CentralPrefix S.val.val :=
  Classical.choice (exists_centralPrefix S.val S.property)

def badRelation (S : BadSubset m q) : MvPolynomial (Fin m) (Polynomial K) :=
  (chosenPrefix S).relation

theorem badRelation_at_zero (S : BadSubset m q) :
    MvPolynomial.map (Polynomial.evalRingHom (0 : K)) (badRelation S) =
      monomial (subsetExponent S.val.val) 1 :=
  (chosenPrefix S).relation_at_zero

theorem badExponent_injective :
    Function.Injective (fun S : BadSubset m q ↦ subsetExponent S.val.val) := by
  intro S T h
  apply Subtype.ext
  apply Subtype.ext
  exact subsetExponent_injective h

/-- A single all-bad coefficient minor, over the ordinary parameter polynomial
ring, specializes to the identity in every dimension and every degree. -/
theorem badRelation_coefficient_det_ne_zero (m q : ℕ) :
    (PolynomialMinors.coefficientMatrix
      (fun S : BadSubset m q ↦ subsetExponent S.val.val)
      (badRelation (K := K))).det ≠ 0 :=
  PolynomialMinors.coefficient_det_ne_zero_of_monomial_specialization
    (Polynomial.evalRingHom (0 : K)) _ badExponent_injective _ badRelation_at_zero

def forwardWeight (m : ℕ) (i : Fin m) : ℕ := 2^(i.val+1)
def backwardWeight (m : ℕ) (i : Fin m) : ℕ := 2^(i.rev.val+1)

/-- All rows use just these two forms.  Reversing a prefix exchanges the
two displayed generators of the same ordinary quotient ideal. -/
theorem badRelation_mem_quotientIdeal (φ : K →+* L) (t : L) (ht : t ≠ 0)
    (S : BadSubset m q) :
    MvPolynomial.map (Polynomial.eval₂RingHom φ t) (badRelation S) ∈
      BooleanQuotient.quotientIdeal
        (fun i ↦ t^(forwardWeight m i)) (fun i ↦ t^(backwardWeight m i)) := by
  let c := chosenPrefix S
  change MvPolynomial.map (Polynomial.eval₂RingHom φ t)
    (normalizedRelation c.weight c.vertices c.half c.selected c.tail) ∈ _
  have hle (j : {i : Fin m // i ∉ c.vertices}) (T : FixedSubsets c.vertices c.half) :
      cost c.weight c.vertices c.selected.val ≤
        c.weight j.val + cost c.weight c.vertices T.val := by
    have hp := c.correction_pos j T
    unfold correctionExponent at hp
    omega
  cases hdir : c.reflected with
  | false =>
      have hw : c.weight = forwardWeight m := by
        funext i
        simp [CentralPrefix.weight, forwardWeight, hdir, orientation]
      have h := normalizedRelation_mem_quotientIdeal φ t ht c.weight c.vertices c.half
        c.vertices_card c.selected c.tail (fun i ↦ t^(backwardWeight m i)) hle
      rw [hw] at h ⊢
      exact h
  | true =>
      have hw : c.weight = backwardWeight m := by
        funext i
        simp [CentralPrefix.weight, backwardWeight, hdir, orientation]
      have h := normalizedRelation_mem_quotientIdeal φ t ht c.weight c.vertices c.half
        c.vertices_card c.selected c.tail (fun i ↦ t^(forwardWeight m i)) hle
      have hcomm (b d : Fin m → L) :
          BooleanQuotient.quotientIdeal b d = BooleanQuotient.quotientIdeal d b := by
        simp only [BooleanQuotient.quotientIdeal, Set.pair_comm]
      rw [hw] at h ⊢
      rw [hcomm (fun i ↦ t^(backwardWeight m i))
        (fun i ↦ t^(forwardWeight m i))] at h
      exact h

end PaperVerification.AlternatingForms.BooleanBadRelations
