module

public import ToricPower.DualDiagonalFramedComplex

/-!
# Exact Laurent coefficients of the actual ring-linear dual matrix

A transposed framed monomial can connect two Laurent basis vectors only
when their total characters agree. In that case its coefficient is the
original periodic incidence at the exact difference of their first-factor
characters. This proves the required grading for the actual `R`-linear
complex, rather than assigning a grading to its cohomology afterwards.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  {S T : Set (Fin s)} {d : ℕ}
  (F : DiagonalCellFrames A S T d) (G : DiagonalCellFrames A S T (d+1))
  (i : NormalizedCell A d) (j : NormalizedCell A (d+1))
  (p q : rayCharacterMonoid A S × rayCharacterMonoid A T)

/-- The genuine difference of the two first-factor Laurent characters. -/
def dualFramedDisplacement : Fin n → ℤ :=
  (G.left j + q.1.val) - (F.left i + p.1.val)

/-- Matching the actual polynomial exponent is equivalent to matching
both total weight and the literal original incidence displacement. -/
theorem diagonalFramedMonomial_add_iff (t : DiagonalGlobalColumnTerm k A d j) :
    (t.val.1 = i ∧ diagonalFramedMonomial k A F G j t + p = q) ↔
      (t.val = (i, dualFramedDisplacement A F G i j p q) ∧
        F.dualWeight i p = G.dualWeight j q) := by
  constructor
  · rintro ⟨cell, monomial⟩
    have left := congrArg (fun v : rayCharacterMonoid A S × rayCharacterMonoid A T =>
      v.1.val) monomial
    have right := congrArg (fun v : rayCharacterMonoid A S × rayCharacterMonoid A T =>
      v.2.val) monomial
    change t.val.2 + F.left t.val.1 - G.left j + p.1.val = q.1.val at left
    change -t.val.2 + F.right t.val.1 - G.right j + p.2.val = q.2.val at right
    rw [cell] at left right
    constructor
    · apply Prod.ext cell
      funext c
      have h := congrFun left c
      dsimp [dualFramedDisplacement] at h ⊢
      omega
    · funext c
      have hL := congrFun left c
      have hR := congrFun right c
      dsimp [DiagonalCellFrames.dualWeight] at hL hR ⊢
      omega
  · rintro ⟨term, weight⟩
    have cell := congrArg Prod.fst term
    have character := congrArg Prod.snd term
    refine ⟨cell, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · change t.val.2 + F.left t.val.1 - G.left j + p.1.val = q.1.val
      rw [cell, character]
      funext c
      dsimp [dualFramedDisplacement]
      omega
    · change -t.val.2 + F.right t.val.1 - G.right j + p.2.val = q.2.val
      rw [cell, character]
      funext c
      have h := congrFun weight c
      dsimp [dualFramedDisplacement, DiagonalCellFrames.dualWeight] at h ⊢
      omega

local instance framedCoefficientTermsFintype : Fintype (DiagonalGlobalColumnTerm k A d j) :=
  Fintype.ofFinite _

/-- Every polynomial coefficient of the actual transposed matrix,
including the vanishing between different total characters. -/
theorem diagonalFramedGlobalColumn_mul_coeff (r : k) :
    (diagonalFramedGlobalColumn k A F G j i * AddMonoidAlgebra.single p r).coeff q =
      if F.dualWeight i p = G.dualWeight j q then
        diagonalGlobalColumn k A d j (i, dualFramedDisplacement A F G i j p q) * r
      else 0 := by
  let candidate := (i, dualFramedDisplacement A F G i j p q)
  have summand (t : DiagonalGlobalColumnTerm k A d j) :
      ((Finsupp.single t.val.1
          (AddMonoidAlgebra.single (diagonalFramedMonomial k A F G j t)
            (diagonalGlobalColumn k A d j t.val)) :
        NormalizedCell A d →₀ DiagonalChartRing k A S T) i *
          AddMonoidAlgebra.single p r).coeff q =
      if t.val = candidate ∧ F.dualWeight i p = G.dualWeight j q then
        diagonalGlobalColumn k A d j t.val * r else 0 := by
    have equivalent := diagonalFramedMonomial_add_iff k A F G i j p q t
    by_cases cell : t.val.1 = i
    · rw [cell, Finsupp.single_eq_same, AddMonoidAlgebra.single_mul_single]
      by_cases exponent : diagonalFramedMonomial k A F G j t + p = q
      · have matchTerm := equivalent.mp ⟨cell, exponent⟩
        rw [exponent, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
          if_pos matchTerm]
      · have mismatch : ¬(t.val = candidate ∧ F.dualWeight i p = G.dualWeight j q) :=
          fun h => exponent (equivalent.mpr h).2
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne (Ne.symm exponent),
          if_neg mismatch]
    · have mismatch : ¬(t.val = candidate ∧ F.dualWeight i p = G.dualWeight j q) :=
        fun h => cell (equivalent.mpr h).1
      rw [Finsupp.single_eq_of_ne (Ne.symm cell), zero_mul, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply, if_neg mismatch]
  change (AddMonoidAlgebra.coeffLinearEquiv k
    (diagonalFramedGlobalColumn k A F G j i * AddMonoidAlgebra.single p r)) q = _
  unfold diagonalFramedGlobalColumn
  rw [Finsupp.finsetSum_apply, Finset.sum_mul, map_sum, Finsupp.finsetSum_apply]
  change (∑ t : DiagonalGlobalColumnTerm k A d j,
    ((Finsupp.single t.val.1
      (AddMonoidAlgebra.single (diagonalFramedMonomial k A F G j t)
        (diagonalGlobalColumn k A d j t.val)) :
      NormalizedCell A d →₀ DiagonalChartRing k A S T) i *
        AddMonoidAlgebra.single p r).coeff q) = _
  simp_rw [summand]
  by_cases weight : F.dualWeight i p = G.dualWeight j q
  · rw [if_pos weight]
    simp only [weight, and_true]
    by_cases supported : candidate ∈ (diagonalGlobalColumn k A d j).support
    · let t₀ : DiagonalGlobalColumnTerm k A d j := ⟨candidate, supported⟩
      calc
        (∑ t : DiagonalGlobalColumnTerm k A d j,
          if t.val = candidate then diagonalGlobalColumn k A d j t.val * r else 0) =
          ∑ t : DiagonalGlobalColumnTerm k A d j,
            if t = t₀ then diagonalGlobalColumn k A d j candidate * r else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          by_cases equal : t = t₀
          · subst t
            simp only [t₀, if_true]
          · have unequal : t.val ≠ candidate := fun h => equal (Subtype.ext h)
            rw [if_neg unequal, if_neg equal]
        _ = diagonalGlobalColumn k A d j candidate * r := by simp
    · have zero : diagonalGlobalColumn k A d j candidate = 0 :=
        Finsupp.notMem_support_iff.mp supported
      change _ = diagonalGlobalColumn k A d j candidate * r
      rw [zero, zero_mul]
      apply Finset.sum_eq_zero
      intro t ht
      have unequal : t.val ≠ candidate := by
        intro equal
        apply supported
        rw [← equal]
        exact t.property
      rw [if_neg unequal]
  · rw [if_neg weight]
    simp only [weight, and_false, if_false, Finset.sum_const_zero]

end ToricPower.IntegralArrangement
