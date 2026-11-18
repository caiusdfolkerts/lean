module

public import sunlet.weighted_initial
public import sunlet.exponent_rank
public import sunlet.dimension_algebra
public import sunlet.polynomial_image
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! From the literal exponent matrix to the Krull dimension of the actual image algebra. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Sunlet.SelectedRelations Sunlet.SelectedExponents

namespace Sunlet.DimensionLowerBound

variable {K ι Ω : Type*} [Field K] [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω]

def selectedMatrix (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] : Matrix (ι × Ω) (ParamVar ι Ω) ℚ :=
  fun ab i => (selectedExponent π e o P ab i : ℚ)

theorem selectedMatrix_mulVecLin (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P : Set ι)
    [DecidablePred (· ∈ P)] :
    (selectedMatrix π e o P).mulVecLin = ExponentRank.relationMap π e o P := by
  apply LinearMap.ext
  intro w
  funext ab
  change (∑ i, (selectedExponent π e o P ab i : ℚ) * w i) =
    w (.s ab.2) + w (.t (π ab.1 ab.2)) +
      if selectsU π e o P ab.1 ab.2 then w (.u ab.1) + w (.h (π ab.1 ab.2))
      else w (.v ab.1) + w (.h ab.2)
  by_cases hs : selectsU π e o P ab.1 ab.2
  · simp [selectedExponent, hs, uExponent_dot, add_assoc]
  · simp [selectedExponent, hs, vExponent_dot, add_assoc]

/-- The complete lower bound of Theorem 2.3. The field may have any characteristic. -/
theorem coordinateRing_dimension_ge
    (π : ι → Equiv.Perm Ω) (e : ι) (o : Ω) (P N : Set ι)
    [DecidablePred (· ∈ P)]
    (he : π e = Equiv.refl Ω) (heP : e ∉ P)
    (hPN : Disjoint P N)
    (hder : ∀ a, a ≠ e → ∀ b, π a b ≠ b)
    (hPne : ∀ a ∈ P, a ≠ e) (hNne : ∀ a ∈ N, a ≠ e)
    (hPtwo : ∃ a ∈ P, ∃ b ∈ P, π a ≠ π b)
    (hNtwo : ∃ a ∈ N, ∃ b ∈ N, π a ≠ π b)
    (hPtr : TransitiveFamily π P) (hNtr : TransitiveFamily π N) :
    (3 * Fintype.card Ω + 2 * Fintype.card ι - 4 : ℕ) ≤
      ringKrullDim (MvPolynomial (ι × Ω) K ⧸
        PolynomialImage.definingIdeal (coordinatePolynomial (K := K) π)) := by
  classical
  let M := selectedMatrix π e o P
  have hplus : M.rank + 4 = 3 * Fintype.card Ω + 2 * Fintype.card ι := by
    change Module.finrank ℚ (selectedMatrix π e o P).mulVecLin.range + 4 = _
    rw [selectedMatrix_mulVecLin]
    exact ExponentRank.finrank_range_add_four π e o P N he heP hPN hder hPne hNne
      hPtwo hNtwo hPtr hNtr
  obtain ⟨I, r, hrinj, hspan, hr⟩ := exists_linearIndependent' ℚ M.row
  letI : Fintype I := Fintype.ofInjective r hrinj
  have hcard : Fintype.card I = M.rank := by
    rw [M.rank_eq_finrank_span_row, ← hspan]
    exact (finrank_span_eq_card hr).symm
  have halg : AlgebraicIndependent K (fun j => coordinatePolynomial (K := K) π (r j)) := by
    exact WeightedInitial.coordinate_subfamily_algebraicIndependent π e o P he heP hder r hr
  let A := PolynomialImage.imageAlgebra (coordinatePolynomial (K := K) π)
  let x : I → A := fun j => ⟨coordinatePolynomial π (r j), by
    refine ⟨MvPolynomial.X (r j), ?_⟩
    simp [PolynomialImage.comorphism]⟩
  have hx : AlgebraicIndependent K x := by
    apply AlgebraicIndependent.of_comp A.val
    exact halg
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (PolynomialImage.comorphism (coordinatePolynomial (K := K) π)).rangeRestrict
    (PolynomialImage.comorphism (coordinatePolynomial (K := K) π)).rangeRestrict_surjective
  have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A x hx
  have hsize : Fintype.card I = 3 * Fintype.card Ω + 2 * Fintype.card ι - 4 := by omega
  rw [ringKrullDim_eq_of_ringEquiv
    (PolynomialImage.coordinateRingEquivImage (coordinatePolynomial (K := K) π)).toRingEquiv]
  simpa only [hsize] using hd

end Sunlet.DimensionLowerBound
