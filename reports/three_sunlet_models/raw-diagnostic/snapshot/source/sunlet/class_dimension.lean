module

public import sunlet.class_kernel
public import sunlet.dimension_lower_bound

/-! Exact dimension from the proved class-height kernel criterion. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Sunlet.ClassKernel

open ClassSelection OrbitHeight ExponentRank

variable {K G C : Type*} [Field K] [AddCommGroup G] [Fintype G] [Fintype C]
  [LinearOrder C] (P : InverseStablePartition G C)
  (σ : Set C) [DecidablePred (· ∈ σ)]

def relationMap : (ParamVar C C → ℚ) →ₗ[ℚ] (G × G → ℚ) where
  toFun w bc := w (.s (P.classOf bc.1)) + w (.t (P.classOf bc.2)) +
    if selectsU P.classOf σ bc.1 bc.2 then
      w (.u (P.classOf (bc.2 - bc.1))) + w (.h (P.classOf bc.2))
    else w (.v (P.classOf (bc.2 - bc.1))) + w (.h (P.classOf bc.1))
  map_add' w z := by funext bc; dsimp; split_ifs <;> ring
  map_smul' r w := by funext bc; dsimp; split_ifs <;> ring

theorem mem_ker_iff (w : ParamVar C C → ℚ) :
    w ∈ (relationMap P σ).ker ↔ IsRelation P σ w := by
  simp only [LinearMap.mem_ker, funext_iff, Prod.forall, relationMap,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, IsRelation, Equation]

def canonicalKer (hσ0 : P.zeroClass ∉ σ) :
    (Fin 4 → ℚ) →ₗ[ℚ] (relationMap P σ).ker :=
  (canonicalLinear P.zeroClass).codRestrict _ fun q =>
    (mem_ker_iff P σ _).mpr (canonical_isRelation P σ hσ0 (q 0) (q 1) (q 2) (q 3))

theorem finrank_ker (hmin : ∀ i, P.zeroClass ≤ i) (hσ0 : P.zeroClass ∉ σ)
    (hkill : KillsHeights P σ) : Module.finrank ℚ (relationMap P σ).ker = 4 := by
  have hinj : Function.Injective (canonicalKer P σ hσ0) := by
    intro q r h
    apply canonical_injective P.zeroClass P.zeroClass
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective (canonicalKer P σ hσ0) := by
    intro w
    refine ⟨decodeLinear P.zeroClass P.zeroClass w, ?_⟩
    apply Subtype.ext
    exact (relation_canonical P σ hmin hσ0 w ((mem_ker_iff P σ w).mp w.property) hkill).symm
  let E := LinearEquiv.ofBijective (canonicalKer P σ hσ0) ⟨hinj, hsurj⟩
  simpa using E.finrank_eq.symm

theorem finrank_range_add_four (hmin : ∀ i, P.zeroClass ≤ i) (hσ0 : P.zeroClass ∉ σ)
    (hkill : KillsHeights P σ) :
    Module.finrank ℚ (relationMap P σ).range + 4 = 5 * Fintype.card C := by
  have h := (relationMap P σ).finrank_range_add_finrank_ker
  rw [finrank_ker P σ hmin hσ0 hkill] at h
  simp only [Module.finrank_pi, Module.finrank_self, mul_one, card_paramVar] at h
  omega

def selectedMatrix : Matrix (G × G) (ParamVar C C) ℚ :=
  fun bc i => (selectedExponent P.classOf σ bc i : ℚ)

theorem selectedMatrix_mulVecLin : (selectedMatrix P σ).mulVecLin = relationMap P σ := by
  apply LinearMap.ext
  intro w
  funext bc
  change (∑ i, (selectedExponent P.classOf σ bc i : ℚ) * w i) = _
  simp only [selectedExponent]
  split_ifs <;>
    simp [uExponent, vExponent, relationMap, *, Finsupp.add_apply, Nat.cast_add,
      add_mul, Finset.sum_add_distrib, Finsupp.single_apply, add_assoc]

/-- Rational rank gives the genuine Krull lower bound, in every characteristic. -/
theorem coordinateRing_dimension_ge (hmin : ∀ i, P.zeroClass ≤ i)
    (hσ0 : P.zeroClass ∉ σ) (hkill : KillsHeights P σ) :
    (5 * Fintype.card C - 4 : ℕ) ≤
      ringKrullDim (MvPolynomial (G × G) K ⧸
        PolynomialImage.definingIdeal (Identified.coordinatePolynomial (K := K) P.classOf)) := by
  classical
  let M := selectedMatrix P σ
  have hplus : M.rank + 4 = 5 * Fintype.card C := by
    change Module.finrank ℚ (selectedMatrix P σ).mulVecLin.range + 4 = _
    rw [selectedMatrix_mulVecLin]
    exact finrank_range_add_four P σ hmin hσ0 hkill
  obtain ⟨I, r, hrinj, hspan, hr⟩ := exists_linearIndependent' ℚ M.row
  letI : Fintype I := Fintype.ofInjective r hrinj
  have hcard : Fintype.card I = M.rank := by
    rw [M.rank_eq_finrank_span_row, ← hspan]
    exact (finrank_span_eq_card hr).symm
  have halg : AlgebraicIndependent K (fun j =>
      Identified.coordinatePolynomial (K := K) P.classOf ((r j).2 - (r j).1, (r j).1)) :=
    ClassSelection.coordinate_subfamily_algebraicIndependent P.classOf σ r hr
  let A := PolynomialImage.imageAlgebra (Identified.coordinatePolynomial (K := K) P.classOf)
  let f : I → A := fun j =>
    ⟨Identified.coordinatePolynomial P.classOf ((r j).2 - (r j).1, (r j).1), by
      refine ⟨MvPolynomial.X ((r j).2 - (r j).1, (r j).1), ?_⟩
      simp [PolynomialImage.comorphism]⟩
  have hf : AlgebraicIndependent K f := AlgebraicIndependent.of_comp A.val halg
  letI : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective
    (PolynomialImage.comorphism (Identified.coordinatePolynomial (K := K) P.classOf)).rangeRestrict
    (PolynomialImage.comorphism (Identified.coordinatePolynomial (K := K) P.classOf)).rangeRestrict_surjective
  have hd := DimensionAlgebra.card_le_ringKrullDim_of_algebraicIndependent K A f hf
  have hsize : Fintype.card I = 5 * Fintype.card C - 4 := by omega
  rw [ringKrullDim_eq_of_ringEquiv
    (PolynomialImage.coordinateRingEquivImage
      (Identified.coordinatePolynomial (K := K) P.classOf)).toRingEquiv]
  simpa only [hsize] using hd

/-- Combining the independent normalized upper bound with the actual initial
rank yields equality. The sign criterion is discharged by the order-selection
argument, rather than accepted as a principal theorem hypothesis. -/
theorem imageClosure_dimension_eq [Infinite K]
    (hmin : ∀ i, P.zeroClass ≤ i) (hσ0 : P.zeroClass ∉ σ) (hkill : KillsHeights P σ) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) P.classOf))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  apply le_antisymm
  · apply Identified.imageClosure_dimension_le
    intro a
    simpa only [P.zero_class] using P.zero_iff a
  · rw [PolynomialImage.vanishingIdeal_imageClosure]
    exact coordinateRing_dimension_ge P σ hmin hσ0 hkill

end Sunlet.ClassKernel
