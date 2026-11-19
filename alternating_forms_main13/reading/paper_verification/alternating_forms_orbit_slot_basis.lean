module

public import PaperVerification.AlternatingFormsOrbitExteriorCoordinates

/-!
# Exterior bases indexed by oriented coordinate pairs

The orbit calculations use blockwise coordinate slots rather than the
usual increasing-pair index.  The three explicit conditions below say
exactly that each unordered pair occurs once with a chosen orientation.
They provide a genuine exterior basis and identify its coefficients with
the alternating matrix entries.  No rank or spanning result is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K ν ι : Type*} [CommRing K]
  [Fintype ν] [DecidableEq ν] [Fintype ι] [DecidableEq ι]

/-- Concrete combinatorial data asserting that the slots orient all
unordered pairs exactly once. -/
structure OrbitPairSlots (row col : ι → ν) : Prop where
  injective : Function.Injective (fun i => (row i, col i))
  no_reverse : ∀ i j, ¬ (row i = col j ∧ col i = row j)
  covers : ∀ u v, u ≠ v →
    ∃ i, (row i = u ∧ col i = v) ∨ (row i = v ∧ col i = u)

theorem OrbitPairSlots.row_ne_col {row col : ι → ν}
    (h : OrbitPairSlots row col) (i : ι) : row i ≠ col i := by
  intro hi
  exact h.no_reverse i i ⟨hi, hi.symm⟩

/-- The coordinate of a literal slot sum at its own oriented slot is
exactly its input coefficient. -/
theorem orbitTwoFormOfSlots_coefficient {row col : ι → ν}
    (h : OrbitPairSlots row col) (c : ι → K) (i : ι) :
    orbitExteriorCoefficientMatrix (orbitTwoFormOfSlots row col c)
      (row i) (col i) = c i := by
  rw [orbitExteriorCoefficientMatrix_ofSlots]
  have hs : ∀ j,
      c j *
        ((Pi.basisFun K ν (row j)) (row i) * (Pi.basisFun K ν (col j)) (col i) -
          (Pi.basisFun K ν (row j)) (col i) * (Pi.basisFun K ν (col j)) (row i)) =
        if j = i then c i else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [Pi.basisFun_apply, Pi.single_apply, h.row_ne_col i,
        (h.row_ne_col i).symm]
    · have hp : row j ≠ row i ∨ col j ≠ col i := by
        by_cases hr : row j = row i
        · exact Or.inr (fun hc => hji (h.injective (Prod.ext hr hc)))
        · exact Or.inl hr
      have hq : row j ≠ col i ∨ col j ≠ row i :=
        not_and_or.mp (h.no_reverse j i)
      rcases hp with hp | hp <;> rcases hq with hq | hq <;>
        simp [Pi.basisFun_apply, Pi.single_apply, hji, hp, hq,
          Ne.symm hp, Ne.symm hq]
  simp only [hs, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Every exterior 2-form is reconstructed from these literal matrix
entries.  Completeness of the slots is used explicitly here. -/
theorem orbitTwoFormOfSlots_reconstruct {row col : ι → ν}
    (h : OrbitPairSlots row col) (f : ⋀[K]^2 (ν → K)) :
    orbitTwoFormOfSlots row col
      (fun i => orbitExteriorCoefficientMatrix f (row i) (col i)) = f := by
  apply orbitExteriorCoefficientMatrix_injective
  ext u v
  by_cases huv : u = v
  · subst v
    rw [orbitExteriorCoefficientMatrix_diagonal, orbitExteriorCoefficientMatrix_diagonal]
  · obtain ⟨i, hi | hi⟩ := h.covers u v huv
    · rw [← hi.1, ← hi.2, orbitTwoFormOfSlots_coefficient h]
    · rw [← hi.1, ← hi.2]
      rw [orbitExteriorCoefficientMatrix_skew
        (orbitTwoFormOfSlots row col
          (fun j => orbitExteriorCoefficientMatrix f (row j) (col j)))
        (row i) (col i), orbitTwoFormOfSlots_coefficient h]
      exact (orbitExteriorCoefficientMatrix_skew f (row i) (col i)).symm

/-- The explicit coordinate equivalence; its inverse is the indicated
collection of matrix entries of the actual exterior element. -/
def orbitSlotLinearEquiv {row col : ι → ν} (h : OrbitPairSlots row col) :
    (ι → K) ≃ₗ[K] (⋀[K]^2 (ν → K)) where
  toFun := orbitTwoFormOfSlots row col
  invFun f i := orbitExteriorCoefficientMatrix f (row i) (col i)
  left_inv c := by
    funext i
    exact orbitTwoFormOfSlots_coefficient h c i
  right_inv := orbitTwoFormOfSlots_reconstruct h
  map_add' c d := by
    simp only [orbitTwoFormOfSlots, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [orbitTwoFormOfSlots, Pi.smul_apply, smul_eq_mul,
      Finset.smul_sum, smul_smul, RingHom.id_apply]

theorem orbitSlotLinearEquiv_apply {row col : ι → ν}
    (h : OrbitPairSlots row col) (c : ι → K) :
    orbitSlotLinearEquiv (K := K) h c = orbitTwoFormOfSlots row col c := rfl

theorem orbitSlotLinearEquiv_symm_apply {row col : ι → ν}
    (h : OrbitPairSlots row col) (f : ⋀[K]^2 (ν → K)) (i : ι) :
    (orbitSlotLinearEquiv h).symm f i =
      orbitExteriorCoefficientMatrix f (row i) (col i) := rfl

/-- The actual second-exterior-power basis indexed by the orbit slots. -/
def orbitSlotBasis {row col : ι → ν} (h : OrbitPairSlots row col) :
    Module.Basis ι K (⋀[K]^2 (ν → K)) :=
  (Pi.basisFun K ι).map (orbitSlotLinearEquiv h)

theorem orbitSlotBasis_apply {row col : ι → ν}
    (h : OrbitPairSlots row col) (i : ι) :
    orbitSlotBasis (K := K) h i = exteriorPower.ιMulti K 2
      ![Pi.basisFun K ν (row i), Pi.basisFun K ν (col i)] := by
  simp only [orbitSlotBasis, Module.Basis.map_apply, orbitSlotLinearEquiv_apply,
    orbitTwoFormOfSlots, Pi.basisFun_apply, Pi.single_apply]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem orbitSlotBasis_repr {row col : ι → ν}
    (h : OrbitPairSlots row col) (f : ⋀[K]^2 (ν → K)) (i : ι) :
    (orbitSlotBasis h).repr f i =
      orbitExteriorCoefficientMatrix f (row i) (col i) := by
  change (Pi.basisFun K ι).repr ((orbitSlotLinearEquiv h).symm f) i = _
  rw [Pi.basisFun_repr]
  rfl

end PaperVerification.AlternatingForms
