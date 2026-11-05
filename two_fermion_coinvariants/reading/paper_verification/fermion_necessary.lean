module

public import PaperVerification.FermionRadical
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# Necessity of the subset-sum condition for separated ordinary moments

If a subset sum vanishes in a residue field, put one transcendental parameter
on that subset and a root of `G` on its complement. In an algebraically closed
extension, each monic cover has a preimage of the chosen value. This gives an
ordinary moment zero at which one cover value is transcendental. A finite
quotient would make that value integral, which is impossible.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

section TranscendentalWitness

variable {K L F : Type*} [CommRing K] [Field L] [Field F] [IsAlgClosed F]
variable [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
variable {n : ℕ}

theorem not_finite_separated_of_zero_subset_sum
    (β : Fin n → K) (G : Polynomial K) (φ : Fin n → Polynomial K)
    (hG : G.Monic) (hGpos : 0 < G.natDegree)
    (hφ : ∀ i, (φ i).Monic) (hφpos : ∀ i, 0 < (φ i).natDegree)
    (U : Finset (Fin n)) (hU : U.Nonempty)
    (hβU : (∑ i ∈ U, algebraMap K F (β i)) = 0)
    (t : F) (ht : Transcendental L t) :
    ¬ Module.Finite K (MvPolynomial (Fin n) K ⧸ separatedOrdinaryIdeal β G φ) := by
  classical
  intro hfinite
  letI := hfinite
  have hGdegree : (G.map (algebraMap K F)).degree ≠ 0 := by
    apply ne_of_gt
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rwa [hG.natDegree_map]
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (G.map (algebraMap K F)) hGdegree
  have hGa : Polynomial.aeval a G = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using ha
  let y : Fin n → F := fun i ↦ if i ∈ U then t else a
  have hroots : ∀ i : Fin n, ∃ z : F, Polynomial.aeval z (φ i) = y i := by
    intro i
    have hdegree : ((φ i).map (algebraMap K F) - Polynomial.C (y i)).degree ≠ 0 := by
      apply ne_of_gt
      apply Polynomial.natDegree_pos_iff_degree_pos.mp
      rw [Polynomial.natDegree_sub_C, (hφ i).natDegree_map]
      exact hφpos i
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
      ((φ i).map (algebraMap K F) - Polynomial.C (y i)) hdegree
    refine ⟨z, ?_⟩
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_map, Polynomial.aeval_def, sub_eq_zero] using hz
  choose ρ hρ using hroots
  let x : Fin n → MvPolynomial (Fin n) K :=
    fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)
  let e : MvPolynomial (Fin n) K →ₐ[K] F := MvPolynomial.aeval ρ
  have hex (i : Fin n) : e (x i) = y i := by
    dsimp only [x]
    rw [← Polynomial.aeval_algHom_apply]
    simpa only [e, MvPolynomial.aeval_X] using hρ i
  have hzero (k : ℕ) :
      (∑ i, y i ^ k * (algebraMap K F (β i) * Polynomial.aeval (y i) G)) = 0 := by
    calc
      _ = ∑ i ∈ U, y i ^ k * (algebraMap K F (β i) * Polynomial.aeval (y i) G) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ U)
        intro i _ hi
        simp [y, hi, hGa]
      _ = ∑ i ∈ U, algebraMap K F (β i) * (t ^ k * Polynomial.aeval t G) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [y, if_pos hi]
        ring
      _ = (∑ i ∈ U, algebraMap K F (β i)) * (t ^ k * Polynomial.aeval t G) := by
        rw [Finset.sum_mul]
      _ = 0 := by rw [hβU, zero_mul]
  have hkernel : separatedOrdinaryIdeal β G φ ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨k, rfl⟩
    change e.toRingHom
      (moment x (fun i ↦ MvPolynomial.C (β i) * Polynomial.aeval (x i) G) k) = 0
    rw [scalar_moment_map e.toRingHom]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      map_mul, ← Polynomial.aeval_algHom_apply, hex,
      e, MvPolynomial.aeval_C, moment, smul_eq_mul]
    exact hzero k
  let q : MvPolynomial (Fin n) K ⧸ separatedOrdinaryIdeal β G φ →ₐ[K] F :=
    Ideal.Quotient.liftₐ _ e (fun p hp ↦ hkernel hp)
  obtain ⟨i, hi⟩ := hU
  have hint : IsIntegral K
      (q (Ideal.Quotient.mk (separatedOrdinaryIdeal β G φ) (x i))) :=
    (IsIntegral.of_finite K (Ideal.Quotient.mk (separatedOrdinaryIdeal β G φ) (x i))).map q
  have hvalue : q (Ideal.Quotient.mk (separatedOrdinaryIdeal β G φ) (x i)) = t := by
    change e (x i) = t
    rw [hex]
    simp [y, hi]
  rw [hvalue] at hint
  exact ht (hint.tower_top (A := L)).isAlgebraic

end TranscendentalWitness

section ArbitraryBase

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Every nonempty subset sum must be a unit if the separated ordinary quotient is finite. -/
theorem subset_sums_units_of_separated_ordinary_finite
    (β : Fin n → K) (G : Polynomial K) (φ : Fin n → Polynomial K)
    (hG : G.Monic) (hGpos : 0 < G.natDegree)
    (hφ : ∀ i, (φ i).Monic) (hφpos : ∀ i, 0 < (φ i).natDegree)
    (hfinite : Module.Finite K
      (MvPolynomial (Fin n) K ⧸ separatedOrdinaryIdeal β G φ)) :
    ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i) := by
  classical
  intro U hU
  by_contra hunit
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {∑ i ∈ U, β i}) (Ideal.span_singleton_ne_top hunit)
  letI : M.IsMaximal := hM
  let L := K ⧸ M
  letI : Field L := Ideal.Quotient.field M
  let F := AlgebraicClosure (RatFunc L)
  let t : F := algebraMap (RatFunc L) F RatFunc.X
  have ht : Transcendental L t :=
    (transcendental_algebraMap_iff (R := L)
      (S := RatFunc L) (A := F) (algebraMap (RatFunc L) F).injective).mpr RatFunc.transcendental_X
  have hzeroL : algebraMap K L (∑ i ∈ U, β i) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hle (Ideal.subset_span rfl)
  have hzeroF : (∑ i ∈ U, algebraMap K F (β i)) = 0 := by
    rw [← map_sum]
    rw [IsScalarTower.algebraMap_apply K L F, hzeroL, map_zero]
  exact not_finite_separated_of_zero_subset_sum (L := L) β G φ hG hGpos hφ hφpos
    U hU hzeroF t ht hfinite

/-- The exact ordinary finiteness criterion for separated monic positive-degree covers.

Unlike the basis theorem, this criterion does not require `n!` to be a unit.
-/
theorem separated_ordinary_finite_iff
    (β : Fin n → K) (G : Polynomial K) (φ : Fin n → Polynomial K)
    (hG : G.Monic) (hGpos : 0 < G.natDegree)
    (hφ : ∀ i, (φ i).Monic) (hφpos : ∀ i, 0 < (φ i).natDegree) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ separatedOrdinaryIdeal β G φ) ↔
      ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i) := by
  constructor
  · exact subset_sums_units_of_separated_ordinary_finite β G φ hG hGpos hφ hφpos
  · intro hβ
    exact separated_ordinary_finite β G φ hβ fun i ↦
      hG.comp (hφ i) (hφpos i).ne'

end ArbitraryBase

end PaperVerification.Fermion
