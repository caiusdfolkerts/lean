module

public import PaperVerification.JacobianMilnorReduction

/-!
# Identifying the literal Hamiltonian relation space

For a regular gradient, the divergence of the tangent module equals the vector
span of the images `(F_j ∂_i - F_i ∂_j)(P)` in the paper. The last statement uses
only `i < j`, so the presentation agrees with the displayed quotient in Theorem
6.3, including its relation space as a vector space rather than an ideal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local instance hamiltonianDecidableEq : DecidableEq ι := Classical.decEq ι

def hamiltonian (F : P) (i j : ι) : P →ₗ[K] P :=
  (LinearMap.mulLeft K (pderiv j F)).comp (pderiv i).toLinearMap -
    (LinearMap.mulLeft K (pderiv i F)).comp (pderiv j).toLinearMap

@[simp] theorem hamiltonian_apply (F p : P) (i j : ι) :
    hamiltonian F i j p = pderiv j F * pderiv i p - pderiv i F * pderiv j p := rfl

@[simp] theorem hamiltonian_self (F p : P) (i : ι) : hamiltonian F i i p = 0 := sub_self _

theorem hamiltonian_swap (F p : P) (i j : ι) :
    hamiltonian F j i p = -hamiltonian F i j p := by
  simp only [hamiltonian_apply, neg_sub]

def hamiltonianSpace (F : P) : Submodule K P :=
  Submodule.span K {p | ∃ i j : ι, ∃ q, p = hamiltonian F i j q}

private def hamiltonianField (F p : P) (i j : ι) : ι → P :=
  Pi.single i (pderiv j F * p) - Pi.single j (pderiv i F * p)

private theorem hamiltonianField_mem_tangent (F p : P) (i j : ι) :
    hamiltonianField F p i j ∈ tangent F := by
  change KoszulSyzygies.coefficient (gradient F)
    (Pi.single i (pderiv j F * p) - Pi.single j (pderiv i F * p)) = 0
  rw [map_sub, coefficient_single, coefficient_single]
  simp only [gradient]
  ring

private theorem divergence_hamiltonianField (F p : P) (i j : ι) :
    divergence (hamiltonianField F p i j) = hamiltonian F i j p := by
  rw [hamiltonianField]
  rw [map_sub, divergence_single, divergence_single, pderiv_mul, pderiv_mul]
  rw [pderiv_comm i j F]
  simp only [hamiltonian_apply]
  ring

theorem hamiltonian_mem_divergenceSpace (F p : P) (i j : ι) :
    hamiltonian F i j p ∈ divergenceSpace F := by
  exact ⟨hamiltonianField F p i j, hamiltonianField_mem_tangent F p i j,
    divergence_hamiltonianField F p i j⟩

theorem hamiltonianSpace_le_divergenceSpace (F : P) :
    hamiltonianSpace F ≤ divergenceSpace F := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, j, q, rfl⟩
  exact hamiltonian_mem_divergenceSpace F q i j

/-- Every divergence of a coordinate Koszul boundary is a literal sum of
Hamiltonian operator values. -/
theorem divergence_boundary_eq_sum_hamiltonian (F : P) (A : ι → ι → P) :
    divergence (KoszulSyzygies.boundary (gradient F) A) =
      ∑ i, ∑ j, hamiltonian F i j (A j i) := by
  rw [divergence_boundary]
  change (∑ j, (∑ i, pderiv i (A j i - A i j)) * pderiv j F) = _
  have hentry (i j : ι) :
      pderiv i (A j i - A i j) * pderiv j F =
        pderiv i (A j i) * pderiv j F - pderiv i (A i j) * pderiv j F := by
    rw [map_sub, sub_mul]
  simp_rw [Finset.sum_mul, hentry, hamiltonian_apply]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

theorem divergenceSpace_eq_hamiltonianSpace {n : ℕ}
    (F : MvPolynomial (Fin n) K)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F))) : divergenceSpace F = hamiltonianSpace F := by
  apply le_antisymm
  · rintro p ⟨g, hg, rfl⟩
    have hker : g ∈ LinearMap.ker (KoszulSyzygies.coefficient (gradient F)) := hg
    rw [KoszulSyzygies.kernel_eq_boundary_range (gradient F) hreg] at hker
    obtain ⟨A, rfl⟩ := hker
    rw [divergence_boundary_eq_sum_hamiltonian]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    exact Submodule.subset_span ⟨i, j, A j i, rfl⟩
  · exact hamiltonianSpace_le_divergenceSpace F

/-- The exact `i < j` presentation printed in the paper. -/
def orderedHamiltonianSpace {n : ℕ} (F : MvPolynomial (Fin n) K) :
    Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K {p | ∃ i j : Fin n, i < j ∧ ∃ q, p = hamiltonian F i j q}

theorem hamiltonianSpace_eq_ordered {n : ℕ} (F : MvPolynomial (Fin n) K) :
    hamiltonianSpace F = orderedHamiltonianSpace F := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨i, j, q, rfl⟩
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact Submodule.subset_span ⟨i, j, hij, q, rfl⟩
    · change hamiltonian F i i q ∈ orderedHamiltonianSpace F
      rw [hamiltonian_self]
      exact (orderedHamiltonianSpace F).zero_mem
    · rw [hamiltonian_swap F q j i]
      exact (orderedHamiltonianSpace F).neg_mem (Submodule.subset_span ⟨j, i, hji, q, rfl⟩)
  · apply Submodule.span_mono
    rintro p ⟨i, j, _, q, rfl⟩
    exact ⟨i, j, q, rfl⟩

theorem divergenceSpace_eq_paper_relations {n : ℕ} (F : MvPolynomial (Fin n) K)
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin n) K)
      (List.ofFn (gradient F))) : divergenceSpace F = orderedHamiltonianSpace F :=
  (divergenceSpace_eq_hamiltonianSpace F hreg).trans (hamiltonianSpace_eq_ordered F)

end PaperVerification.JacobianDivergence
