module

public import PaperVerification.JacobianDegree
public import PaperVerification.GradedComponentBasis

/-!
# Homogeneous bases of the actual polynomial quotient components

The degree of a basis class is certified by a homogeneous polynomial lift.
Component dimensions are then exactly the numbers of basis vectors of that
degree. Finiteness of each indexing fibre is proved from positive weights.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Module

namespace PaperVerification.EulerResonance

variable {K ι I : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def quotientGrading (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d p, p ∈ U → weightedHomogeneousComponent w d p ∈ U) :
    TauCeti.InternalGrading K (P ⧸ U) ℕ := by
  let G : TauCeti.InternalGrading K P ℕ :=
    .ofDecomposition (weightedHomogeneousSubmodule K w)
  have hUG : DirectSum.SetLike.IsHomogeneous G.piece U := by
    rw [TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
    intro d p hp
    have he :
        (DirectSum.decompose (weightedHomogeneousSubmodule K w) p d : P) =
          weightedHomogeneousComponent w d p :=
      weightedDecomposition.decompose'_apply K w p d
    rw [he]
    exact hU d p hp
  exact G.quotient U hUG

theorem quotientGrading_piece (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d p, p ∈ U → weightedHomogeneousComponent w d p ∈ U) (d : ℕ) :
    (quotientGrading w U hU).piece d = quotientComponent w d U := by
  simp only [quotientGrading, TauCeti.InternalGrading.quotient_piece,
    TauCeti.InternalGrading.ofDecomposition_piece, LinearMap.restrictScalars_self]
  exact (quotientComponent_eq_map w d U).symm

def homogeneousComponentBasis (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d p, p ∈ U → weightedHomogeneousComponent w d p ∈ U)
    (B : Basis I K (P ⧸ U)) (degree : I → ℕ)
    (hB : ∀ i, B i ∈ quotientComponent w (degree i) U) (d : ℕ) :
    Basis {i // degree i = d} K (quotientComponent w d U) :=
  (GradedComponentBasis.componentBasis (quotientGrading w U hU) B degree
    (fun i => (quotientGrading_piece w U hU (degree i)).symm ▸ hB i) d).map
      (LinearEquiv.ofEq _ _ (quotientGrading_piece w U hU d))

theorem homogeneous_basis_fibre_finite (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d p, p ∈ U → weightedHomogeneousComponent w d p ∈ U)
    (hw : ∀ i, 0 < w i) (B : Basis I K (P ⧸ U)) (degree : I → ℕ)
    (hB : ∀ i, B i ∈ quotientComponent w (degree i) U) (d : ℕ) :
    Finite {i // degree i = d} := by
  letI := quotientComponent_finite w d U hw
  exact (homogeneousComponentBasis w U hU B degree hB d).finite_index_of_rank_lt_aleph0
    (Module.rank_lt_aleph0 K _)

theorem homogeneous_basis_component_finrank (w : ι → ℕ) (U : Submodule K P)
    (hU : ∀ d p, p ∈ U → weightedHomogeneousComponent w d p ∈ U)
    (B : Basis I K (P ⧸ U)) (degree : I → ℕ)
    (hB : ∀ i, B i ∈ quotientComponent w (degree i) U) (d : ℕ) :
    Module.finrank K (quotientComponent w d U) = Nat.card {i // degree i = d} :=
  Module.finrank_eq_nat_card_basis (homogeneousComponentBasis w U hU B degree hB d)

end PaperVerification.EulerResonance

namespace PaperVerification.JacobianDivergence

variable {K ι : Type*} [Field K] [Fintype ι]
local notation "P" => MvPolynomial ι K

theorem weightedEuler_mem_jacobian (F : P) (w : ι → ℕ) (h : ℕ)
    (hF : F.IsWeightedHomogeneous w h) (p : P) (hp : p ∈ jacobianSubmodule F) :
    weightedEuler w p ∈ jacobianSubmodule F := by
  rw [← coefficientMap_range] at hp
  obtain ⟨g, rfl⟩ := hp
  have he := coefficient_eulerShift F w h hF g
  change coefficientMap F (eulerShift w g) =
    weightedEuler w (coefficientMap F g) - h • coefficientMap F g at he
  rw [sub_eq_iff_eq_add.mp he.symm]
  apply (jacobianSubmodule F).add_mem
  · rw [← coefficientMap_range]
    exact ⟨eulerShift w g, rfl⟩
  · apply (jacobianSubmodule F).nsmul_mem
    rw [← coefficientMap_range]
    exact ⟨g, rfl⟩

theorem homogeneousComponent_mem_jacobian [CharZero K]
    (F : P) (w : ι → ℕ) (h : ℕ) (hF : F.IsWeightedHomogeneous w h)
    (d : ℕ) (p : P) (hp : p ∈ jacobianSubmodule F) :
    weightedHomogeneousComponent w d p ∈ jacobianSubmodule F :=
  homogeneousComponent_mem_of_eulerStable w _
    (weightedEuler_mem_jacobian F w h hF) p hp d

end PaperVerification.JacobianDivergence
