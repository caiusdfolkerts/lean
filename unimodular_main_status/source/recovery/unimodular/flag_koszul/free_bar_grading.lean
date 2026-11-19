module

public import Recovery.Unimodular.FlagKoszul.HomogeneousWords
public import Recovery.Unimodular.FlagKoszul.FreeIdentification

/-!
# Homogeneous exactness of the actual free bar resolution

The explicit contraction moves a positive coefficient into the first bar slot.
Consequently it preserves the original internal degree, including in bar degree
zero. Its augmentation term vanishes in every strictly positive internal degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.FlagKoszul.FreeBarGrading

open HomogeneousWords

variable {K A I : Type*} [CommRing K] [CommRing A] [Algebra K A]

def coefficientDegree (δ : I → ℕ) : Option I → ℕ
  | none => 0
  | some i => δ i

variable (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none = 1) (hε : ∀ i, ε (B (some i)) = 0) (δ : I → ℕ)

include hunit in
theorem homotopy_mem_piece {r N : ℕ} {z : List I →₀ A}
    (hz : z ∈ piece B δ (coefficientDegree δ) r N) :
    PaperVerification.NoncommutativeBar.homotopy B z ∈
      piece B δ (coefficientDegree δ) (r + 1) N := by
  apply linearMap_mem_piece_of_basis B B δ (coefficientDegree δ) (coefficientDegree δ)
    (PaperVerification.NoncommutativeBar.homotopy B) ?_ hz
  intro L j hL hj
  cases j with
  | none =>
    rw [hunit, PaperVerification.NoncommutativeBar.homotopy_single_one B hunit]
    exact Submodule.zero_mem _
  | some i =>
    change PaperVerification.NoncommutativeBar.homotopy B
      (Finsupp.single L (PaperVerification.AugmentedAlgebraBasis.positiveVector B i)) ∈ _
    rw [PaperVerification.NoncommutativeBar.homotopy_single_positive, ← hunit]
    apply single_basis_mem_piece B δ (coefficientDegree δ) (i :: L) none
    · simp only [List.length_cons, hL]
    · simpa only [coefficientDegree, zero_add, wordDegree_cons] using hj

include hunit hε in
theorem augmentationProjection_eq_zero {r N : ℕ} {z : List I →₀ A}
    (hN : 0 < N) (hz : z ∈ piece B δ (coefficientDegree δ) r N) :
    PaperVerification.NoncommutativeBar.augmentationProjection ε z = 0 := by
  have hc : B.repr (z []) none = 0 := by
    by_contra h
    have hd := (hz [] none h).2
    simp only [coefficientDegree, wordDegree_nil, add_zero] at hd
    omega
  have hεz : ε (z []) = 0 :=
    (PaperVerification.AugmentedAlgebraBasis.augmentation_eq_coordinate ε B hunit hε (z [])).trans hc
  simp only [PaperVerification.NoncommutativeBar.augmentationProjection,
    LinearMap.comp_apply, LinearMap.smulRight_apply, Finsupp.lapply_apply,
    AlgHom.toLinearMap_apply, hεz, zero_smul]

include hunit hε in
/-- A genuine homogeneous boundary in every positive internal degree,
including degree zero of the chain complex. -/
theorem homogeneous_cycle_is_boundary {r N : ℕ} {z : List I →₀ A}
    (hN : 0 < N) (hz : z ∈ piece B δ (coefficientDegree δ) r N)
    (hd : CoefficientModuleBar.differential B z = 0) :
    ∃ y ∈ piece B δ (coefficientDegree δ) (r + 1) N,
      CoefficientModuleBar.differential B y = z := by
  refine ⟨PaperVerification.NoncommutativeBar.homotopy B z,
    homotopy_mem_piece B hunit δ hz, ?_⟩
  rw [CoefficientModuleBar.differential_self] at hd ⊢
  have hc := PaperVerification.NoncommutativeBar.contracting_identity ε B hunit hε z
  simpa only [hd, map_zero, augmentationProjection_eq_zero ε B hunit hε δ hN hz,
    add_zero] using hc

#print axioms homotopy_mem_piece
#print axioms homogeneous_cycle_is_boundary

end Unimodular.FlagKoszul.FreeBarGrading
