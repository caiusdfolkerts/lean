module
public import shared_results.part023
public import graph_foundation.part013

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.HomogeneousSelectedGeneration -/
section

/-! # Reading selected-color generation homogeneously

The selected submodule is the span of all basis vectors in the chosen
colors. Since the differential preserves color, each selected cycle is
the finite sum of cycles of individual selected colors. Consequently the
usual homogeneous interpretation of generation agrees with the selected
submodule formulation used in the transfer theorem.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.MixedTransfer
open Classical CommAlg
open IntegerFiltered.MultiplicativeFiltration

/-- Passing from a sum of selected homogeneous components to the union of
their individual cycle classes does not change the generated algebra. -/
theorem selectedHomology_adjoin_eq_homogeneous
    {R A I Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : ParityDifferential R A) (b : Module.Basis I R A)
    (degree : I → Γ) (U : Set Γ)
    (hD : ∀ i, D.d (b i) ∈ Grading.Piece b degree (degree i)) :
    Algebra.adjoin R (selectedHomologyClasses D
      (Submodule.span R (b '' {i | degree i ∈ U}))) =
    Algebra.adjoin R {z | ∃ g ∈ U,
      z ∈ selectedHomologyClasses D (Grading.Piece b degree g)} := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro z ⟨x, hx, rfl⟩
    have hxSupport := b.mem_span_image.mp hx
    have hxCycle : D.d x.val = 0 := x.property
    let T := (b.repr x.val).support.image degree
    have hcycle (g : Γ) : D.d (Grading.projection b degree g x.val) = 0 := by
      have he := LinearMap.congr_fun
        (shiftedProjection_commutes b b degree degree id Function.injective_id
          D.d hD g) x.val
      change D.d (Grading.projection b degree g x.val) =
        Grading.projection b degree g (D.d x.val) at he
      simpa only [hxCycle, map_zero] using he
    let y (g : Γ) : D.cycles :=
      ⟨Grading.projection b degree g x.val, hcycle g⟩
    have hsum : (∑ g ∈ T, y g) = x := by
      apply Subtype.ext
      change D.cycles.val (∑ g ∈ T, y g) = x.val
      rw [map_sum]
      exact Grading.sum_projections b degree x.val
    rw [← hsum, map_sum]
    apply Subalgebra.sum_mem
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    apply Algebra.subset_adjoin
    exact ⟨degree i, hxSupport hi, y (degree i),
      Grading.projection_mem b degree (degree i) x.val, rfl⟩
  · apply Algebra.adjoin_le
    rintro z ⟨g, hg, x, hx, rfl⟩
    have hle : Grading.Piece b degree g ≤
        Submodule.span R (b '' {i | degree i ∈ U}) := by
      apply Submodule.span_mono
      rintro _ ⟨i, hi, rfl⟩
      change degree i = g at hi
      exact ⟨i, by simpa only [Set.mem_setOf_eq, hi] using hg, rfl⟩
    exact Algebra.subset_adjoin ⟨x, hle hx, rfl⟩

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K]
  [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : C → Ideal (MvPolynomial V K))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (powerProduct J s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

/-- The selected-color formulation used by Theorem 5.5 is exactly
homogeneous generation in those individual actual coefficient components. -/
theorem mixedSelectedHomology_adjoin_eq_homogeneous (U : Set (C →₀ ℕ)) :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA J)
      (Auxiliary.selectedPiece m J G hG hu U)) =
    Algebra.adjoin K {z | ∃ s ∈ U,
      z ∈ selectedHomologyClasses (idealReesKoszulDGA J)
        (Auxiliary.auxiliaryPiece m J G hG hu s)} := by
  apply selectedHomology_adjoin_eq_homogeneous (idealReesKoszulDGA J)
    (groebnerReesKoszulBasis m J G hG hu) (fun a => a.1.1) U
  intro a
  rw [Grading.mem_piece]
  intro b hb
  exact (groebnerReesKoszul_d_auxiliary_exterior m J G hG hu a b hb).1

end FourPapers.MixedTransfer

end
end
end

end
