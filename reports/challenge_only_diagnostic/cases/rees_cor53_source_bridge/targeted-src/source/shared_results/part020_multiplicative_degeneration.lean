module
public import graph_foundation.part014
public import shared_results.part020_integer_filtered_generation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.MultiplicativeDegeneration -/
section

/-! # Multiplicative propagation for a genuine filtered differential algebra

The selected submodule is the auxiliary-degree-one complex in the application.
The finite-component hypothesis below concerns literal homology quotients of
the differential and its associated graded maps. No lifting or degeneration
conclusion is assumed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical DirectSum
open scoped BigOperators

variable {K A Γ : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)

/-- Equality of finite-component homology dimensions, written in any finite
interval containing its filtration. Bounds are existential data, and are known
to exist from exhaustiveness and separatedness. -/
def ComponentDimensionsAgree (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ x ∈ W, D.d x ∈ W) : Prop :=
  ∃ (L : ℤ) (hL : (F.level (L - 1)).comap W.subtype = ⊥) (N : ℕ),
    (F.componentFiltration W L hL).level N = ⊤ ∧
    Module.finrank K (FilteredHomology.Homology
      (componentDifferential D W hW) (componentDifferential D W hW)
      (componentDifferential_square D W hW)) =
      ∑ n ∈ Finset.range N,
        Module.finrank K (FilteredHomology.GradedHomology
          (F.componentFiltration W L hL) (F.componentFiltration W L hL)
          (F.componentFiltration W L hL)
          (componentDifferential D W hW) (componentDifferential D W hW)
          (F.componentDifferential_preserves D hd W hW L hL)
          (F.componentDifferential_preserves D hd W hW L hL)
          (componentDifferential_square D W hW) n)

theorem componentDimensionsAgree_iff_relativeLiftsCycles
    (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ x ∈ W, D.d x ∈ W) :
    F.ComponentDimensionsAgree D hd W hW ↔ F.RelativeLiftsCycles D W := by
  constructor
  · rintro ⟨L, hL, N, hN, hdim⟩
    exact F.relativeLiftsCycles_of_homology_dimension_eq D hd W hW L hL N hN hdim
  · intro hlift
    obtain ⟨L, hL, N, hN⟩ := F.exists_component_bounds W
    exact ⟨L, hL, N, hN,
      F.component_homology_dimension_eq_of_relative D hd W hW L hL N hN hlift⟩

variable [AddMonoid Γ] [DecidableEq Γ]
  (P : Γ → Submodule K A) [GradedAlgebra P]
  [∀ i, FiniteDimensional K (P i)]
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

/-- Multiplicative degeneration: equality on the selected components lifts
all leading cycles, preserves the homology dimensions on every finite graded
component, and propagates algebra generation to the original homology. -/
theorem propagation_from_selected_components
    (hF : ∀ n, SetLike.IsHomogeneous P (F.level n))
    (hD : ∀ i x, x ∈ P i → D.d x ∈ P i)
    (W : Submodule K A) (hWh : SetLike.IsHomogeneous P W)
    (hWd : ∀ x ∈ W, D.d x ∈ W)
    (hfirst : ∀ i, F.ComponentDimensionsAgree D hd (P i ⊓ W)
      (fun x hx => ⟨hD i x hx.1, hWd x hx.2⟩))
    (hgen : Algebra.adjoin K (F.specialClasses D hd hp W) = ⊤) :
    F.LiftsCycles D ∧
      (∀ i, F.ComponentDimensionsAgree D hd (P i) (hD i)) ∧
      Algebra.adjoin K (selectedHomologyClasses D W) = ⊤ := by
  have hrelative : F.RelativeLiftsCycles D W :=
    F.relativeLiftsCycles_of_components D P W hF hWh hD (fun i =>
      (F.componentDimensionsAgree_iff_relativeLiftsCycles D hd (P i ⊓ W)
        (fun x hx => ⟨hD i x hx.1, hWd x hx.2⟩)).mp (hfirst i))
  have hlift : F.LiftsCycles D :=
    F.liftsCycles_of_relative_generators D hd hp W hgen hrelative
  refine ⟨hlift, ?_, ?_⟩
  · intro i
    apply (F.componentDimensionsAgree_iff_relativeLiftsCycles D hd (P i) (hD i)).mpr
    exact F.relativeLiftsCycles_of_homogeneous_projection D P hF hD hlift i
  · exact F.homology_generated_of_relative_generators D P hd hp hF hD W hWh
      hrelative hgen

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
