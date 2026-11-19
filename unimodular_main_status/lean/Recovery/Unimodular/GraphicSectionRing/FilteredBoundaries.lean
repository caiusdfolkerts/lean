module

public import Recovery.Unimodular.GraphicSectionRing.BarComparison

/-!
# Finite filtered descent retaining the actual homogeneous chain spaces

The leading complex supplies genuine boundary witnesses in the specified
submodules. Finite descent in the independent height filtration then gives
boundary witnesses for the original differential in those same submodules.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.GraphicSectionRing.FilteredBoundaries

open PaperVerification.Fermion.BasisFiltered
open PaperVerification.FilteredComplex

variable {K M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  (b : Module.Basis I K M) (w : I → ℕ)
  (f g : M →ₗ[K] M) (V W : Submodule K M)

/-- The finite-height proof retains the actual specified source and target
submodules; in the application these are the ordinary internal-degree pieces. -/
theorem cycle_is_boundary
    (hzero : ∀ y, f (f y) = 0)
    (hlead : HasLeadingMap b w b w f g)
    (hg : PreservesComponents b w b w g)
    (hV : ∀ m x, x ∈ V → component b w m x ∈ V)
    (hW : ∀ m x, x ∈ W → component b w m x ∈ W)
    (hfW : ∀ y, y ∈ W → f y ∈ V)
    (hmodel : ∀ x, x ∈ V → g x = 0 → ∃ y, y ∈ W ∧ g y = x)
    (x : M) (hxV : x ∈ V) (hx : f x = 0) : ∃ y, y ∈ W ∧ f y = x := by
  have lift (m : ℕ) (z : M) (hzV : z ∈ V)
      (hcz : g (component b w m z) = 0) :
      ∃ y, y ∈ W ∧ Bound b w m y ∧ Bound b w m (f y) ∧
        component b w m (f y) = component b w m z := by
    obtain ⟨u, huW, hgu⟩ := hmodel _ (hV m z hzV) hcz
    let y := component b w m u
    have hyW : y ∈ W := hW m u huW
    have hy : Bound b w m y := bound_component b w m u
    have hyy : component b w m y = y := by
      rw [component_of_homogeneous b w (homogeneous_component b w m u), if_pos rfl]
    have hzz : component b w m (component b w m z) = component b w m z := by
      rw [component_of_homogeneous b w (homogeneous_component b w m z), if_pos rfl]
    refine ⟨y, hyW, hy, (hlead m y hy).1, ?_⟩
    rw [(hlead m y hy).2, hyy]
    change g (component b w m u) = component b w m z
    rw [hg m u, hgu, hzz]
  have bounded : ∀ m z, Bound b w m z → z ∈ V → f z = 0 →
      ∃ y, y ∈ W ∧ Bound b w m y ∧ f y = z := by
    intro m
    induction m with
    | zero =>
      intro z hz hzV hcycle
      have hc : g (component b w 0 z) = 0 := by
        rw [← (hlead 0 z hz).2, hcycle, map_zero]
      obtain ⟨y, hyW, hy, hfy, he⟩ := lift 0 z hzV hc
      have hres : z - f y = 0 := eq_zero_of_bound_zero_component_zero b w
        (bound_sub b w hz hfy) (by rw [map_sub, he, sub_self])
      exact ⟨y, hyW, hy, (sub_eq_zero.mp hres).symm⟩
    | succ m ih =>
      intro z hz hzV hcycle
      have hc : g (component b w (m + 1) z) = 0 := by
        rw [← (hlead (m + 1) z hz).2, hcycle, map_zero]
      obtain ⟨y, hyW, hy, hfy, he⟩ := lift (m + 1) z hzV hc
      have hr : Bound b w m (z - f y) := bound_pred_of_component_zero b w
        (bound_sub b w hz hfy) (by rw [map_sub, he, sub_self])
      have hrV : z - f y ∈ V := V.sub_mem hzV (hfW y hyW)
      have hrcycle : f (z - f y) = 0 := by rw [map_sub, hcycle, hzero, sub_self]
      obtain ⟨t, htW, ht, hft⟩ := ih (z - f y) hr hrV hrcycle
      refine ⟨t + y, W.add_mem htW hyW,
        bound_add b w (bound_mono b w (Nat.le_succ m) ht) hy, ?_⟩
      rw [map_add, hft, sub_add_cancel]
  obtain ⟨m, hm⟩ := exists_bound b w x
  obtain ⟨y, hyW, _, hfy⟩ := bounded m x hm hxV hx
  exact ⟨y, hyW, hfy⟩

#print axioms cycle_is_boundary

end Unimodular.GraphicSectionRing.FilteredBoundaries
