module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

/-!
# Extending finite-order tests from a neighborhood of a closed set

The radial identity in the paper assumes only two continuous derivatives near
the positive semidefinite cone.  A smooth cutoff inside that neighborhood
extends the test to the whole matrix space without changing any of its local
values or derivatives on the cone.  No smoothness of the original function
outside its stated neighborhood is required.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace WishartVerification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite-order test near a closed set has a global extension agreeing on
a neighborhood of each point of the set.  Bounds on values and derivatives
on that set are therefore preserved exactly. -/
theorem exists_contDiff_extension_near_closed {n : ℕ∞} {S U : Set E}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    {g : E → ℝ} (hg : ContDiffOn ℝ n g U) :
    ∃ g' : E → ℝ, ContDiff ℝ n g' ∧ ∀ x ∈ S, g' =ᶠ[𝓝 x] g := by
  obtain ⟨V, hV, hSV, hVU⟩ := normal_exists_closure_subset hS hU hSU
  obtain ⟨W, hW, hSW, hWV⟩ := normal_exists_closure_subset hS hV hSV
  obtain ⟨χ, hχ, _hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := n) hV isClosed_closure hWV
  have hχsupportU : tsupport χ ⊆ U := by
    simpa only [tsupport, hχsupport] using hVU
  refine ⟨fun x => χ x * g x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds hx))
    · have hzero : χ =ᶠ[𝓝 x] (fun _ => 0) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχsupportU h))
      apply (show ContDiffAt ℝ n (fun _ : E => (0 : ℝ)) x from
        contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp only [hy, zero_mul]
  · intro x hx
    filter_upwards [hW.mem_nhds (hSW hx)] with y hy
    rw [(hχone y).mp (subset_closure hy), one_mul]

/-- The extension preserves the value, differential, and Hessian on the
closed set.  This is the exact finite-order interface used by Lemma 3.1. -/
theorem exists_c2_extension_near_closed {S U : Set E}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    {g : E → ℝ} (hg : ContDiffOn ℝ 2 g U) :
    ∃ g' : E → ℝ, ContDiff ℝ 2 g' ∧ ∀ x ∈ S,
      g' x = g x ∧ fderiv ℝ g' x = fderiv ℝ g x ∧
        fderiv ℝ (fderiv ℝ g') x = fderiv ℝ (fderiv ℝ g) x := by
  obtain ⟨g', hg', heq⟩ := exists_contDiff_extension_near_closed hS hU hSU hg
  refine ⟨g', hg', fun x hx => ?_⟩
  exact ⟨(heq x hx).eq_of_nhds, (heq x hx).fderiv_eq,
    (heq x hx).fderiv.fderiv_eq⟩

end WishartVerification

end
