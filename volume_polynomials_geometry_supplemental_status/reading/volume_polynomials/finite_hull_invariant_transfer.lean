module

public import VolumePolynomials.MixedVolumeMonotonicity

@[expose] public section
set_option autoImplicit false

/-! # Closed translation-invariant properties of tuples of convex bodies

Actual finite convex hulls are dense in the Hausdorff metric. A finite
simplex thickening makes their centered total sum full dimensional. These
two limit arguments remove the auxiliary centering and interior conditions
from any closed property invariant under independent translations.
-/

noncomputable section
open Set Filter Module
open scoped Pointwise Topology BigOperators

namespace VolumePolynomials

open PolytopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

theorem all_bodyTuples_of_centered_finiteHull
    (hN : 0 < N) (S : Set (Fin N → ConvexBody E)) (hclosed : IsClosed S)
    (htranslate : ∀ K ∈ S, ∀ v : Fin N → E,
      (fun i => translateBody (v i) (K i)) ∈ S)
    (hcenter : ∀ K : Fin N → ConvexBody E,
      (∀ i, IsFiniteHull (K i : Set E)) → (∀ i, (0 : E) ∈ K i) →
      (0 : E) ∈ interior (↑(∑ i, K i) : Set E) → K ∈ S)
    (K : Fin N → ConvexBody E) : K ∈ S := by
  first
  | have hfinite : {L : Fin N → ConvexBody E | ∀ i, IsFiniteHull (L i : Set E)} ⊆ S := by
      intro L hL
      choose p hp using fun i => (L i).nonempty
      let Q : Fin N → ConvexBody E := fun i => translateBody (-p i) (L i)
      have hQ0 : ∀ i, (0 : E) ∈ Q i := fun i => zero_mem_translateBody_neg (hp i)
      have hQfinite : ∀ i, IsFiniteHull (Q i : Set E) :=
        fun i => isFiniteHull_translateBody (hL i) (-p i)
      obtain ⟨P, hPfinite, hPint⟩ := exists_finiteHull_with_zero_interior (E := E)
      have hP0 : (0 : E) ∈ P := interior_subset hPint
      let R : ℝ → Fin N → ConvexBody E := fun r i => Q i + r • P
      have hR0 (r : ℝ) (i : Fin N) : (0 : E) ∈ R r i :=
        ⟨0, hQ0 i, 0, ⟨0, hP0, by simp⟩, zero_add 0⟩
      have hRfinite (r : ℝ) (i : Fin N) : IsFiniteHull (R r i : Set E) :=
        (hQfinite i).add (hPfinite.smul r)
      have hRint {r : ℝ} (hr : 0 < r) :
          (0 : E) ∈ interior (↑(∑ i, R r i) : Set E) := by
        have hpint : (0 : E) ∈ interior (r • (P : Set E)) := by
          rw [interior_smul₀ hr.ne']
          exact ⟨0, hPint, by simp⟩
        have hsub : r • (P : Set E) ⊆ (↑(∑ i, R r i) : Set E) := by
          intro x hx
          apply body_le_sum_of_zero_mem (R r) (hR0 r) (⟨0, hN⟩ : Fin N)
          exact ⟨0, hQ0 _, x, hx, zero_add x⟩
        exact interior_mono hsub hpint
      have hcont : Continuous R := by
        dsimp [R]
        fun_prop
      have ht : Tendsto R (𝓝[>] 0) (𝓝 Q) := by
        simpa only [R, body_zero_smul, add_zero] using
          (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      have hRmem : ∀ᶠ r : ℝ in 𝓝[>] 0, R r ∈ S := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact hcenter (R r) (hRfinite r) (hR0 r) (hRint hr)
      have hQ : Q ∈ S := hclosed.mem_of_tendsto ht hRmem
      have hback := htranslate Q hQ p
      simpa only [Q, translateBody_translate, add_neg_cancel, translateBody_zero] using hback
    exact closure_minimal hfinite hclosed (dense_finiteHullBodyTuples (E := E) N K)

end VolumePolynomials
