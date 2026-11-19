module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Papers.HomogeneousSpanDimension

open Set Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def liftPoint (x : E) : E × ℝ := (x, 1)

def liftSpan (S : Set E) : Submodule ℝ (E × ℝ) :=
  Submodule.span ℝ (liftPoint '' S)

theorem liftPoint_mem {S : Set E} {p : E} (hp : p ∈ S) :
    liftPoint p ∈ liftSpan S :=
  Submodule.subset_span ⟨p, hp, rfl⟩

theorem liftSpan_eq_direction_sup_point {S : Set E} {p : E} (hp : p ∈ S) :
    liftSpan S = (vectorSpan ℝ S).map (LinearMap.inl ℝ E ℝ) ⊔
      Submodule.span ℝ {liftPoint p} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, rfl⟩
    refine Submodule.mem_sup.mpr
      ⟨(LinearMap.inl ℝ E ℝ) (x - p), ?_, liftPoint p, ?_, ?_⟩
    · exact Submodule.mem_map.mpr
        ⟨x - p, vsub_mem_vectorSpan ℝ hx hp, rfl⟩
    · exact Submodule.subset_span (Set.mem_singleton _)
    · ext <;> simp [liftPoint]
  · apply sup_le
    · rw [Submodule.map_le_iff_le_comap,
        vectorSpan_eq_span_vsub_set_right ℝ hp]
      apply Submodule.span_le.mpr
      rintro z ⟨x, hx, rfl⟩
      change (LinearMap.inl ℝ E ℝ) (x -ᵥ p) ∈ liftSpan S
      have h := (liftSpan S).sub_mem (liftPoint_mem hx) (liftPoint_mem hp)
      simpa [liftPoint, vsub_eq_sub] using h
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact liftPoint_mem hp

theorem liftPoint_not_mem_direction {S : Set E} (p : E) :
    liftPoint p ∉ (vectorSpan ℝ S).map (LinearMap.inl ℝ E ℝ) := by
  intro h
  obtain ⟨x, hx, heq⟩ := Submodule.mem_map.mp h
  have hzero : (0 : ℝ) = 1 := by
    simpa [liftPoint] using congrArg Prod.snd heq
  exact zero_ne_one hzero

theorem finrank_map_inl (U : Submodule ℝ E) :
    finrank ℝ (U.map (LinearMap.inl ℝ E ℝ)) = finrank ℝ U := by
  have hinj : Function.Injective
      ((LinearMap.inl ℝ E ℝ).comp U.subtype) :=
    (LinearMap.inl_injective (R := ℝ) (M := E) (M₂ := ℝ)).comp
      Subtype.val_injective
  have he : ((LinearMap.inl ℝ E ℝ).comp U.subtype).range =
      U.map (LinearMap.inl ℝ E ℝ) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj hinj

variable [FiniteDimensional ℝ E]

theorem finrank_liftSpan {S : Set E} (hS : S.Nonempty) :
    finrank ℝ (liftSpan S) = finrank ℝ (vectorSpan ℝ S) + 1 := by
  obtain ⟨p, hp⟩ := hS
  rw [liftSpan_eq_direction_sup_point hp,
    Submodule.finrank_sup_span_singleton (liftPoint_not_mem_direction p),
    finrank_map_inl]

/-- A genuine affine two-face spans a three-dimensional homogeneous
linear subspace.  Nonemptiness is explicit; no face data are encoded in
the definition of the homogeneous span. -/
theorem finrank_liftSpan_eq_three {S : Set E} (hS : S.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ S) = 2) :
    finrank ℝ (liftSpan S) = 3 := by
  rw [finrank_liftSpan hS, hdim]

end Papers.HomogeneousSpanDimension
