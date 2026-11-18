module
public import Mathlib
/-! General geometric proof interfaces for Normal Corollary7.
These preserve actual convex hulls and supporting hyperplanes. Source-prepared
only; no local Lean validation has run. -/
@[expose] public section
noncomputable section
namespace PalomarNormalCorollary7Exposure
open Set
variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]
/-- Intersecting a convex hull with a supporting hyperplane retains exactly
its generating points on that hyperplane. No finite-model replacement occurs. -/
theorem hull_support_level (v : ι → E) (ℓ : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hv : ∀ i, ℓ (v i) ≤ c) :
    {x ∈ convexHull ℝ (Set.range v) | ℓ x = c} =
      convexHull ℝ (v '' {i | ℓ (v i) = c}) := by
  let T : Set E := v '' {i | ℓ (v i) = c}
  have hconv : Convex ℝ {x : E | ℓ x ≤ c ∧
      (ℓ x = c → x ∈ convexHull ℝ T)} := by
    intro x hx y hy a b ha hb hab
    have hle : ℓ (a • x + b • y) ≤ c := by
      simp only [map_add, map_smul, smul_eq_mul]
      calc
        a * ℓ x + b * ℓ y ≤ a * c + b * c :=
          add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
            (mul_le_mul_of_nonneg_left hy.1 hb)
        _ = c := by rw [← add_mul,hab,one_mul]
    refine ⟨hle,fun he => ?_⟩
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      have hey : ℓ y = c := by simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using he
      simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using hy.2 hey
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      have hex : ℓ x = c := by simpa only [hb0,ha1,zero_smul,one_smul,add_zero] using he
      simpa only [hb0,ha1,zero_smul,one_smul,add_zero] using hx.2 hex
    have he' : a * ℓ x + b * ℓ y = c := by
      simpa only [map_add,map_smul,smul_eq_mul] using he
    have hpa := mul_nonneg ha (sub_nonneg.mpr hx.1)
    have hpb := mul_nonneg hb (sub_nonneg.mpr hy.1)
    have hsum : a * (c - ℓ x) + b * (c - ℓ y) = 0 := by
      calc
        _ = (a+b) * c - (a * ℓ x + b * ℓ y) := by ring
        _ = 0 := by rw [hab,he',one_mul,sub_self]
    have hzeroa : a * (c - ℓ x) = 0 := by linarith only [hpa,hpb,hsum]
    have hzerob : b * (c - ℓ y) = 0 := by linarith only [hpa,hpb,hsum]
    have hex : ℓ x = c := by
      have hh := (mul_eq_zero.mp hzeroa).resolve_left ha0
      linarith
    have hey : ℓ y = c := by
      have hh := (mul_eq_zero.mp hzerob).resolve_left hb0
      linarith
    exact (convex_convexHull ℝ T) (hx.2 hex) (hy.2 hey) ha hb hab
  have hgood : convexHull ℝ (Set.range v) ⊆
      {x : E | ℓ x ≤ c ∧ (ℓ x = c → x ∈ convexHull ℝ T)} := by
    apply convexHull_min _ hconv
    rintro x ⟨i,rfl⟩
    exact ⟨hv i,fun hi => subset_convexHull ℝ T ⟨i,hi,rfl⟩⟩
  have hsub : convexHull ℝ T ⊆ convexHull ℝ (Set.range v) :=
    convexHull_mono (by rintro x ⟨i,hi,rfl⟩; exact ⟨i,rfl⟩)
  have heq : convexHull ℝ T ⊆ {x : E | ℓ x = c} := by
    apply convexHull_min _ (convex_hyperplane ℓ.isLinear c)
    rintro x ⟨i,hi,rfl⟩
    exact hi
  apply Set.Subset.antisymm
  · rintro x ⟨hx,hxl⟩
    exact (hgood hx).2 hxl
  · intro x hx
    exact ⟨hsub hx,heq hx⟩

/-- A strictly exposed generating point is an extreme point of the entire
actual convex hull, even if the generating family has redundant labels. -/
theorem strict_generator_extreme (v : ι → E) (ℓ : E →ₗ[ℝ] ℝ) (i : ι)
    (hs : ∀ j, j ≠ i → ℓ (v j) < ℓ (v i)) :
    v i ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ := by
  have hv : ∀ j, ℓ (v j) ≤ ℓ (v i) := by
    intro j
    by_cases hji : j = i
    · subst j; exact le_rfl
    · exact (hs j hji).le
  have himage : v '' {j | ℓ (v j) = ℓ (v i)} = {v i} := by
    apply Set.Subset.antisymm
    · rintro x ⟨j,hj,rfl⟩
      by_cases hji : j = i
      · subst j; exact Set.mem_singleton _
      · exact (ne_of_lt (hs j hji) hj).elim
    · rintro x (rfl : x = v i)
      exact ⟨i,rfl,rfl⟩
  have hlevel : {x ∈ convexHull ℝ (Set.range v) | ℓ x = ℓ (v i)} = {v i} := by
    rw [hull_support_level v ℓ (ℓ (v i)) hv,himage,convexHull_singleton]
  have hvalid : convexHull ℝ (Set.range v) ⊆ {x : E | ℓ x ≤ ℓ (v i)} := by
    apply convexHull_min _ (convex_halfSpace_le ℓ.isLinear (ℓ (v i)))
    rintro x ⟨j,rfl⟩
    exact hv j
  refine ⟨subset_convexHull ℝ _ ⟨i,rfl⟩,?_⟩
  intro x hx y hy hseg
  rw [openSegment_eq_image] at hseg
  obtain ⟨t,ht,he⟩ := hseg
  have hxe := hvalid hx
  have hye := hvalid hy
  have he' : (1-t) * ℓ x + t * ℓ y = ℓ (v i) := by
    simpa only [map_add,map_smul,smul_eq_mul] using congrArg ℓ he
  have h0 : (1-t) * (ℓ (v i) - ℓ x) = 0 := by
    nlinarith [mul_nonneg (le_of_lt ht.1) (sub_nonneg.mpr hye),
      mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hxe)]
  have hxl : ℓ x = ℓ (v i) := by
    have hh := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (ne_of_gt ht.2))
    linarith
  have hmem : x ∈ {z ∈ convexHull ℝ (Set.range v) | ℓ z = ℓ (v i)} := ⟨hx,hxl⟩
  rw [hlevel] at hmem
  exact hmem
end PalomarNormalCorollary7Exposure
