module
public import normal_projective.geometry
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.NormNum
/-! # Actual exposed faces of a finite halfspace intersection -/
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace NormalProjective
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

def tightFace (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) (I : Set ι) : Set E :=
  {x ∈ halfspaceRegion f h | ∀ i ∈ I, f i x = h i}

theorem tightFace_isExposed (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) (I : Set ι) :
    IsExposed ℝ (halfspaceRegion f h) (tightFace f h I) := by
  classical
  intro hn
  obtain ⟨x, hxP, hxI⟩ := hn
  let s : Finset ι := Finset.univ.filter (fun i => i ∈ I)
  let l : E →L[ℝ] ℝ := ∑ i ∈ s, (f i).toContinuousLinearMap
  refine ⟨l, Set.ext (fun y => ?_)⟩
  constructor
  · rintro ⟨hyP, hyI⟩
    refine ⟨hyP, fun z hz => ?_⟩
    simp only [l, ContinuousLinearMap.sum_apply, LinearMap.coe_toContinuousLinearMap']
    exact Finset.sum_le_sum fun i hi => by
      rw [hyI i (Finset.mem_filter.mp hi).2]
      exact hz i
  · rintro ⟨hyP, hmax⟩
    refine ⟨hyP, fun i hi => ?_⟩
    have hsumi : (∑ j ∈ s, f j y) = ∑ j ∈ s, h j := by
      apply le_antisymm
      · exact Finset.sum_le_sum fun j _ => hyP j
      · have hxsum : (∑ j ∈ s, f j x) = ∑ j ∈ s, h j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hxI j (Finset.mem_filter.mp hj).2
        have hm := hmax x hxP
        simp only [l, ContinuousLinearMap.sum_apply, LinearMap.coe_toContinuousLinearMap'] at hm
        rwa [hxsum] at hm
    have heach := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ s) => hyP j)).mp hsumi
    exact heach i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

def activeFinset (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) (x : E) : Finset ι :=
  by
    classical
    exact Finset.univ.filter (fun i => f i x = h i)

@[simp] theorem mem_activeFinset (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (x : E) (i : ι) :
    i ∈ activeFinset f h x ↔ f i x = h i := by
  classical
  simp [activeFinset]

/-- Every nonempty convex subset has a point tight precisely on its universally tight facets. -/
theorem exists_common_tight_point
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) {F : Set E}
    (hn : F.Nonempty) (hc : Convex ℝ F) (hFP : F ⊆ halfspaceRegion f h) :
    ∃ x ∈ F, ∀ i, f i x = h i ↔ ∀ y ∈ F, f i y = h i := by
  classical
  letI : Nonempty F := hn.to_subtype
  let a : F := Function.argmin (fun x : F => (activeFinset f h x.val).card)
  have hmin (y : F) :
      (activeFinset f h a.val).card ≤ (activeFinset f h y.val).card :=
    le_of_not_gt (Function.not_lt_argmin
      (fun x : F => (activeFinset f h x.val).card) y)
  refine ⟨a.val, a.property, fun i => ⟨?_, fun hi => hi _ a.property⟩⟩
  intro hai y hy
  let z : E := (1 / 2 : ℝ) • a.val + (1 / 2 : ℝ) • y
  have hzF : z ∈ F := hc a.property hy (by norm_num) (by norm_num) (by norm_num)
  have hsub : activeFinset f h z ⊆ activeFinset f h a.val := by
    intro j hj
    rw [mem_activeFinset] at hj ⊢
    have haP := hFP a.property j
    have hyP := hFP hy j
    dsimp [z] at hj
    simp only [map_add, map_smul, smul_eq_mul] at hj
    linarith
  have heq : activeFinset f h z = activeFinset f h a.val :=
    Finset.eq_of_subset_of_card_le hsub (hmin ⟨z, hzF⟩)
  have hz : f i z = h i := by
    rw [← mem_activeFinset, heq, mem_activeFinset]
    exact hai
  dsimp [z] at hz
  simp only [map_add, map_smul, smul_eq_mul] at hz
  linarith

/-- Exposed faces are exactly intersections of tight displayed inequalities. -/
theorem exposedFace_eq_tightFace
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) {F : Set E}
    (hF : IsExposed ℝ (halfspaceRegion f h) F) (hn : F.Nonempty) :
    F = tightFace f h {i | ∀ y ∈ F, f i y = h i} := by
  obtain ⟨x, hxF, hx⟩ := exists_common_tight_point f h hn
    (hF.convex (convex_halfspaceRegion f h)) hF.subset
  obtain ⟨l, hl⟩ := hF hn
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨hF.subset hy, fun i hi => hi y hy⟩
  · rintro y ⟨hyP, hyI⟩
    have hxP := hF.subset hxF
    have hv : ∀ i, f i x = h i → f i (y - x) = 0 := by
      intro i hi
      rw [map_sub, hi, hyI i ((hx i).mp hi), sub_self]
    obtain ⟨δ, hδ, _, hzP⟩ := halfspace_two_sided_perturbation f h hxP hv
    have hxmax : ∀ z ∈ halfspaceRegion f h, l z ≤ l x := by
      rw [hl] at hxF
      exact hxF.2
    have hzmax := hxmax (x - δ • (y - x)) hzP
    have hymax := hxmax y hyP
    have hly : l y = l x := by
      simp only [map_sub, map_smul, smul_eq_mul] at hzmax
      nlinarith
    rw [hl]
    exact ⟨hyP, fun z hz => (hxmax z hz).trans_eq hly.symm⟩

/-- Actual exposed faces inherit the finite vertex hull representation. -/
theorem exposedFace_eq_convexHull_vertices
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hP : IsCompact (halfspaceRegion f h)) {F : Set E}
    (hF : IsExposed ℝ (halfspaceRegion f h) F) :
    F = convexHull ℝ (F ∩ (halfspaceRegion f h).extremePoints ℝ) := by
  have hFE := hF.isExtreme
  have hfin : (F.extremePoints ℝ).Finite :=
    (halfspace_extremePoints_finite f h).subset hFE.extremePoints_subset_extremePoints
  have hh := closure_convexHull_extremePoints (hF.isCompact hP)
    (hF.convex (convex_halfspaceRegion f h))
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hh
  rw [hFE.extremePoints_eq] at hh
  exact hh.symm

end NormalProjective

