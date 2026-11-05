module

public import VolumePolynomials.FinitePolytope
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false

/-!
# Finite halfspace systems and generic support heights

The exceptional support vectors form a finite union of proper linear
subspaces. Outside this union every feasible active system is independent,
and at an extreme point it is an actual coordinate system. This is the
linear-algebraic content of the simple-polytope perturbation argument in
Schneider, *Convex Bodies*, Lemmas 2.4.13--2.4.14.

No assertion about mixed volumes is assumed or encoded in these definitions.
-/

noncomputable section
open Set Filter Module
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def body (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Set E :=
  {x | ∀ i, l i x ≤ h i}

theorem body_convex (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    Convex ℝ (body l h) := by
  first
  | have he (i : ι) : (l i).toLinearMap ⁻¹' Iic (h i) = {x : E | l i x ≤ h i} := by
      ext x
      simp only [mem_preimage, mem_Iic, ContinuousLinearMap.coe_coe, mem_ofPred_eq]
    simpa only [body, Set.ofPred_forall, he] using
      (convex_iInter fun i => (convex_Iic (h i)).linear_preimage (l i).toLinearMap)

theorem body_isClosed (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    IsClosed (body l h) := by
  first
  | simpa only [body, Set.ofPred_forall] using
      (isClosed_iInter fun i => isClosed_le (l i).continuous (continuous_const (y := h i)))

def restriction (s : Finset ι) : (ι → ℝ) →ₗ[ℝ] (s → ℝ) where
  toFun h i := h i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evaluation (l : ι → E →L[ℝ] ℝ) (s : Finset ι) : E →ₗ[ℝ] (s → ℝ) :=
  LinearMap.pi (fun i : s => (l i).toLinearMap)

@[simp] theorem restriction_apply (s : Finset ι) (h : ι → ℝ) (i : s) :
    restriction s h i = h i := rfl

@[simp] theorem evaluation_apply (l : ι → E →L[ℝ] ℝ)
    (s : Finset ι) (x : E) (i : s) : evaluation l s x i = l i x := rfl

theorem restriction_surjective (s : Finset ι) : Function.Surjective (restriction s) := by
  first
  | intro r
    refine ⟨fun i => if hi : i ∈ s then r ⟨i, hi⟩ else 0, ?_⟩
    funext i
    simp only [restriction_apply, dif_pos i.property]

/-- Heights on `s` that are jointly attained by some point of the ambient
space. If the active equations are dependent, this is a proper subspace. -/
def compatibleHeights (l : ι → E →L[ℝ] ℝ) (s : Finset ι) :
    Submodule ℝ (ι → ℝ) := (evaluation l s).range.comap (restriction s)

theorem mem_compatibleHeights (l : ι → E →L[ℝ] ℝ) (s : Finset ι) (h : ι → ℝ) :
    h ∈ compatibleHeights l s ↔ ∃ x : E, ∀ i ∈ s, l i x = h i := by
  first
  | constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, fun i hi => congrFun hx ⟨i, hi⟩⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, funext fun i => hx i i.property⟩

theorem compatibleHeights_ne_top (l : ι → E →L[ℝ] ℝ) (s : Finset ι)
    (hs : ¬ Function.Surjective (evaluation l s)) : compatibleHeights l s ≠ ⊤ := by
  first
  | intro heq
    apply hs
    intro r
    obtain ⟨h, hh⟩ := restriction_surjective s r
    have hm : h ∈ compatibleHeights l s := by rw [heq]; trivial
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, hx.trans hh⟩

def Generic (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Prop :=
  ∀ s : Finset ι, h ∈ compatibleHeights l s →
    Function.Surjective (evaluation l s)

open scoped Classical in
theorem generic_eq_iInter (l : ι → E →L[ℝ] ℝ) :
    {h | Generic l h} = ⋂ s : Finset ι,
      if Function.Surjective (evaluation l s) then Set.univ
      else (compatibleHeights l s : Set (ι → ℝ))ᶜ := by
  first
  | classical
    ext h
    simp only [Generic, mem_setOf_eq, mem_iInter]
    apply forall_congr'
    intro s
    by_cases hs : Function.Surjective (evaluation l s) <;> simp [hs]

theorem isOpen_generic (l : ι → E →L[ℝ] ℝ) : IsOpen {h | Generic l h} := by
  first
  | classical
    rw [generic_eq_iInter]
    apply isOpen_iInter_of_finite
    intro s
    split_ifs
    · exact isOpen_univ
    · exact (compatibleHeights l s).closed_of_finiteDimensional.isOpen_compl

/-- Generic support vectors occur in every nonempty open subset of the full
space of heights; no restriction of the number of facets is imposed. -/
theorem dense_generic (l : ι → E →L[ℝ] ℝ) : Dense {h | Generic l h} := by
  first
  | classical
    rw [generic_eq_iInter]
    apply dense_iInter_of_isOpen
    · intro s
      split_ifs
      · exact isOpen_univ
      · exact (compatibleHeights l s).closed_of_finiteDimensional.isOpen_compl
    · intro s
      split_ifs with hs
      · exact dense_univ
      · apply interior_eq_empty_iff_dense_compl.mp
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hi
        exact compatibleHeights_ne_top l s hs
          ((compatibleHeights l s).eq_top_of_nonempty_interior' hi)

def active (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (x : E) : Finset ι :=
  Finset.univ.filter fun i => l i x = h i

@[simp] theorem mem_active (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) (x : E) (i : ι) :
    i ∈ active l h x ↔ l i x = h i := by simp [active]

/-- A point with the same active equalities as an extreme point must equal
that extreme point. The proof uses a two-sided sufficiently small segment. -/
theorem extreme_active_unique (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {x y : E} (hx : x ∈ (body l h).extremePoints ℝ)
    (hy : ∀ i, l i x = h i → l i y = h i) : y = x := by
  first
  | have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
        l i x < h i → l i (x + t • (y - x)) < h i := by
      apply Filter.eventually_all.mpr
      intro i
      by_cases hi : l i x < h i
      · have ht : ∀ᶠ t : ℝ in 𝓝 0, l i (x + t • (y - x)) < h i :=
          (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hi)
        filter_upwards [ht] with t ht
        exact fun _ => ht
      · exact Filter.Eventually.of_forall fun _ hi' => (hi hi').elim
    obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
    have hpert (t : ℝ) (ht : dist t 0 < ε) : x + t • (y - x) ∈ body l h := by
      intro i
      rcases (hx.1 i).lt_or_eq with hi | hi
      · exact (hsmall ht i hi).le
      · simp only [map_add, map_smul, map_sub, smul_eq_mul, hi, hy i hi,
          sub_self, mul_zero, add_zero, le_refl]
    have hp : dist (ε / 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    have hm : dist (-(ε / 2)) 0 < ε := by simpa using hp
    have he := hx.2 (hpert (ε / 2) hp)
      (show x - (ε / 2) • (y - x) ∈ body l h by
        simpa only [neg_smul, ← sub_eq_add_neg] using hpert (-(ε / 2)) hm)
      (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • (y - x)))
    have hz : (ε / 2) • (y - x) = 0 := add_left_cancel (he.trans (add_zero x).symm)
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt (half_pos hε)))

theorem active_evaluation_injective (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    Function.Injective (evaluation l (active l h v)) := by
  first
  | intro x y hxy
    have hz : v + (x - y) = v := by
      apply extreme_active_unique l h hv
      intro i hi
      have he : l i x = l i y := congrFun hxy ⟨i, (mem_active l h v i).mpr hi⟩
      simp [map_add, map_sub, hi, he]
    have hzero : x - y = 0 := add_left_cancel (hz.trans (add_zero v).symm)
    exact sub_eq_zero.mp hzero

theorem active_evaluation_bijective (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    Function.Bijective (evaluation l (active l h v)) := by
  first
  | refine ⟨active_evaluation_injective l h hv, hg (active l h v) ?_⟩
    exact (mem_compatibleHeights l _ h).mpr ⟨v, fun i hi => (mem_active l h v i).mp hi⟩

/-- The finite type of sets of normals that give an ambient coordinate system. -/
def BasisIndex (l : ι → E →L[ℝ] ℝ) :=
  {s : Finset ι // Function.Bijective (evaluation l s)}

instance basisIndex_fintype (l : ι → E →L[ℝ] ℝ) : Fintype (BasisIndex l) := by
  classical
  change Fintype {s : Finset ι // Function.Bijective (evaluation l s)}
  exact Fintype.ofFinite _

def coordinates (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) : E ≃L[ℝ] (b.val → ℝ) :=
  (LinearEquiv.ofBijective (evaluation l b.val) b.property).toContinuousLinearEquiv

@[simp] theorem coordinates_apply (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (x : E) (i : b.val) : coordinates l b x i = l i x := rfl

def vertexMap (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) : (ι → ℝ) →L[ℝ] E :=
  ((coordinates l b).symm.toLinearMap.comp (restriction b.val)).toContinuousLinearMap

@[simp] theorem vertexMap_active (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (h : ι → ℝ) (i : b.val) : l i (vertexMap l b h) = h i := by
  first
  | change (coordinates l b ((coordinates l b).symm (restriction b.val h))) i = h i
    simp only [ContinuousLinearEquiv.apply_symm_apply, restriction_apply]

theorem vertexMap_unique (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (h : ι → ℝ) {x : E} (hx : ∀ i ∈ b.val, l i x = h i) :
    vertexMap l b h = x := by
  first
  | apply (coordinates l b).injective
    funext i
    exact (vertexMap_active l b h i).trans (hx i i.property).symm

theorem extreme_eq_vertexMap (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    ∃ b : BasisIndex l, vertexMap l b h = v := by
  first
  | refine ⟨⟨active l h v, active_evaluation_bijective l h hg hv⟩, ?_⟩
    exact vertexMap_unique l _ h (fun i hi => (mem_active l h v i).mp hi)

theorem vertexMap_mem_extremePoints (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l)
    (h : ι → ℝ) (hv : vertexMap l b h ∈ body l h) :
    vertexMap l b h ∈ (body l h).extremePoints ℝ := by
  first
  | refine ⟨hv, ?_⟩
    intro x hx y hy hseg
    apply (coordinates l b).injective
    funext i
    have he : IsExposed ℝ (body l h) ((l i).toExposed (body l h)) :=
      ContinuousLinearMap.toExposed.isExposed
    have hve : vertexMap l b h ∈ (l i).toExposed (body l h) := by
      refine ⟨hv, fun z hz => ?_⟩
      rw [vertexMap_active]
      exact hz i
    have hxe := he.isExtreme.left_mem_of_mem_openSegment hx hy hve hseg
    have hmax := hxe.2 (vertexMap l b h) hv
    rw [vertexMap_active] at hmax
    exact (le_antisymm (hx i) hmax).trans (vertexMap_active l b h i).symm

theorem finite_extremePoints (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    ((body l h).extremePoints ℝ).Finite := by
  first
  | have hinj : Set.InjOn (active l h) ((body l h).extremePoints ℝ) := by
      intro x hx y _ hxy
      apply (extreme_active_unique l h hx ?_).symm
      intro i hi
      have hm := (mem_active l h x i).mpr hi
      rw [hxy] at hm
      exact (mem_active l h y i).mp hm
    exact (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn
      (fun _ _ => Set.mem_univ _) hinj

theorem body_eq_convexHull_extremePoints (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (body l h)) :
    body l h = convexHull ℝ ((body l h).extremePoints ℝ) := by
  first
  | have he := closure_convexHull_extremePoints hc (body_convex l h)
    rw [(finite_extremePoints l h).isClosed_convexHull ℝ |>.closure_eq] at he
    exact he.symm

theorem generic_active_card (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hg : Generic l h) {v : E} (hv : v ∈ (body l h).extremePoints ℝ) :
    (active l h v).card = finrank ℝ E := by
  first
  | let b : BasisIndex l := ⟨active l h v, active_evaluation_bijective l h hg hv⟩
    have he := (coordinates l b).toLinearEquiv.finrank_eq
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe] using he.symm

end VolumePolynomials.PolyhedralSupport
