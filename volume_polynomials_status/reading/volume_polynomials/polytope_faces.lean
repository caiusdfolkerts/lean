module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
set_option autoImplicit false

/-!
# Exposed faces and the fixed direction spaces of positive Minkowski sums

These lemmas concern the literal exposed set of a continuous linear functional.
They are valid for arbitrary nonempty compact sets where indicated; no abstract
face lattice, polytope representation, or mixed-volume assertion is assumed.

The final equality is the algebraic step needed to use the facet directions of
the single sum at weights one for every strictly positive assignment of weights.
-/

noncomputable section
open Set
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeFaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A maximizer of a sum is exactly a sum of maximizers. No attainment assumption
is needed: membership on either side already supplies the relevant points. -/
theorem exposed_add (l : E →L[ℝ] ℝ) (A B : Set E) :
    l.toExposed (A + B) = l.toExposed A + l.toExposed B := by
  first
  | ext x
    constructor
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, hmax⟩
      refine ⟨a, ⟨ha, ?_⟩, b, ⟨hb, ?_⟩, rfl⟩
      · intro y hy
        have h := hmax (y + b) ⟨y, hy, b, hb, rfl⟩
        simpa only [map_add, add_le_add_iff_right] using h
      · intro y hy
        have h := hmax (a + y) ⟨a, ha, y, hy, rfl⟩
        simpa only [map_add, add_le_add_iff_left] using h
    · rintro ⟨a, ⟨ha, hma⟩, b, ⟨hb, hmb⟩, rfl⟩
      refine ⟨⟨a, ha, b, hb, rfl⟩, ?_⟩
      rintro y ⟨u, hu, v, hv, rfl⟩
      simpa only [map_add] using add_le_add (hma u hu) (hmb v hv)

theorem exposed_smul (l : E →L[ℝ] ℝ) (A : Set E) {c : ℝ} (hc : 0 < c) :
    l.toExposed (c • A) = c • l.toExposed A := by
  first
  | ext x
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hmax⟩
      refine ⟨a, ⟨ha, ?_⟩, rfl⟩
      intro y hy
      have h := hmax (c • y) ⟨y, hy, rfl⟩
      simp only [map_smul, smul_eq_mul] at h
      exact (mul_le_mul_iff_right₀ hc).mp h
    · rintro ⟨a, ⟨ha, hmax⟩, rfl⟩
      refine ⟨⟨a, ha, rfl⟩, ?_⟩
      rintro y ⟨b, hb, rfl⟩
      simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left (hmax b hb) hc.le

@[simp] theorem exposed_singleton (l : E →L[ℝ] ℝ) (x : E) :
    l.toExposed ({x} : Set E) = {x} := by
  first
  | ext y
    simp only [ContinuousLinearMap.toExposed, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro h
      subst y
      exact ⟨rfl, fun z hz => by subst z; exact le_rfl⟩

theorem exposed_nonempty (l : E →L[ℝ] ℝ) {A : Set E}
    (hA : IsCompact A) (hne : A.Nonempty) : (l.toExposed A).Nonempty := by
  first
  | obtain ⟨x, hx, hmax⟩ := hA.exists_isMaxOn hne l.continuous.continuousOn
    exact ⟨x, hx, hmax⟩

/-- Direction spaces add by taking their supremum, with nonemptiness ensuring
that each original direction can be recovered while the other point is fixed. -/
theorem vectorSpan_add {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty) :
    vectorSpan ℝ (A + B) = vectorSpan ℝ A ⊔ vectorSpan ℝ B := by
  first
  | let L : (E × E) →ₗ[ℝ] E := (LinearMap.id : E →ₗ[ℝ] E).coprod LinearMap.id
    have hset : L.toAffineMap '' (A ×ˢ B) = A + B := by
      ext x
      constructor
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    rw [← hset, ← AffineMap.map_vectorSpan, vectorSpan_prod_eq hA hB]
    simpa only [L, LinearMap.toAffineMap_linear, LinearMap.coprod_map_prod,
      Submodule.map_id]

theorem vectorSpan_smul (A : Set E) {c : ℝ} (hc : c ≠ 0) :
    vectorSpan ℝ (c • A) = vectorSpan ℝ A := by
  first
  | let L : E →ₗ[ℝ] E := c • LinearMap.id
    change vectorSpan ℝ (L.toAffineMap '' A) = _
    rw [← AffineMap.map_vectorSpan]
    exact (Submodule.map_smul LinearMap.id (vectorSpan ℝ A) c hc).trans
      (Submodule.map_id _)

variable {ι : Type*}

theorem exposed_sum (l : E →L[ℝ] ℝ) (s : Finset ι) (A : ι → Set E) :
    l.toExposed (∑ i ∈ s, A i) = ∑ i ∈ s, l.toExposed (A i) := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => simp [← Set.singleton_zero]
    | @insert i s hi ih => simp only [Finset.sum_insert hi, exposed_add, ih]

theorem nonempty_sum (s : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ s, (A i).Nonempty) : (∑ i ∈ s, A i).Nonempty := by
  first
  | classical
    exact Finset.sum_induction A Set.Nonempty (fun _ _ ha hb => ha.add hb)
      (singleton_nonempty 0) hA

theorem vectorSpan_sum (s : Finset ι) (A : ι → Set E) :
    (∀ i ∈ s, (A i).Nonempty) →
      vectorSpan ℝ (∑ i ∈ s, A i) = s.sup (fun i => vectorSpan ℝ (A i)) := by
  first
  | classical
    induction s using Finset.induction_on with
    | empty => intro _; simp [← Set.singleton_zero]
    | @insert i s hi ih =>
        intro hA
        have hs : ∀ j ∈ s, (A j).Nonempty := fun j hj => hA j (Finset.mem_insert_of_mem hj)
        rw [Finset.sum_insert hi,
          vectorSpan_add (hA i (Finset.mem_insert_self i s)) (nonempty_sum s A hs),
          Finset.sup_insert, ih hs]

/-- Strictly positive rescaling preserves the direction space of a finite
Minkowski sum, without requiring the individual sets to be full dimensional. -/
theorem vectorSpan_weighted_sum (s : Finset ι) (A : ι → Set E) (t : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).Nonempty) (ht : ∀ i ∈ s, 0 < t i) :
    vectorSpan ℝ (∑ i ∈ s, t i • A i) = vectorSpan ℝ (∑ i ∈ s, A i) := by
  first
  | have hne : ∀ i ∈ s, (t i • A i).Nonempty := by
      intro i hi
      exact (hA i hi).image (fun x => t i • x)
    rw [vectorSpan_sum s _ hne, vectorSpan_sum s A hA]
    apply Finset.sup_congr rfl
    intro i hi
    exact vectorSpan_smul (A i) (ht i hi).ne'

theorem exposed_weighted_sum (l : E →L[ℝ] ℝ) (s : Finset ι)
    (A : ι → Set E) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 < t i) :
    l.toExposed (∑ i ∈ s, t i • A i) = ∑ i ∈ s, t i • l.toExposed (A i) := by
  first
  | rw [exposed_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact exposed_smul l (A i) (ht i hi)

/-- The direction space of every exposed face is independent of the strictly
positive weights. In particular, its codimension-one property is unchanged. -/
theorem vectorSpan_exposed_weighted_sum (l : E →L[ℝ] ℝ) (s : Finset ι)
    (A : ι → Set E) (t : ι → ℝ)
    (hA : ∀ i ∈ s, IsCompact (A i)) (hne : ∀ i ∈ s, (A i).Nonempty)
    (ht : ∀ i ∈ s, 0 < t i) :
    vectorSpan ℝ (l.toExposed (∑ i ∈ s, t i • A i)) =
      vectorSpan ℝ (l.toExposed (∑ i ∈ s, A i)) := by
  first
  | rw [exposed_weighted_sum l s A t ht, exposed_sum]
    exact vectorSpan_weighted_sum s (fun i => l.toExposed (A i)) t
      (fun i hi => exposed_nonempty l (hA i hi) (hne i hi)) ht

end VolumePolynomials.PolytopeFaces
