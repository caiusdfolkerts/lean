module

public import VolumePolynomials.PolyhedralSupport
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section
set_option autoImplicit false

/-!
# Choosing independent active constraints

At every extreme point of a finite halfspace system, including a nonsimple
one, some active constraints form an ambient coordinate system. This permits
all extreme points to be indexed by a fixed finite set of normal bases.
-/

noncomputable section
open Set Module
open scoped BigOperators

namespace VolumePolynomials.PolyhedralSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem basisIndex_card (l : ι → E →L[ℝ] ℝ) (b : BasisIndex l) :
    b.val.card = finrank ℝ E := by
  first
  | have he := (coordinates l b).toLinearEquiv.finrank_eq
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe] using he.symm

theorem exists_basisIndex_subset (l : ι → E →L[ℝ] ℝ) (s : Finset ι)
    (hs : Function.Injective (evaluation l s)) :
    ∃ b : BasisIndex l, b.val ⊆ s := by
  first
  | classical
    let v : s → Module.Dual ℝ E := fun i => (l i).toLinearMap
    have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
      apply Submodule.span_eq_top_of_ne_zero
      intro z hz
      by_contra! h
      apply hz
      apply hs
      funext i
      simpa only [v, evaluation_apply, map_zero, ContinuousLinearMap.coe_coe] using
        h (v i) ⟨i, rfl⟩
    obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℝ v
    letI : Finite κ := Finite.of_injective a ha
    letI : Fintype κ := Fintype.ofFinite κ
    let f : κ → ι := fun k => (a k).val
    have hf : Function.Injective f := Subtype.val_injective.comp ha
    let t : Finset ι := Finset.univ.image f
    have ht : t ⊆ s := by
      intro i hi
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      exact (a k).property
    have hcard : t.card = finrank ℝ E := by
      let B : Basis κ ℝ (Module.Dual ℝ E) := Basis.mk hli (by rw [hsp, hspan])
      rw [show t.card = Fintype.card κ by
        simp only [t, Finset.card_image_of_injective _ hf, Finset.card_univ]]
      simpa only [Subspace.dual_finrank_eq] using (Module.finrank_eq_card_basis B).symm
    have hinj : Function.Injective (evaluation l t) := by
      intro x y hxy
      apply sub_eq_zero.mp
      apply (Module.forall_dual_apply_eq_zero_iff ℝ (x - y)).mp
      intro φ
      have hφ : φ ∈ Submodule.span ℝ (Set.range (v ∘ a)) := by
        rw [hsp, hspan]
        trivial
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨k, rfl⟩ := hφ
        have hk : f k ∈ t := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
        have he := congrFun hxy ⟨f k, hk⟩
        change l (f k) x = l (f k) y at he
        change l (f k) (x - y) = 0
        rw [map_sub, he, sub_self]
      | zero => rfl
      | add φ ψ _ _ hφ hψ => simp only [LinearMap.add_apply, hφ, hψ, add_zero]
      | smul r φ _ hφ => simp only [LinearMap.smul_apply, hφ, smul_zero]
    have hdim : finrank ℝ E = finrank ℝ (t → ℝ) := by
      simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe] using hcard.symm
    exact ⟨⟨t, hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩,
      ht⟩

theorem extreme_eq_vertexMap_without_generic (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    {x : E} (hx : x ∈ (body l h).extremePoints ℝ) :
    ∃ b : BasisIndex l, vertexMap l b h = x := by
  first
  | obtain ⟨b, hb⟩ := exists_basisIndex_subset l (active l h x)
      (active_evaluation_injective l h hx)
    exact ⟨b, vertexMap_unique l b h (fun i hi => (mem_active l h x i).mp (hb hi))⟩

def feasibleBases (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) : Set (BasisIndex l) :=
  {b | vertexMap l b h ∈ body l h}

theorem extremePoints_eq_vertices (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ) :
    (body l h).extremePoints ℝ =
      (fun b : BasisIndex l => vertexMap l b h) '' feasibleBases l h := by
  first
  | ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := extreme_eq_vertexMap_without_generic l h hx
      refine ⟨b, ?_, hb⟩
      change vertexMap l b h ∈ body l h
      rw [hb]
      exact hx.1
    · rintro ⟨b, hb, rfl⟩
      exact vertexMap_mem_extremePoints l b h hb

theorem body_eq_convexHull_vertices (l : ι → E →L[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (body l h)) :
    body l h = convexHull ℝ
      ((fun b : BasisIndex l => vertexMap l b h) '' feasibleBases l h) := by
  first
  | rw [body_eq_convexHull_extremePoints l h hc, extremePoints_eq_vertices]

end VolumePolynomials.PolyhedralSupport
