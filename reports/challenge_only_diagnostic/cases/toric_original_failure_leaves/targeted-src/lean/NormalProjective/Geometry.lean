module
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith

/-!
# Finite halfspace geometry

Reconstructed after the execution filesystem was replaced.
This module remains an uncompiled candidate until an actual check succeeds.
-/

@[expose] public section
noncomputable section
open Set Filter Module Matrix
open scoped Topology BigOperators

namespace NormalProjective

section Perturbation

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

def halfspaceRegion (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) : Set E :=
  {x | ∀ i, f i x ≤ h i}

def ActiveFacet (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) (x : E) :=
  {i : ι // f i x = h i}

instance activeFacetFintype (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) (x : E) :
    Fintype (ActiveFacet f h x) :=
  by
    classical
    unfold ActiveFacet
    infer_instance

theorem halfspace_two_sided_perturbation
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) {x v : E}
    (hx : x ∈ halfspaceRegion f h)
    (hv : ∀ i, f i x = h i → f i v = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      x + δ • v ∈ halfspaceRegion f h ∧
      x - δ • v ∈ halfspaceRegion f h := by
  classical
  have hnear : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, f i (x + t • v) ≤ h i := by
    intro i
    by_cases hi : f i x = h i
    · filter_upwards [] with t
      simp [map_add, map_smul, hi, hv i hi]
    · have his : f i x < h i := lt_of_le_of_ne (hx i) hi
      have ho : IsOpen {t : ℝ | f i x + t * f i v < h i} :=
        isOpen_lt (continuous_const.add (continuous_id.mul continuous_const)) continuous_const
      have hzero : (0 : ℝ) ∈ {t : ℝ | f i x + t * f i v < h i} := by
        simpa using his
      filter_upwards [ho.mem_nhds hzero] with t ht
      simpa only [map_add, map_smul, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, f i (x + t • v) ≤ h i :=
    Filter.eventually_all.mpr hnear
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hall
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp : δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ]
    dsimp [δ]
    linarith
  have hm : -δ ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ]
    dsimp [δ]
    linarith
  refine ⟨δ, hδ, hball hp, ?_⟩
  have hm' : ∀ i, f i (x + (-δ) • v) ≤ h i := hball hm
  simpa only [halfspaceRegion, mem_setOf_eq, neg_smul, sub_eq_add_neg] using hm'

theorem active_normals_separate
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) {x : E}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ)
    {v : E} (hv : ∀ i, f i x = h i → f i v = 0) : v = 0 := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hδ, hp, hm⟩ := halfspace_two_sided_perturbation f h hx.1 hv
  have heq : x - δ • v = x :=
    hx.2 hm hp (mem_openSegment_sub_add x (δ • v))
  have hsv : δ • v = 0 := sub_eq_self.mp heq
  exact (smul_eq_zero.mp hsv).resolve_left (ne_of_gt hδ)

def activeFacetSet (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) (x : E) : Set ι :=
  {i | f i x = h i}

theorem extreme_activeFacetSet_injective
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) :
    Function.Injective
      (fun x : (halfspaceRegion f h).extremePoints ℝ =>
        activeFacetSet f h x.val) := by
  intro x y hxy
  change activeFacetSet f h x.val = activeFacetSet f h y.val at hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply active_normals_separate f h x.property
  intro i hi
  have hyi : f i y.val = h i := by
    have hmem : i ∈ activeFacetSet f h x.val := hi
    change i ∈ activeFacetSet f h y.val
    rw [← hxy]
    exact hmem
  simp [map_sub, hi, hyi]

theorem halfspace_extremePoints_finite
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) :
    ((halfspaceRegion f h).extremePoints ℝ).Finite := by
  classical
  letI : Finite ((halfspaceRegion f h).extremePoints ℝ) :=
    Finite.of_injective _ (extreme_activeFacetSet_injective f h)
  exact Set.toFinite _

theorem convex_halfspaceRegion (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) :
    Convex ℝ (halfspaceRegion f h) := by
  intro x hx y hy a b ha hb hab i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * f i x + b * f i y ≤ a * h i + b * h i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = h i := by rw [← add_mul, hab, one_mul]

end Perturbation

section Compact

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem isClosed_halfspaceRegion (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) :
    IsClosed (halfspaceRegion f h) := by
  simpa only [halfspaceRegion, Set.setOf_forall] using
    (isClosed_iInter fun i =>
      isClosed_le (f i).continuous_of_finiteDimensional continuous_const)

theorem compact_halfspace_eq_convexHull_extremePoints
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) :
    halfspaceRegion f h =
      convexHull ℝ ((halfspaceRegion f h).extremePoints ℝ) := by
  have hh := closure_convexHull_extremePoints hc (convex_halfspaceRegion f h)
  rw [((halfspace_extremePoints_finite f h).isClosed_convexHull ℝ).closure_eq] at hh
  exact hh.symm

theorem compact_halfspace_has_extremePoint
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ)
    (hc : IsCompact (halfspaceRegion f h)) (hn : (halfspaceRegion f h).Nonempty) :
    ((halfspaceRegion f h).extremePoints ℝ).Nonempty :=
  hc.extremePoints_nonempty hn

theorem active_normals_span_dual
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) {x : E}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ) :
    Submodule.span ℝ (Set.range (fun i : ActiveFacet f h x => f i.val)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  by_contra hno
  apply hv
  apply active_normals_separate f h hx
  intro i hi
  by_contra hne
  exact hno ⟨f i, ⟨⟨i, hi⟩, rfl⟩, hne⟩

end Compact

section Coordinates

variable {d : ℕ} {ι : Type*} [Fintype ι]

def facetCoefficientMatrix
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) : Matrix ι (Fin d) ℝ :=
  fun i j => f i (Pi.single j 1)

theorem facetCoefficientMatrix_mulVec
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    facetCoefficientMatrix f *ᵥ x = fun i => f i x := by
  classical
  ext i
  change (∑ j, f i (Pi.single j 1) * x j) = f i x
  calc
    (∑ j, f i (Pi.single j 1) * x j) =
        ∑ j, x j * f i (Pi.single j 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _
    _ = f i (∑ j, x j • Pi.single j 1) := by simp
    _ = f i x := by
      congr 1
      ext j
      simp [Pi.single_apply, eq_comm]

theorem facetCoefficientMatrix_det_ne_zero
    (f : Fin d → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hf : LinearIndependent ℝ f) :
    (facetCoefficientMatrix f).det ≠ 0 := by
  classical
  let e : Module.Dual ℝ (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
    (Pi.basisFun ℝ (Fin d)).dualBasis.equivFun
  have he (g : Module.Dual ℝ (Fin d → ℝ)) (j : Fin d) :
      e g j = g (Pi.single j 1) := by
    simpa [e] using (Pi.basisFun ℝ (Fin d)).dualBasis_equivFun g j
  have hmap := hf.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hrow : LinearIndependent ℝ (facetCoefficientMatrix f).row := by
    convert hmap using 1
    funext i j
    exact (he (f i) j).symm
  exact ((Matrix.isUnit_iff_isUnit_det (facetCoefficientMatrix f)).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hrow)).ne_zero

theorem extremePoint_has_active_basis
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ) {x : Fin d → ℝ}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ) :
    ∃ I : Fin d ↪ ι,
      (∀ j, f (I j) x = h (I j)) ∧
      LinearIndependent ℝ (fun j => f (I j)) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ :=
    exists_linearIndependent' ℝ (fun i : ActiveFacet f h x => f i.val)
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  let b : Basis κ ℝ (Module.Dual ℝ (Fin d → ℝ)) :=
    Basis.mk hli (by
      rw [hspan, active_normals_span_dual f h hx])
  have hcard : Fintype.card κ = d := by
    simpa [Subspace.dual_finrank_eq] using (Module.finrank_eq_card_basis b).symm
  let e : κ ≃ Fin d := (Fintype.equivFin κ).trans (finCongr hcard)
  let I : Fin d ↪ ι :=
    ⟨fun j => (a (e.symm j)).val,
      fun i j hij => e.symm.injective (ha (Subtype.ext hij))⟩
  refine ⟨I, fun j => (a (e.symm j)).property, ?_⟩
  have hfun : (fun j => f (I j)) = (b.reindex e) := by
    funext j
    simp only [Basis.reindex_apply, b, Basis.mk_apply]
    rfl
  rw [hfun]
  exact (b.reindex e).linearIndependent

theorem extremePoint_has_nonsingular_active_minor
    (f : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ) (h : ι → ℝ) {x : Fin d → ℝ}
    (hx : x ∈ (halfspaceRegion f h).extremePoints ℝ) :
    ∃ I : Fin d ↪ ι,
      ((facetCoefficientMatrix f).submatrix I id).det ≠ 0 ∧
      ((facetCoefficientMatrix f).submatrix I id) *ᵥ x =
        (fun i => h (I i)) := by
  obtain ⟨I, hI, hlin⟩ := extremePoint_has_active_basis f h hx
  refine ⟨I, ?_, ?_⟩
  · exact facetCoefficientMatrix_det_ne_zero (fun i => f (I i)) hlin
  · change facetCoefficientMatrix (fun i => f (I i)) *ᵥ x = _
    rw [facetCoefficientMatrix_mulVec]
    funext i
    exact hI i

end Coordinates
end NormalProjective

