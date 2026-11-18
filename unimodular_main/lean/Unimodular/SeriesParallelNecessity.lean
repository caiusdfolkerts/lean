module

public import Unimodular.SeriesParallelMatrixReduction
public import Unimodular.SeriesParallelIntegralGraphic
public import Unimodular.SeriesParallelMinorClosure

@[expose] public section

open scoped BigOperators Matroid
open Set TauCeti.Toric

namespace Unimodular.VectorMatroid

noncomputable section

/-- An injective linear change of coordinates preserves every independent
subset of a represented matroid. -/
theorem ofFamily_comp_injective {K α V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (v : α → V) (f : V →ₗ[K] W) (hf : Function.Injective f) :
    ofFamily (K := K) (f ∘ v) = ofFamily (K := K) v := by
  apply (ofFamily_eq_iff _ _).mpr
  intro S
  change LinearIndependent K (f ∘ (fun a : S => v a.val)) ↔
    LinearIndependent K (fun a : S => v a.val)
  exact f.linearIndependent_iff (LinearMap.ker_eq_bot.mpr hf)

end
end Unimodular.VectorMatroid

namespace Unimodular.SeriesParallel

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w z

/-- Split a labeled configuration into its designated basis labels and all
remaining labels. This is an actual bijection, so no duplicate or antipodal
column is discarded. -/
def splitBasisLabels {I : Type u} {E : Type v} (h : I ↪ E) :
    I ⊕ {e : E // e ∉ Set.range h} ≃ E :=
  (Equiv.sumCongr (Equiv.ofInjective h h.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range h))

@[simp] theorem splitBasisLabels_left {I : Type u} {E : Type v} (h : I ↪ E) (i : I) :
    splitBasisLabels h (.inl i) = h i := rfl

@[simp] theorem splitBasisLabels_right {I : Type u} {E : Type v} (h : I ↪ E)
    (e : {e : E // e ∉ Set.range h}) : splitBasisLabels h (.inr e) = e.val := rfl

/-- Every finite labeled ray family containing a lattice basis has a standard
series--parallel matroid. Completeness, regularity, and the genuine corner
criterion are the only geometric hypotheses; the basis labels may be chosen
from any of the actual rays. -/
theorem ray_family_seriesParallel {I : Type u} {E : Type v} {N : Type w} {V : Type z}
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) (b : Module.Basis I ℤ N)
    (U : E → N) (hU : ∀ e, ConeBases.IsRay Φ (U e))
    (basisLabels : I ↪ E) (hB : ∀ i, U (basisLabels i) = b i) :
    FiniteSeriesParallel (VectorMatroid.ofFamily (K := ℝ) (fun e => ι (U e))) := by
  classical
  let J := {e : E // e ∉ Set.range basisLabels}
  let A : I → J → ℤ := fun i j => b.repr (U j.val) i
  have hb : ∀ i, ConeBases.IsRay Φ (b i) := fun i => hB i ▸ hU (basisLabels i)
  have huniform := FanBridge.uniform_of_positiveCriterion Φ hc hr hp b
  have hsmall : SmallMinors A := by
    constructor
    · intro i j
      exact Heller.coordinate_abs_le_one b {u | ConeBases.IsRay Φ u}
        huniform hb (hU j.val) i
    · intro i k j l
      by_cases hik : i = k
      · subst k
        simp [A, mul_comm]
      · simpa only [A, mul_comm (b.repr (U j.val) k) (b.repr (U l.val) i)] using
          Heller.two_coordinate_minor_abs_le_one b {u | ConeBases.IsRay Φ u}
            huniform hb (hU j.val) (hU l.val) hik
  have hforbidden : MatrixForbidden A :=
    fan_supportGraph_forbidden Φ hc hr hp b hb (fun j : J => U j.val)
      (fun j => hU j.val)
  have hmatrix := matrix_finite_seriesParallel A hsmall hforbidden
  let e := splitBasisLabels basisLabels
  let c := CoordinateQuotients.realBasis ι Φ.lattice b
  let w : E → I → ℝ := fun a => c.equivFun (ι (U a))
  have he : ∀ a : I ⊕ J, w (e a) = matrixColumns A a := by
    intro a
    cases a with
    | inl i =>
      have hei : e (.inl i) = basisLabels i := splitBasisLabels_left basisLabels i
      rw [hei]
      ext k
      simp [w, c, hB, Module.Basis.equivFun_apply,
        CoordinateQuotients.realBasis_repr, matrixColumns, Pi.basisFun_apply,
        Module.Basis.repr_self_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
    | inr j =>
      ext i
      exact CoordinateQuotients.realBasis_repr ι Φ.lattice b (U j.val) i
  have hmap := VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (K := ℝ) (matrixColumns A) w e.toEmbedding he
  have hrange : Set.range e.toEmbedding = Set.univ := Set.range_eq_univ.mpr e.surjective
  rw [hrange] at hmap
  have hcoordinates : VectorMatroid.ofFamily (K := ℝ) w =
      VectorMatroid.ofFamily (K := ℝ) (fun a => ι (U a)) :=
    VectorMatroid.ofFamily_comp_injective (fun a => ι (U a)) c.equivFun.toLinearMap
      c.equivFun.injective
  have hresult := hmatrix.relabel e
  change FiniteSeriesParallel ((VectorMatroid.ofFamily (K := ℝ) (matrixColumns A)).mapEmbedding
    e.toEmbedding) at hresult
  rw [hmap] at hresult
  change FiniteSeriesParallel (VectorMatroid.ofFamily (K := ℝ) w) at hresult
  rwa [hcoordinates] at hresult

/-- The complete actual primitive-ray set of a complete regular fan satisfying
the corner criterion is finite. The coordinate fan presentation supplies an
explicit finite collection, and the integral coordinate equivalence is injective. -/
theorem finite_primitive_rays {N : Type w} {V : Type z} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) : {u | ConeBases.IsRay Φ u}.Finite := by
  obtain ⟨C, hC, hfull, _⟩ := FanMaximalCones.full_cones_cover Φ hc 0
  obtain ⟨n, b, hCb⟩ := ConeBases.exists_basis_of_full_regular Φ.lattice
    (Fan.isRegular_iff.mp hr C hC) hfull
  obtain ⟨σ, _, hσ⟩ := FanBridge.exists_smoothCompleteFan_in_basis Φ hc hr hp b
  have hfin : σ.rays.Finite := by
    have heq : (σ.rayFinset : Set (Lattice n)) = σ.rays := by
      ext u
      exact σ.mem_rayFinset u
    rw [← heq]
    exact σ.rayFinset.finite_toSet
  have heq : {u | ConeBases.IsRay Φ u} = b.equivFun ⁻¹' σ.rays := Set.ext hσ
  rw [heq]
  exact Set.Finite.preimage b.equivFun.injective.injOn hfin

/-- The principal necessity statement in Theorems 1.2 and 6.6: the matroid of
all actual signed primitive ray vectors of every complete regular fan satisfying
the deeply monotone corner criterion is a direct sum of ordinary series--parallel
networks. The class is defined and independently justified using eligible
ordinary circuits, cocircuits, deletion, and contraction. -/
theorem fan_rayMatroid_seriesParallel {N : Type w} {V : Type z} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) :
    FiniteSeriesParallel (VectorMatroid.ofFamily (K := ℝ)
      (fun u : {u : N // ConeBases.IsRay Φ u} => ι u.val)) := by
  classical
  let E := {u : N // ConeBases.IsRay Φ u}
  letI : Fintype E := (finite_primitive_rays Φ hc hr hp).fintype
  obtain ⟨C, hC, hfull, _⟩ := FanMaximalCones.full_cones_cover Φ hc 0
  obtain ⟨n, b, hCb⟩ := ConeBases.exists_basis_of_full_regular Φ.lattice
    (Fan.isRegular_iff.mp hr C hC) hfull
  have hb : ConeBases.cone (ι := ι) b ∈ Φ.cones := hCb ▸ hC
  let labels : Fin n ↪ E :=
    { toFun := fun i => ⟨b i, ConeBases.isRay_basis Φ b hb i⟩
      inj' := fun _ _ h => b.injective (congrArg Subtype.val h) }
  exact ray_family_seriesParallel Φ hc hr hp b (fun u : E => u.val)
    (fun u => u.property) labels (fun _ => rfl)

/-- The integral version of the family theorem. The output is a basis of the
original lattice, and every original signed vector is literally a difference
of its vertex vectors. No orientation-uniqueness theorem is assumed. -/
theorem ray_family_integral_incidence {I : Type u} {E : Type v} {N : Type w} {V : Type z}
    [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) (b : Module.Basis I ℤ N)
    (U : E → N) (hU : ∀ e, ConeBases.IsRay Φ (U e))
    (basisLabels : I ↪ E) (hB : ∀ i, U (basisLabels i) = b i) :
    ∃ d : Module.Basis I ℤ N, ∀ a : E, ∃ p q : Option I,
      U a = basisVertex d p - basisVertex d q := by
  classical
  let J := {e : E // e ∉ Set.range basisLabels}
  let A : I → J → ℤ := fun i j => b.repr (U j.val) i
  have hb : ∀ i, ConeBases.IsRay Φ (b i) := fun i => hB i ▸ hU (basisLabels i)
  have huniform := FanBridge.uniform_of_positiveCriterion Φ hc hr hp b
  have hsmall : SmallMinors A := by
    constructor
    · intro i j
      exact Heller.coordinate_abs_le_one b {u | ConeBases.IsRay Φ u}
        huniform hb (hU j.val) i
    · intro i k j l
      by_cases hik : i = k
      · subst k
        simp [A, mul_comm]
      · simpa only [A, mul_comm (b.repr (U j.val) k) (b.repr (U l.val) i)] using
          Heller.two_coordinate_minor_abs_le_one b {u | ConeBases.IsRay Φ u}
            huniform hb (hU j.val) (hU l.val) hik
  have hforbidden : MatrixForbidden A :=
    fan_supportGraph_forbidden Φ hc hr hp b hb (fun j : J => U j.val)
      (fun j => hU j.val)
  obtain ⟨c, hincidence⟩ := matrix_integralGraphic A hsmall hforbidden
  let e := splitBasisLabels basisLabels
  let d := c.map b.equivFun.symm
  have hcolumn : ∀ a : I ⊕ J, b.equivFun (U (e a)) = matrixIntColumns A a := by
    intro a
    cases a with
    | inl i =>
      have hei : e (.inl i) = basisLabels i := splitBasisLabels_left basisLabels i
      rw [hei, hB]
      ext k
      simp [matrixIntColumns, Module.Basis.equivFun_apply,
        Module.Basis.repr_self_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
    | inr j => rfl
  have hvertex : ∀ p : Option I, basisVertex d p = b.equivFun.symm (basisVertex c p) := by
    intro p
    cases p <;> simp [d, basisVertex]
  refine ⟨d, ?_⟩
  intro a
  obtain ⟨p, q, hpq⟩ := hincidence (e.symm a)
  refine ⟨p, q, ?_⟩
  apply b.equivFun.injective
  rw [map_sub, hvertex, hvertex, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]
  have hcol := hcolumn (e.symm a)
  simpa only [Equiv.apply_symm_apply] using hcol.trans hpq

/-- The actual primitive vectors in Theorem 6.6 admit an integral directed
incidence realization. Edge labels are exactly the primitive rays, so antipodal
pairs and all original vector signs are retained. The basis gives the integral
lattice isomorphism explicitly. -/
theorem fan_ray_configuration_integral_incidence {N : Type w} {V : Type z}
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N)
      (source target : {u : N // ConeBases.IsRay Φ u} → Option (Fin n)),
      ∀ u, u.val = basisVertex b (source u) - basisVertex b (target u) := by
  classical
  let E := {u : N // ConeBases.IsRay Φ u}
  letI : Fintype E := (finite_primitive_rays Φ hc hr hp).fintype
  obtain ⟨C, hC, hfull, _⟩ := FanMaximalCones.full_cones_cover Φ hc 0
  obtain ⟨n, b, hCb⟩ := ConeBases.exists_basis_of_full_regular Φ.lattice
    (Fan.isRegular_iff.mp hr C hC) hfull
  have hb : ConeBases.cone (ι := ι) b ∈ Φ.cones := hCb ▸ hC
  let labels : Fin n ↪ E :=
    { toFun := fun i => ⟨b i, ConeBases.isRay_basis Φ b hb i⟩
      inj' := fun _ _ h => b.injective (congrArg Subtype.val h) }
  obtain ⟨d, hd⟩ := ray_family_integral_incidence Φ hc hr hp b (fun u : E => u.val)
    (fun u => u.property) labels (fun _ => rfl)
  choose source target hvec using hd
  exact ⟨n, d, source, target, hvec⟩

/-- The necessity direction of the exact minor-class assertion, with ordinary
Mathlib matroid minors and their actual retained ground sets. -/
theorem fan_rayMatroid_all_minors_seriesParallel {N : Type w} {V : Type z}
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ)
    {M : Matroid {u : N // ConeBases.IsRay Φ u}}
    (hM : M ≤m VectorMatroid.ofFamily (K := ℝ)
      (fun u : {u : N // ConeBases.IsRay Φ u} => ι u.val)) :
    GroundSeriesParallel M :=
  (fan_rayMatroid_seriesParallel Φ hc hr hp).groundConstruction.minor hM

/-- The same theorem on the literal primitive-ray subset of the original
lattice. The label embedding is proved to recover exactly this on-set matroid. -/
theorem fan_onSet_rayMatroid_seriesParallel {N : Type w} {V : Type z}
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) :
    GroundSeriesParallel (VectorMatroid.onSet (K := ℝ) (fun u : N => ι u)
      {u | ConeBases.IsRay Φ u}) := by
  let f : {u : N // ConeBases.IsRay Φ u} ↪ N := ⟨Subtype.val, Subtype.val_injective⟩
  have h := (fan_rayMatroid_seriesParallel Φ hc hr hp).groundConstruction.mapEmbedding f
  have heq := VectorMatroid.ofFamily_mapEmbedding_eq_onSet (K := ℝ)
    (fun u : {u : N // ConeBases.IsRay Φ u} => ι u.val) (fun u : N => ι u) f (fun _ => rfl)
  have hrange : Set.range f = {u | ConeBases.IsRay Φ u} := by
    ext u
    simp [f]
  rwa [heq, hrange] at h

/-- All actual deletion/contraction minors on the original lattice ground set
belong to the standard series--parallel class. -/
theorem fan_onSet_rayMatroid_all_minors_seriesParallel {N : Type w} {V : Type z}
    [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) {M : Matroid N}
    (hM : M ≤m VectorMatroid.onSet (K := ℝ) (fun u : N => ι u)
      {u | ConeBases.IsRay Φ u}) : GroundSeriesParallel M :=
  (fan_onSet_rayMatroid_seriesParallel Φ hc hr hp).minor hM

#print axioms Unimodular.SeriesParallel.ray_family_seriesParallel
#print axioms Unimodular.SeriesParallel.fan_rayMatroid_seriesParallel
#print axioms Unimodular.SeriesParallel.fan_ray_configuration_integral_incidence
#print axioms Unimodular.SeriesParallel.fan_rayMatroid_all_minors_seriesParallel

end
end Unimodular.SeriesParallel
