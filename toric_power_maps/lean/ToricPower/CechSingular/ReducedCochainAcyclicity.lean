module

public import ToricPower.CechSingular.GlobalCarrierHomotopy

@[expose] public noncomputable section

open ToricPower.CechIncidenceChains ToricPower.CechAcyclicCarrier
open ToricPower.NegativeSupportCech ToricPower.NegativeSupportRelative

/-! ## Exact generic source: ReducedCochainAcyclicity -/
section Source_ReducedCochainAcyclicity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open BondalThomsen.ClosedConvexNerveComparison
open BondalThomsen.ConvexNerveRealizationEquivalence
open BondalThomsen.ConvexNerveGlobalCarrierHomotopy
open ToricPower.NegativeSupportCech
open ToricPower.NegativeSupportRelative
open scoped Classical Simplicial

variable (𝕜 : Type) [Field 𝕜]

attribute [local instance] Classical.decEq

namespace BondalThomsen.ConvexNerveReducedCochainAcyclicity

section AffineSimplices

variable {Ray : Type*} {Chart : Type} [Finite Chart]

def incidencePatches (incidence : Ray → Chart → Prop) (negative : Ray → Prop) : Chart → Set Ray :=
  fun chart => {ray | negative ray ∧ incidence ray chart}

omit [Finite Chart] in
theorem incidencePatches_coverNerve (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    coverNerve (incidencePatches incidence negative) = negativeChartComplex incidence negative := by
  apply PreAbstractSimplicialComplex.ext
  ext face
  change face ∈ coverNerve (incidencePatches incidence negative) ↔
    face ∈ negativeChartComplex incidence negative
  rw [mem_coverNerve_iff]
  change (face.Nonempty ∧ ∃ ray, ∀ chart ∈ face, negative ray ∧ incidence ray chart) ↔
    face.Nonempty ∧ ∃ ray, negative ray ∧ ∀ chart ∈ face, incidence ray chart
  constructor
  · rintro ⟨nonempty, ray, contains⟩
    obtain ⟨chart, present⟩ := nonempty.exists_mem
    exact ⟨nonempty, ray, (contains chart present).1, fun chart member => (contains chart member).2⟩
  · rintro ⟨nonempty, ray, negative_ray, contains⟩
    exact ⟨nonempty, ray, fun chart member => ⟨negative_ray, contains chart member⟩⟩

noncomputable abbrev incidenceRealization (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :=
  AbstractSimplicialComplex.Realization (activeNerve (incidencePatches incidence negative))

noncomputable def tupleActiveVertex (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) (index : Fin (degree + 1)) :
    ActiveIndex (incidencePatches incidence negative) :=
  ⟨tuple.val index, by
    obtain ⟨ray, negative_ray, contains⟩ := tuple.property
    exact ⟨ray, negative_ray, contains index⟩⟩

noncomputable def tupleAffineSimplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    C(Convexity.StdSimplex ℝ (Fin (degree + 1)), incidenceRealization incidence negative) where
  toFun point := simplexToRealization (activeNerve (incidencePatches incidence negative))
    (point.map (tupleActiveVertex incidence negative degree tuple)) (by
      change (point.map _).weights.support.image Subtype.val ∈ coverNerve (incidencePatches incidence negative)
      rw [incidencePatches_coverNerve]
      apply (negativeChartComplex incidence negative).isRelLowerSet_faces.mem_of_le
        ((tupleForbidden_iff_face incidence negative degree tuple.val).mp tuple.property)
      · rw [Convexity.StdSimplex.weights_map]
        apply Finset.Subset.trans (Finset.image_subset_image Finsupp.mapDomain_support)
        rw [Finset.image_image]
        exact Finset.image_subset_image (Finset.subset_univ _)
      · exact (Convexity.StdSimplex.support_weights_nonempty _).image _)
  continuous_toFun := (continuous_into_realization_iff _ _).mpr fun index =>
    (continuous_apply index).comp
      ((Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous.comp
        (Convexity.StdSimplex.continuous_map ℝ _))

theorem tupleAffineSimplex_precomp (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {degree next : ℕ} (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : forbiddenTuple incidence negative next) (point : Convexity.StdSimplex ℝ (Fin (degree + 1))) :
    tupleAffineSimplex incidence negative degree
      ⟨tuple.val ∘ selection, tupleForbidden_precomp incidence negative selection tuple.val tuple.property⟩ point =
    tupleAffineSimplex incidence negative next tuple (point.map selection) := by
  apply Subtype.ext
  change (point.map _).weights = ((point.map selection).map _).weights
  rw [← Convexity.StdSimplex.map_comp]
  rfl

end AffineSimplices

section SingularSimplices

variable {Ray : Type*} {Chart : Type} [Finite Chart]

noncomputable def tupleSingularSimplex (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    (degree : ℕ) (tuple : forbiddenTuple incidence negative degree) :
    (TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative))).obj (.op ⦋degree⦌) :=
  (TopCat.toSSetObjEquiv _ _).symm (tupleAffineSimplex incidence negative degree tuple)

theorem tupleSingularSimplex_precomp (incidence : Ray → Chart → Prop) (negative : Ray → Prop)
    {source target : SimplexCategory} (selection : source ⟶ target)
    (tuple : forbiddenTuple incidence negative target.len) :
    (TopCat.toSSet.obj (TopCat.of (incidenceRealization incidence negative))).map selection.op
      (tupleSingularSimplex incidence negative target.len tuple) =
    tupleSingularSimplex incidence negative source.len
      ⟨tuple.val ∘ selection.toOrderHom,
        tupleForbidden_precomp incidence negative selection.toOrderHom tuple.val tuple.property⟩ := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  apply ContinuousMap.ext
  intro point
  exact (tupleAffineSimplex_precomp incidence negative selection.toOrderHom tuple point).symm

end SingularSimplices

section DualSingularComplex

noncomputable abbrev integralSingularChains (Space : Type) [TopologicalSpace Space] :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  (TopCat.toSSet.obj (TopCat.of Space)).chainComplex (AddCommGrpCat.of ℤ)

end DualSingularComplex

section SingularHomotopies

noncomputable def integralSingularChainHomotopyEquiv {Space Target : Type}
    [TopologicalSpace Space] [TopologicalSpace Target]
    (equivalence : ContinuousMap.HomotopyEquiv Space Target) :
    HomotopyEquiv (integralSingularChains Space) (integralSingularChains Target) := by
  let functor := (AlgebraicTopology.singularChainComplexFunctor.{0, 0, 1} AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
  let source_homotopy := equivalence.left_inv.some
  let target_homotopy := equivalence.right_inv.some
  refine {
    hom := functor.map (TopCat.ofHom equivalence.toFun)
    inv := functor.map (TopCat.ofHom equivalence.invFun)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_
  }
  · have homotopy : TopCat.Homotopy
        (TopCat.ofHom equivalence.toFun ≫ TopCat.ofHom equivalence.invFun)
        (𝟙 (TopCat.of Space)) := source_homotopy
    have result := homotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
    change Homotopy (functor.map (TopCat.ofHom equivalence.toFun ≫ TopCat.ofHom equivalence.invFun))
      (functor.map (𝟙 (TopCat.of Space))) at result
    rw [functor.map_comp] at result
    exact result.trans (Homotopy.ofEq (functor.map_id (TopCat.of Space)))
  · have homotopy : TopCat.Homotopy
        (TopCat.ofHom equivalence.invFun ≫ TopCat.ofHom equivalence.toFun)
        (𝟙 (TopCat.of Target)) := target_homotopy
    have result := homotopy.singularChainComplexFunctorObjMap (AddCommGrpCat.of ℤ)
    change Homotopy (functor.map (TopCat.ofHom equivalence.invFun ≫ TopCat.ofHom equivalence.toFun))
      (functor.map (𝟙 (TopCat.of Target))) at result
    rw [functor.map_comp] at result
    exact result.trans (Homotopy.ofEq (functor.map_id (TopCat.of Target)))

end SingularHomotopies

end BondalThomsen.ConvexNerveReducedCochainAcyclicity

end Source_ReducedCochainAcyclicity
