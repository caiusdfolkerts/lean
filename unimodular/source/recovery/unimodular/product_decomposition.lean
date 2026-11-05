module

public import Recovery.Unimodular.ProductIntrinsic
public import Recovery.Unimodular.ProductFanRays
public import Recovery.Unimodular.ProductLineMatroid
public import Recovery.Unimodular.NativePort.LiteralRootTransport

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set TauCeti.Toric
open scoped BigOperators

namespace Unimodular.ComponentProducts

open ComponentLattice

variable {n : ℕ}

noncomputable instance componentsFintype (U : Set (Lattice n)) [Finite U] :
    Fintype (Components U) := Fintype.ofFinite _

attribute [local instance] Classical.propDecidable

def factorVector (U : Set (Lattice n)) (c : Components U)
    (u : {u : U // MatroidComponents.component (represented U) u = c}) : latticeSpan U c :=
  ⟨u.val.val, Submodule.subset_span ⟨u.val, u.property, rfl⟩⟩

abbrev LineComponents (U : Set (Lattice n)) :=
  MatroidComponents.Component (LineMatroid.matroid (K := ℝ) (fun u : U => embed u.val))

/-- All data in the canonical product conclusion refer to original sublattices,
actual real spans, actual finite complete fans and every cone. The two inverse
maps are explicitly the sums of the original inclusions. -/
structure CanonicalProduct (U : Set (Lattice n)) [Fintype U]
    (Φ : Fan (standardEmbedding n)) where
  integral : Lattice n ≃ₗ[ℤ] (∀ c : Components U, latticeSpan U c)
  real : Ambient n ≃ₗ[ℝ] (∀ c : Components U, realSpan U c)
  integral_sum : ∀ x, integral.symm x = ∑ c, (x c : Lattice n)
  real_sum : ∀ x, real.symm x = ∑ c, (x c : Ambient n)
  compatible : ∀ x, real (embed x) = fun c => componentEmbedding U c (integral x c)
  factor : ∀ c : Components U, Fan (componentEmbedding U c)
  complete : ∀ c, (factor c).IsComplete
  rays : ∀ c, AllowedBlocks.HasRays (componentEmbedding U c) (factorVector U c) (factor c)
  allCones : ∀ C : PointedCone ℝ (Ambient n), C ∈ Φ.cones ↔
    ∃ D : ∀ c, PointedCone ℝ (realSpan U c),
      (∀ c, D c ∈ (factor c).cones) ∧
      C = (FanProducts.conePi D).map (real.symm : _ →ₗ[ℝ] _)
  summandCones : ∀ c (C : PointedCone ℝ (realSpan U c)),
    C.map (realSpan U c).subtype ∈ Φ.cones ↔ C ∈ (factor c).cones
  unique : ∀ Ω : ∀ c, Fan (componentEmbedding U c),
    (∀ c, (Ω c).IsComplete) →
    (∀ C : PointedCone ℝ (Ambient n), C ∈ Φ.cones ↔
      ∃ D : ∀ c, PointedCone ℝ (realSpan U c),
        (∀ c, D c ∈ (Ω c).cones) ∧
        C = (FanProducts.conePi D).map (real.symm : _ →ₗ[ℝ] _)) → factor = Ω
  lineIndex : Components U ≃ LineComponents U
  lineIndex_apply : ∀ u : U,
    lineIndex (MatroidComponents.component (represented U) u) =
      MatroidComponents.component (LineMatroid.matroid (K := ℝ) (fun u : U => embed u.val))
        (LineMatroid.projection (K := ℝ) (fun u : U => embed u.val) u)

section Construction

variable {U : Set (Lattice n)} [Fintype U]
  (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : ∀ i, b i ∈ U)

theorem decomposition_subtype (c : Components U) (x : realSpan U c) :
    realDecomposition b hb x.val = Pi.single c x := by
  funext d
  by_cases hd : d = c
  · subst d
    simpa only [Pi.single_eq_same] using realDecomposition_of_mem b hb x.property
  · rw [Pi.single_eq_of_ne hd]
    exact realDecomposition_of_mem_ne b hb (Ne.symm hd) x.property

theorem factor_vector_eq_decomposition (c : Components U)
    (u : {u : U // MatroidComponents.component (represented U) u = c}) :
    integralDecomposition b hb u.val.val c = factorVector U c u :=
  BasisPartition.productEquiv_symm_of_mem _ _ (factorVector U c u).property

/- Construction from an actual configuration basis. The main endpoint below
derives this basis from uniformity rather than requiring it as a premise. -/
include b hb in
theorem canonicalProduct_of_basis (hnz : ∀ u : U, embed u.val ≠ 0)
    (Φ : Fan (standardEmbedding n)) (hc : Φ.IsComplete)
    (hr : AllowedBlocks.HasRays (standardEmbedding n) (fun u : U => u.val) Φ) :
    Nonempty (CanonicalProduct U Φ) := by
  classical
  let f := integralDecomposition b hb
  let e := realDecomposition b hb
  let i := componentEmbedding U
  have hi : ∀ c, IsIntegralLattice (i c) := component_isIntegralLattice b hb
  have hfe : ∀ x, e (standardEmbedding n x) = (FanProducts.piEmbedding i) (f x) :=
    decomposition_compatible b hb
  let Ψ := FanTransport.transport f.toAddEquiv e hfe Φ
  let eqv := FanTransport.equivalence f.toAddEquiv e hfe Φ
  have hΨc : Ψ.IsComplete := (FanTransport.transport_complete_iff _ _ _ _).mpr hc
  have hΨr : AllowedBlocks.HasRays (FanProducts.piEmbedding i)
      (fun u : U => f u.val) Ψ :=
    FanTransport.hasRays_of_equiv eqv (fun u => hfe u.val) hr
  let label : U → Components U := MatroidComponents.component (represented U)
  have hs : ∀ u : U, ∀ d : Components U, d ≠ label u → i d (f u.val d) = 0 := by
    intro u d hd
    have hz := ray_decomposition_zero b hb u (Ne.symm hd)
    have he := congrFun (hfe u.val) d
    change realDecomposition b hb (embed u.val) d = i d (f u.val d) at he
    rw [hz] at he
    exact he.symm
  have hnz' : ∀ u : U, (FanProducts.piEmbedding i) (f u.val) ≠ 0 := by
    intro u hu
    apply hnz u
    apply e.injective
    change e (standardEmbedding n u.val) = e 0
    rw [hfe, hu, map_zero]
  let hsR := FanProducts.hasSummandRays_of_hasRays i (fun u : U => f u.val) label Ψ hΨr hs
  let factors := FanProducts.factorFan i hi Ψ hsR
  have hprod := FanProducts.proposition_4_1_cones i hi Ψ hsR hΨc
  have hfacr : ∀ c, AllowedBlocks.HasRays (i c) (factorVector U c) (factors c) := by
    intro c
    have h := FanProducts.factorFan_hasRays i (fun u : U => f u.val) label Ψ
      hi hΨr hnz' hs c
    have hf : (fun u : {u : U // label u = c} => f u.val.val c) = factorVector U c := by
      funext u
      exact factor_vector_eq_decomposition b hb c u
    rw [hf] at h
    exact h
  have horig : ∀ C : PointedCone ℝ (Ambient n), C ∈ Φ.cones ↔
      ∃ D : ∀ c, PointedCone ℝ (realSpan U c), (∀ c, D c ∈ (factors c).cones) ∧
        C = (FanProducts.conePi D).map (e.symm : _ →ₗ[ℝ] _) := by
    intro C
    rw [← eqv.map_mem C, hprod]
    constructor
    · rintro ⟨D, hD, heq⟩
      refine ⟨D, hD, ?_⟩
      change C.map e.toLinearMap = FanProducts.conePi D at heq
      have hh := congrArg (fun F => F.map e.symm.toLinearMap) heq
      simpa only [FanTransport.map_inverse] using hh
    · rintro ⟨D, hD, rfl⟩
      exact ⟨D, hD, FanTransport.map_inverse_rev e _⟩
  refine ⟨{
    integral := f
    real := e
    integral_sum := integralAssembly_apply b hb
    real_sum := realAssembly_apply b hb
    compatible := decomposition_compatible b hb
    factor := factors
    complete := fun c => FanProducts.factorFan_complete i hi Ψ hsR hΨc c
    rays := hfacr
    allCones := horig
    summandCones := ?_
    unique := ?_
    lineIndex := LineMatroid.componentEquiv (K := ℝ) (fun u : U => embed u.val) hnz
    lineIndex_apply := fun u => LineMatroid.componentEquiv_component
      (K := ℝ) (fun u : U => embed u.val) hnz u
  }⟩
  · intro c C
    have hmap : (C.map (realSpan U c).subtype).map (e : _ →ₗ[ℝ] _) =
        C.map (LinearMap.single ℝ (fun c => realSpan U c) c) := by
      rw [PointedCone.map_map]
      congr 1
      apply LinearMap.ext
      intro x
      exact decomposition_subtype b hb c x
    rw [← eqv.map_mem (C.map (realSpan U c).subtype)]
    change (C.map (realSpan U c).subtype).map e.toLinearMap ∈ Ψ.cones ↔
      C ∈ (factors c).cones
    rw [hmap]
    exact FanProducts.map_single_mem_iff i hi Ψ hsR c C
  · intro Ω hΩc hΩ
    apply funext
    apply FanProducts.factorFan_unique i hi Ψ hsR Ω hΩc
    intro C
    rw [← eqv.symm.map_mem C, hΩ, FanEquiv.symm_realEquiv]
    constructor
    · rintro ⟨D, hD, heq⟩
      refine ⟨D, hD, ?_⟩
      change C.map e.symm.toLinearMap = (FanProducts.conePi D).map e.symm.toLinearMap at heq
      have hh := congrArg (fun F => F.map e.toLinearMap) heq
      simpa only [FanTransport.map_inverse_rev] using hh
    · rintro ⟨D, hD, rfl⟩
      exact ⟨D, hD, rfl⟩

end Construction

/-- Proposition 4.1, canonical integral-component clause. The index set is
rigorously identified with the components of the literal line matroid; every
factor is an actual complete fan with precisely the original component rays.
No simpliciality, projectivity, chosen splitting or adapted basis is assumed. -/
theorem proposition_4_1 (U : Set (Lattice n)) [Fintype U]
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hpos : PointedCone.hull ℝ (embed '' U) = ⊤)
    (hnz : ∀ u : U, embed u.val ≠ 0)
    (Φ : Fan (standardEmbedding n)) (hc : Φ.IsComplete)
    (hr : AllowedBlocks.HasRays (standardEmbedding n) (fun u : U => u.val) Φ) :
    Nonempty (CanonicalProduct U Φ) := by
  have hspan : Submodule.span ℝ (embed '' U) = ⊤ := by
    have h := RayHyperplanes.span_range_eq_top_of_positive (fun u : U => embed u.val)
      (by simpa only [← Set.image_eq_range] using hpos)
    simpa only [← Set.image_eq_range] using h
  obtain ⟨b, hb, _⟩ := LatticeHull.exists_lattice_basis_extension U hU hspan
    (fun i : Fin 0 => (Fin.elim0 i : U)) (linearIndependent_empty_type)
  exact canonicalProduct_of_basis b hb hnz Φ hc hr

end Unimodular.ComponentProducts

#print axioms Unimodular.ComponentProducts.factor_vector_eq_decomposition
#print axioms Unimodular.ComponentProducts.canonicalProduct_of_basis
#print axioms Unimodular.ComponentProducts.proposition_4_1
#check "UNIMODULAR_CANONICAL_PRODUCT_DECOMPOSITION_EOF_V3"
