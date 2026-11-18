module

public import Recovery.Unimodular.ProductOriginalSplitting
public import Recovery.Unimodular.ProductGeometric

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set TauCeti.Toric
open scoped BigOperators

namespace Unimodular.OriginalComponentProducts

open ComponentLattice LatticeCoordinates OriginalComponents

variable {n : ℕ} {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : N →+ V}

attribute [local instance] Classical.propDecidable

/-- The basis parameter in the theorem is a coordinate choice available for
every genuine integral lattice, rather than an additional existence premise. -/
theorem lattice_basis_exists (hι : IsIntegralLattice ι) :
    ∃ m : ℕ, Nonempty (Module.Basis (Fin m) ℤ N) := by
  letI : Module.Free ℤ N := hι.free
  letI : Module.Finite ℤ N := hι.finite
  exact ⟨Module.finrank ℤ N, ⟨Module.finBasis ℤ N⟩⟩

theorem uniform_basis_iff (b c : Module.Basis (Fin n) ℤ N) (U : Set N) :
    IntegralRigidity.Uniform b (fun u : U => u.val) ↔
      IntegralRigidity.Uniform c (fun u : U => u.val) :=
  (IntegralRigidity.uniform_iff_independent_spans b _).trans
    (IntegralRigidity.uniform_iff_independent_spans c _).symm

/-- Reindexing by the proved component equivalence gives precisely the
intrinsic fibers of the original line matroid. This explicitly justifies the
phrase 'indexed by those components' and removes any dependence on coordinates
from the meaning of the factor sublattices. -/
theorem originalPart_canonical (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (d : OriginalLineComponents ι U) :
    originalPart hι b U hnz ((originalLineIndex hι b U hnz).symm d) =
      Subtype.val '' {u : U |
        MatroidComponents.component (LineMatroid.matroid (K := ℝ) (fun u : U => ι u.val))
          (LineMatroid.projection (K := ℝ) (fun u : U => ι u.val) u) = d} := by
  simp only [originalPart, Equiv.apply_symm_apply]

/-- The full canonical product lives in the original lattice and real space.
Each factor lattice is the integer span of the original vectors whose literal
line lies in one connected component; each real factor is their actual real
span. The component index is identified with the original line matroid by
`OriginalComponents.originalLineIndex`. -/
structure CanonicalProduct (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) [Fintype U] (hnz : ∀ u : U, ι u.val ≠ 0) (Φ : Fan ι)
    extends OriginalSplitting hι b U hnz where
  factor : ∀ c : Components (ImageSystem b U), Fan (originalEmbedding hι b U hnz c)
  complete : ∀ c, (factor c).IsComplete
  rays : ∀ c, AllowedBlocks.HasRays (originalEmbedding hι b U hnz c)
    (originalFactorVector hι b U hnz c) (factor c)
  allCones : ∀ C : PointedCone ℝ V, C ∈ Φ.cones ↔
    ∃ D : ∀ c, PointedCone ℝ (OriginalSpace hι b U hnz c),
      (∀ c, D c ∈ (factor c).cones) ∧
      C = (FanProducts.conePi D).map (real.symm : _ →ₗ[ℝ] _)
  summandCones : ∀ c (C : PointedCone ℝ (OriginalSpace hι b U hnz c)),
    C.map (OriginalSpace hι b U hnz c).subtype ∈ Φ.cones ↔ C ∈ (factor c).cones
  unique : ∀ Ω : ∀ c, Fan (originalEmbedding hι b U hnz c),
    (∀ c, (Ω c).IsComplete) →
    (∀ C : PointedCone ℝ V, C ∈ Φ.cones ↔
      ∃ D : ∀ c, PointedCone ℝ (OriginalSpace hι b U hnz c),
        (∀ c, D c ∈ (Ω c).cones) ∧
        C = (FanProducts.conePi D).map (real.symm : _ →ₗ[ℝ] _)) → factor = Ω

/-- Geometric construction from a genuine intrinsic splitting. The final
theorem below derives the splitting from uniform unimodularity. -/
theorem canonicalProduct_of_splitting (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) [Fintype U]
    (hnz : ∀ u : U, ι u.val ≠ 0) (Φ : Fan ι) (hc : Φ.IsComplete)
    (hr : AllowedBlocks.HasRays ι (fun u : U => u.val) Φ)
    (s : OriginalSplitting hι b U hnz) : Nonempty (CanonicalProduct hι b U hnz Φ) := by
  classical
  letI : FiniteDimensional ℝ V := hι.finiteDimensional
  let f := s.integral
  let e := s.real
  let i := originalEmbedding hι b U hnz
  have hi : ∀ c, IsIntegralLattice (i c) := s.lattice
  have hfe : ∀ x, e (ι x) = (FanProducts.piEmbedding i) (f x) := s.compatible
  let Ψ := FanTransport.transport f.toAddEquiv e hfe Φ
  let eqv := FanTransport.equivalence f.toAddEquiv e hfe Φ
  have hΨc : Ψ.IsComplete := (FanTransport.transport_complete_iff _ _ _ _).mpr hc
  have hΨr : AllowedBlocks.HasRays (FanProducts.piEmbedding i)
      (fun u : U => f u.val) Ψ :=
    FanTransport.hasRays_of_equiv eqv (fun u => hfe u.val) hr
  let label := originalLabel b U
  have hs : ∀ u : U, ∀ d : Components (ImageSystem b U), d ≠ label u → i d (f u.val d) = 0 := by
    intro u d hd
    let x : OriginalLattice hι b U hnz (label u) :=
      ⟨u.val, Submodule.subset_span ((mem_originalPart_iff hι b U hnz _ u).mpr rfl)⟩
    have hz := congrFun (s.integral_of_mem hι b U hnz (label u) x) d
    rw [Pi.single_eq_of_ne hd] at hz
    change s.integral u.val d = 0 at hz
    change i d (s.integral u.val d) = 0
    rw [hz, map_zero]
  have hnz' : ∀ u : U, (FanProducts.piEmbedding i) (f u.val) ≠ 0 := by
    intro u hu
    apply hnz u
    apply e.injective
    change e (ι u.val) = e 0
    rw [hfe, hu, map_zero]
  obtain ⟨factors, hcomplete, hrays, hprod, hsummand, hunique⟩ :=
    FanProducts.proposition_4_1_exact_rays i hi (fun u : U => f u.val) label
      Ψ hΨc hΨr hnz' hs
  have hfacr : ∀ c, AllowedBlocks.HasRays (i c) (originalFactorVector hι b U hnz c)
      (factors c) := by
    intro c
    have h := hrays c
    have hf : (fun u : {u : U // label u = c} => f u.val.val c) =
        originalFactorVector hι b U hnz c := by
      funext u
      exact s.factor_vector_eq hι b U hnz c u
    rw [hf] at h
    exact h
  have horig : ∀ C : PointedCone ℝ V, C ∈ Φ.cones ↔
      ∃ D : ∀ c, PointedCone ℝ (OriginalSpace hι b U hnz c),
        (∀ c, D c ∈ (factors c).cones) ∧
        C = (FanProducts.conePi D).map e.symm.toLinearMap := by
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
    toOriginalSplitting := s
    factor := factors
    complete := hcomplete
    rays := hfacr
    allCones := horig
    summandCones := ?_
    unique := ?_
  }⟩
  · intro c C
    have hmap : (C.map (OriginalSpace hι b U hnz c).subtype).map e.toLinearMap =
        C.map (LinearMap.single ℝ (fun c => OriginalSpace hι b U hnz c) c) := by
      rw [PointedCone.map_map]
      congr 1
      apply LinearMap.ext
      intro x
      exact s.real_of_mem hι b U hnz c x
    rw [← eqv.map_mem (C.map (OriginalSpace hι b U hnz c).subtype)]
    change (C.map (OriginalSpace hι b U hnz c).subtype).map e.toLinearMap ∈ Ψ.cones ↔
      C ∈ (factors c).cones
    rw [hmap]
    exact hsummand c C
  · intro Ω hΩc hΩ
    apply hunique Ω hΩc
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

/-- Full Proposition 4.1, canonical clause, for an arbitrary integral lattice.
The hypothesis is the original maximal-minor unimodularity condition in an
arbitrary integral basis. No splitting, adapted basis, simpliciality or
projectivity is assumed. Both factors and all cone equalities live in the
literal original lattice and its real space. -/
theorem proposition_4_1 (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) [Fintype U]
    (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hpos : PointedCone.hull ℝ (ι '' U) = ⊤)
    (hnz : ∀ u : U, ι u.val ≠ 0)
    (Φ : Fan ι) (hc : Φ.IsComplete)
    (hr : AllowedBlocks.HasRays ι (fun u : U => u.val) Φ) :
    Nonempty (CanonicalProduct hι b U hnz Φ) := by
  obtain ⟨s⟩ := uniform_original_splitting hι b U hnz hU hpos
  exact canonicalProduct_of_splitting hι b U hnz Φ hc hr s

end Unimodular.OriginalComponentProducts

#print axioms Unimodular.OriginalComponentProducts.lattice_basis_exists
#print axioms Unimodular.OriginalComponentProducts.uniform_basis_iff
#print axioms Unimodular.OriginalComponentProducts.originalPart_canonical
#print axioms Unimodular.OriginalComponentProducts.canonicalProduct_of_splitting
#print axioms Unimodular.OriginalComponentProducts.proposition_4_1
#check "UNIMODULAR_ARBITRARY_LATTICE_PRODUCT_EOF_V1"
