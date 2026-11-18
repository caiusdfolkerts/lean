module

public import Recovery.Unimodular.ProductOriginalComponents
public import Recovery.Unimodular.ProductDecomposition

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set TauCeti.Toric
open scoped BigOperators

namespace Unimodular.OriginalComponents

open ComponentLattice LatticeCoordinates

variable {n : ℕ} {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {ι : N →+ V}

attribute [local instance] Classical.propDecidable

noncomputable instance imageSystemFintype (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) [Fintype U] : Fintype (ImageSystem b U) :=
  Fintype.ofEquiv U (imageLabelEquiv b U)

def originalLabel (b : Module.Basis (Fin n) ℤ N) (U : Set N) (u : U) :
    Components (ImageSystem b U) :=
  MatroidComponents.component (represented (ImageSystem b U)) (imageLabelEquiv b U u)

theorem mem_originalPart_iff (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) (u : U) :
    u.val ∈ originalPart hι b U hnz c ↔ originalLabel b U u = c := by
  constructor
  · rintro ⟨v, hv, hvu⟩
    have he : v = u := Subtype.ext hvu
    subst v
    apply (originalLineIndex hι b U hnz).injective
    rw [originalLabel, originalLineIndex_apply]
    exact hv
  · intro hu
    refine ⟨u, ?_, rfl⟩
    rw [← hu]
    exact (originalLineIndex_apply hι b U hnz u).symm

theorem originalPart_subset (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :
    originalPart hι b U hnz c ⊆ U := by
  rintro _ ⟨u, _, rfl⟩
  exact u.property

theorem originalPart_iUnion (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) :
    (⋃ c, originalPart hι b U hnz c) = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    exact originalPart_subset hι b U hnz c hc
  · intro hx
    exact Set.mem_iUnion.mpr ⟨originalLabel b U ⟨x, hx⟩,
      (mem_originalPart_iff hι b U hnz _ ⟨x, hx⟩).mpr rfl⟩

theorem originalParts_pairwise_disjoint (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) :
    Pairwise (fun c d => Disjoint (originalPart hι b U hnz c) (originalPart hι b U hnz d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hc hd
  let u : U := ⟨x, originalPart_subset hι b U hnz c hc⟩
  have huc := (mem_originalPart_iff hι b U hnz c u).mp hc
  have hud := (mem_originalPart_iff hι b U hnz d u).mp hd
  exact hcd (huc.symm.trans hud)

abbrev OriginalLattice (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :=
  Submodule.span ℤ (originalPart hι b U hnz c)

abbrev OriginalSpace (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U)) :=
  Submodule.span ℝ (ι '' originalPart hι b U hnz c)

def originalFactorVector (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0) (c : Components (ImageSystem b U))
    (u : {u : U // originalLabel b U u = c}) : OriginalLattice hι b U hnz c :=
  ⟨u.val.val, Submodule.subset_span ((mem_originalPart_iff hι b U hnz c u.val).mpr u.property)⟩

theorem originalFactorVector_range (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) (hnz : ∀ u : U, ι u.val ≠ 0)
    (c : Components (ImageSystem b U)) :
    Set.range (fun u => (originalFactorVector hι b U hnz c u : N)) =
      originalPart hι b U hnz c := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact (mem_originalPart_iff hι b U hnz c u.val).mpr u.property
  · intro hx
    let u : U := ⟨x, originalPart_subset hι b U hnz c hx⟩
    exact ⟨⟨u, (mem_originalPart_iff hι b U hnz c u).mp hx⟩, rfl⟩

/-- A splitting by the literal integer and real spans of the original
line-matroid components. The inverse maps are the canonical sums of inclusions. -/
structure OriginalSplitting (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) [Fintype U] (hnz : ∀ u : U, ι u.val ≠ 0) where
  integral : N ≃ₗ[ℤ] (∀ c : Components (ImageSystem b U), OriginalLattice hι b U hnz c)
  real : V ≃ₗ[ℝ] (∀ c : Components (ImageSystem b U), OriginalSpace hι b U hnz c)
  integral_sum : ∀ x, integral.symm x = ∑ c, (x c : N)
  real_sum : ∀ x, real.symm x = ∑ c, (x c : V)
  compatible : ∀ x, real (ι x) = fun c => originalEmbedding hι b U hnz c (integral x c)
  lattice : ∀ c, IsIntegralLattice (originalEmbedding hι b U hnz c)

def splittingOfData (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) [Fintype U] (hnz : ∀ u : U, ι u.val ≠ 0)
    (fi : Lattice n ≃ₗ[ℤ] (∀ c, latticeSpan (ImageSystem b U) c))
    (fr : Ambient n ≃ₗ[ℝ] (∀ c, realSpan (ImageSystem b U) c))
    (hfi : ∀ x, fi.symm x = ∑ c, (x c : Lattice n))
    (hfr : ∀ x, fr.symm x = ∑ c, (x c : Ambient n))
    (hcompat : ∀ x, fr (embed x) = fun c => componentEmbedding (ImageSystem b U) c (fi x c))
    (hlattice : ∀ c, IsIntegralLattice (componentEmbedding (ImageSystem b U) c)) :
    OriginalSplitting hι b U hnz := by
  classical
  let ei := LinearEquiv.piCongrRight (factorIntegralEquiv hι b U hnz)
  let er := LinearEquiv.piCongrRight (factorRealEquiv hι b U hnz)
  let f := (latticeEquiv b).trans (fi.trans ei.symm)
  let g := (realEquiv hι b).trans (fr.trans er.symm)
  refine {
    integral := f
    real := g
    integral_sum := ?_
    real_sum := ?_
    compatible := ?_
    lattice := fun c => originalFactor_isIntegralLattice hι b U hnz c (hlattice c)
  }
  · intro x
    apply (latticeEquiv b).injective
    change latticeEquiv b ((latticeEquiv b).symm (fi.symm (ei x))) =
      latticeEquiv b (∑ c, (x c : N))
    rw [LinearEquiv.apply_symm_apply, hfi, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    exact factorIntegralEquiv_coe hι b U hnz c (x c)
  · intro x
    apply (realEquiv hι b).injective
    change realEquiv hι b ((realEquiv hι b).symm (fr.symm (er x))) =
      realEquiv hι b (∑ c, (x c : V))
    rw [LinearEquiv.apply_symm_apply, hfr, map_sum]
    apply Finset.sum_congr rfl
    intro c _
    exact factorRealEquiv_coe hι b U hnz c (x c)
  · intro x
    apply er.injective
    change er (er.symm (fr (realEquiv hι b (ι x)))) =
      er (fun c => originalEmbedding hι b U hnz c (f x c))
    rw [LinearEquiv.apply_symm_apply]
    funext c
    change fr (realEquiv hι b (ι x)) c =
      factorRealEquiv hι b U hnz c (originalEmbedding hι b U hnz c
        ((factorIntegralEquiv hι b U hnz c).symm (fi (latticeEquiv b x) c)))
    rw [coordinates_commute]
    change fr (embed (latticeEquiv b x)) c = _
    rw [congrFun (hcompat (latticeEquiv b x)) c, factorEquivs_compatible,
      LinearEquiv.apply_symm_apply]

def splittingOfCoordinates (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
    (U : Set N) [Fintype U] (hnz : ∀ u : U, ι u.val ≠ 0) (Φ : Fan ι)
    (P : ComponentProducts.CanonicalProduct (ImageSystem b U) (coordinateFan hι b Φ)) :
    OriginalSplitting hι b U hnz :=
  splittingOfData hι b U hnz P.integral P.real P.integral_sum P.real_sum P.compatible
    (fun c => (P.factor c).lattice)

/-- The canonical integral splitting exists for the ray system itself,
without assuming the existence of any fan. -/
theorem uniform_original_splitting (hι : IsIntegralLattice ι)
    (b : Module.Basis (Fin n) ℤ N) (U : Set N) [Fintype U]
    (hnz : ∀ u : U, ι u.val ≠ 0)
    (hU : IntegralRigidity.Uniform b (fun u : U => u.val))
    (hpos : PointedCone.hull ℝ (ι '' U) = ⊤) :
    Nonempty (OriginalSplitting hι b U hnz) := by
  classical
  let U₀ := ImageSystem b U
  have hU₀ : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U₀ => u.val) :=
    (uniform_image_iff b U).mpr hU
  have hpos₀ : PointedCone.hull ℝ (embed '' U₀) = ⊤ :=
    (hull_top_coordinates_iff hι b U).mpr hpos
  have hspan : Submodule.span ℝ (embed '' U₀) = ⊤ := by
    have h := RayHyperplanes.span_range_eq_top_of_positive (fun u : U₀ => embed u.val)
      (by simpa only [← Set.image_eq_range] using hpos₀)
    simpa only [← Set.image_eq_range] using h
  obtain ⟨B, hB, _⟩ := LatticeHull.exists_lattice_basis_extension U₀ hU₀ hspan
    (fun i : Fin 0 => (Fin.elim0 i : U₀)) (linearIndependent_empty_type)
  exact ⟨splittingOfData hι b U hnz (integralDecomposition B hB) (realDecomposition B hB)
    (integralAssembly_apply B hB) (realAssembly_apply B hB)
    (decomposition_compatible B hB) (component_isIntegralLattice B hB)⟩

namespace OriginalSplitting

variable (hι : IsIntegralLattice ι) (b : Module.Basis (Fin n) ℤ N)
  (U : Set N) [Fintype U] (hnz : ∀ u : U, ι u.val ≠ 0)
  (s : OriginalSplitting hι b U hnz)

theorem integral_of_mem (c : Components (ImageSystem b U))
    (x : OriginalLattice hι b U hnz c) : s.integral x.val = Pi.single c x := by
  classical
  apply s.integral.symm.injective
  rw [LinearEquiv.symm_apply_apply, s.integral_sum]
  symm
  rw [Finset.sum_eq_single c]
  · simp only [Pi.single_eq_same]
  · intro d _ hdc
    rw [Pi.single_eq_of_ne hdc]
    rfl
  · intro hc
    exact (hc (Finset.mem_univ c)).elim

theorem real_of_mem (c : Components (ImageSystem b U))
    (x : OriginalSpace hι b U hnz c) : s.real x.val = Pi.single c x := by
  classical
  apply s.real.symm.injective
  rw [LinearEquiv.symm_apply_apply, s.real_sum]
  symm
  rw [Finset.sum_eq_single c]
  · simp only [Pi.single_eq_same]
  · intro d _ hdc
    rw [Pi.single_eq_of_ne hdc]
    rfl
  · intro hc
    exact (hc (Finset.mem_univ c)).elim

theorem factor_vector_eq (c : Components (ImageSystem b U))
    (u : {u : U // originalLabel b U u = c}) :
    s.integral u.val.val c = originalFactorVector hι b U hnz c u := by
  classical
  have h := congrFun (s.integral_of_mem hι b U hnz c (originalFactorVector hι b U hnz c u)) c
  simpa only [Pi.single_eq_same, originalFactorVector] using h

end OriginalSplitting
end Unimodular.OriginalComponents

#print axioms Unimodular.OriginalComponents.originalPart_iUnion
#print axioms Unimodular.OriginalComponents.originalParts_pairwise_disjoint
#print axioms Unimodular.OriginalComponents.originalFactorVector_range
#print axioms Unimodular.OriginalComponents.splittingOfCoordinates
#print axioms Unimodular.OriginalComponents.uniform_original_splitting
#print axioms Unimodular.OriginalComponents.OriginalSplitting.real_of_mem
#print axioms Unimodular.OriginalComponents.OriginalSplitting.factor_vector_eq
#check "UNIMODULAR_ORIGINAL_SPLITTING_EOF_V1"
