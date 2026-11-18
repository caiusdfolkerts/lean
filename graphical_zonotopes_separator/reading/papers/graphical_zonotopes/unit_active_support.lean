module

public import Papers.GraphicalZonotopes.UnitLatticeGeometry
public import Papers.GraphicalZonotopes.UnitFamilyStructure
public import Papers.GraphicalZonotopes.FourPartGraphRecognition
public import Papers.GraphicalZonotopes.PartialThreeTreeSupport
public import Papers.GraphicalZonotopes.SupportDimensionBound

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise BigOperators
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents FourPartGraphRecognition

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The unit-summand geometry does not need ambient full dimension. In every
actual dimension at least three it produces the Cartesian tetrahedral family
on exactly the active coordinates. -/
theorem active_coefficient_model {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {Q : Set (V → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q))
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ (z : SetFunction V) (A : Fin 4 → Finset V),
      ExtremeSupermodular z ∧
      (∀ i, (A i).card = 1 ∨ (A i).card = 2) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      ProductFamily (family (mobius z)) A ∧
      actualDirectionGraph Q = unionGraph (family (mobius z)) ∧
      DependsOn z ((family (mobius z)).biUnion id) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) =
        Module.finrank ℝ (vectorSpan ℝ Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q + R = (1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ) ≤ 1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) =
      Module.finrank ℝ (vectorSpan ℝ Q) := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
  have hdim3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) := by
    rw [hdim]
    exact hd
  have hne : z ≠ 0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim3
    have hspan : vectorSpan ℝ ({0} : Set (V → ℝ)) =
        (⊥ : Submodule ℝ (V → ℝ)) := _root_.vectorSpan_singleton ℝ (0 : V → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim3
    omega
  have hgp : IsGeneralizedPermutahedron Q := ⟨f,hfn,hfs,hbody⟩
  have hic : MinkowskiIndecomposable Q :=
    (minkowskiIndecomposable_iff_polytopal hgp).mpr hi
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hactual,hdep⟩ :=
    refined_support_of_dimension_ge_three hG hext hzg hdim3
  have hsupported : CliqueSupported G (mobius z) :=
    (mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩
  have hboolean : ∀ u v : V, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
      delta (zeta (mobius z)) u v S = 0 ∨ delta (zeta (mobius z)) u v S = 1 := by
    intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  have hmem : ∀ D, D ∈ family (mobius z) ↔ D.card = 4 ∧ mobius z D ≠ 0 :=
    mem_family _
  obtain ⟨hthin,hsquare⟩ := UnitFamilyStructure.structure_of_boolean
    hG hsupported hboolean hmem
  obtain ⟨A,hsize,hdis,hprod⟩ := FourPartCompletion.cartesian_completion
    (family (mobius z)) (fun D hD => ((hmem D).mp hD).1) hF hconn hthin hsquare
  refine ⟨z,A,hext,hsize,hdis,hprod,?_,hdep,hdim⟩
  rw [actualDirectionGraph_normalize,← hbody] at hactual
  exact hactual

end UnitLatticeGeometry
end GraphicalZonotopes
