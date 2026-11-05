module

public import Papers.GraphicalZonotopes.UnitLatticeGeometry
public import Papers.GraphicalZonotopes.LatticeTranslation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- The unit-lattice coefficient model extends to arbitrary real translations.
Its Möbius coefficients and Boolean rows come from integral normalized support. -/
theorem coefficient_model_translated {n : ℕ} (hn : 4≤n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := hQ.integer_normalize_lowerSupport hi.1
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hcover,hactual⟩ := full_refined_support hn hG hext hzg hdim
  refine ⟨⟨z,hext,hzi.mobius,(mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩,
    ?_,hF,hconn,hcover,?_⟩⟩
  · intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  · rw [actualDirectionGraph_normalize,← hbody] at hactual
    exact hactual

/-- The ordinary polytope definition of indecomposability gives exactly the
same coefficient model; the necessary GP presentation is derived from the sum. -/
theorem coefficient_model_translated_polytopal {n : ℕ} (hn : 4≤n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hnz,hsz,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hnz,hsz,hbody⟩
  exact coefficient_model_translated hn hG hQ ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd
    ⟨R,hR,hcR,hnR,he⟩

end UnitLatticeGeometry
end GraphicalZonotopes
