module

public import Papers.GraphicalZonotopes.ThreeTreeLatticeCoefficients
public import Papers.GraphicalZonotopes.ConditionalQuadratic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- Integer lower-support values give integer elemental slacks in every context. -/
theorem integer_delta {V : Type*} [Fintype V] [DecidableEq V]
    {z : SetFunction V} (hz : IntegerValued z) (u v : V) (S : Finset V) :
    ∃ k : ℤ, delta z u v S = (k : ℝ) := by
  obtain ⟨a,ha⟩ := hz (insert u (insert v S))
  obtain ⟨b,hb⟩ := hz S
  obtain ⟨c,hc⟩ := hz (insert u S)
  obtain ⟨d,hd⟩ := hz (insert v S)
  refine ⟨a+b-c-d,?_⟩
  simp only [delta,ha,hb,hc,hd,Int.cast_add,Int.cast_sub]
  ring

theorem integer_between_zero_one {x : ℝ} (hx : ∃ k : ℤ,x=(k : ℝ))
    (h0 : 0≤x) (h1 : x≤1) : x=0 ∨ x=1 := by
  obtain ⟨k,rfl⟩ := hx
  have hk0 : (0 : ℤ)≤k := by exact_mod_cast h0
  have hk1 : k≤(1 : ℤ) := by exact_mod_cast h1
  have hk : k=0 ∨ k=1 := by omega
  rcases hk with rfl | rfl <;> norm_num

/-- Exact coefficient data extracted from the actual polytope hypotheses of
Theorem 9.5. These are proved conclusions, not assumptions added to that theorem. -/
structure CoefficientModel {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Set (Fin n → ℝ)) where
  function : SetFunction (Fin n)
  extreme : ExtremeSupermodular function
  integer : IntegerValued (mobius function)
  supported : CliqueSupported G (mobius function)
  boolean : ∀ u v : Fin n,u≠v → ∀ S : Finset (Fin n),u∉S → v∉S →
    delta (zeta (mobius function)) u v S=0 ∨ delta (zeta (mobius function)) u v S=1
  nonempty : (family (mobius function)).Nonempty
  connected : (tetrahedronGraph (family (mobius function))).Preconnected
  covers : (family (mobius function)).biUnion id=univ
  directions : actualDirectionGraph Q=edgeGraph (mobius function)

/-- Unit dilation forces every integral elemental slack to be Boolean. The
proof retains the given ambient graph, all vertices, and the original translation. -/
theorem coefficient_model {n : ℕ} (hn : 4≤n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
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
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
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
theorem coefficient_model_polytopal {n : ℕ} (hn : 4≤n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hnz,hsz,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hnz,hsz,hbody⟩
  exact coefficient_model hn hG hQ ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd
    ⟨R,hR,hcR,hnR,he⟩

end UnitLatticeGeometry
end GraphicalZonotopes
