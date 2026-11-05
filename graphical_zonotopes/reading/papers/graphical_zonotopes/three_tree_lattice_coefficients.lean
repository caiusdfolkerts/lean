module

public import Papers.GraphicalZonotopes.ThreeTreeNonzero
public import Papers.GraphicalZonotopes.LatticeCoefficients
public import Papers.GraphicalZonotopes.Translation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A genuine compact convex summand yields the full lower-support data and
all fixed-dilation inequalities, with no assumed generalized-permutahedron
presentation of the summand. -/
theorem actual_summand_lowerSupport {Q R : Set (V → ℝ)} {G : SimpleGraph V}
    (hQ : IsCompact Q) (hcQ : Convex ℝ Q) (hnQ : Q.Nonempty)
    (hR : IsCompact R) (hcR : Convex ℝ R) (hnR : R.Nonempty)
    {a : ℝ} (ha : 0≤a) (he : Q+R=a • graphicalZonotope G) :
    Normalized (lowerSupport Q) ∧ Supermodular (lowerSupport Q) ∧
      Q=basePolytope (lowerSupport Q) ∧ Graphical G (lowerSupport Q) ∧
      ∀ u v,u≠v → G.Adj u v → ∀ S,u∉S → v∉S →
        delta (lowerSupport Q) u v S≤a := by
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul ha
  have hbase : Q+R=basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha,
      baseGraphFunction_eq_graphicalZonotope]
    exact he
  have hn := lowerSupport_normalized hQ hnQ
  have hs := summand_lowerSupport_supermodular hTn hTs hQ hR hnQ hnR hbase
  have hbody := summand_eq_basePolytope hTn hTs hQ hR hcQ hnQ hnR hbase
  have hsum : IsMinkowskiSummand (basePolytope (lowerSupport Q))
      (a • graphicalZonotope G) := by
    rw [← hbody]
    exact ⟨R,hR,hcR,hnR,he⟩
  have hrows := (isMinkowskiSummand_graphical_iff hn hs ha).mp hsum
  exact ⟨hn,hs,hbody,hrows⟩

/-- The nonzero integer-coefficient assertion in Theorem9.1, for arbitrary
actual lattice summands and every tetrahedron of the given 3-tree. This is an
intermediate theorem; the sharp edgewise dilation bound is a further obligation. -/
theorem threeTree_lattice_four_coefficients {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0<a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    ∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : normalize f≠0 := by
    intro he
    rw [he,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular (normalize f) := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  have hnormgraph : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hall := (threeTree_all_tetrahedra_nonzero hn hG hext hnormgraph hdim).2
  have hint := (hQ.lowerSupport_integerValued hi.1).mobius
  intro C hC
  obtain ⟨k,hk⟩ := hint C
  refine ⟨k,?_,hk⟩
  intro hzero
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  have hnonzero := hall C hC
  rw [mobius_four_normalize hc] at hnonzero
  exact hnonzero (by simpa [hzero] using hk)

end GraphicalZonotopes
