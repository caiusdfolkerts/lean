module

public import Papers.GraphicalZonotopes.UnitLatticeGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeDilation
open Finset
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A lattice summand at any real dilation strictly below two is already a
summand of the unscaled graphical zonotope. This is a consequence of integral
support values, not an integrality hypothesis on the dilation parameter. -/
theorem unit_summand_of_lt_two {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : LatticePolytope Q) (hnQ : Q.Nonempty) {a : ℝ} (ha : 0<a) (ha2 : a<2)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    IsMinkowskiSummand Q (graphicalZonotope G) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hn,hs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hnQ hR hcR hnR ha.le he
  rw [hbody]
  have hsum1 : IsMinkowskiSummand (basePolytope (lowerSupport Q))
      ((1 : ℝ) • graphicalZonotope G) := by
    apply (isMinkowskiSummand_graphical_iff hn hs (by norm_num : (0 : ℝ)≤1)).mpr
    refine ⟨hgraph,?_⟩
    intro u v huv hadj S hu hv
    obtain ⟨k,hk⟩ := UnitLatticeGeometry.integer_delta (hQ.lowerSupport_integerValued hnQ) u v S
    have hklt : (k : ℝ)<2 := by rw [← hk];exact (hbound u v huv hadj S hu hv).trans_lt ha2
    have hklt' : k<(2 : ℤ) := by exact_mod_cast hklt
    rw [hk]
    exact_mod_cast (show k≤(1 : ℤ) by omega)
  simpa only [one_smul] using hsum1

/-- Every nontrivial full-dimensional lattice summand requires dilation at
least one, even when its complement and dilation parameter are arbitrary real. -/
theorem dilation_at_least_one {n : ℕ} (hn : 2≤n) {G : SimpleGraph (Fin n)}
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q) (hnQ : Q.Nonempty)
    (hd : FullDimension Q) {a : ℝ} (ha : 0<a)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) : 1≤a := by
  by_contra hn1
  have ha1 : a<1 := lt_of_not_ge hn1
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hnQ hR hcR hnR ha.le he
  let f := lowerSupport Q
  have hzero : ∀ u v : Fin n,u≠v → ∀ S : Finset (Fin n),u∉S → v∉S → delta f u v S=0 := by
    intro u v huv S hu hv
    by_cases hadj : G.Adj u v
    · obtain ⟨k,hk⟩ := UnitLatticeGeometry.integer_delta (hQ.lowerSupport_integerValued hnQ) u v S
      have hk0 : (0 : ℝ)≤k := by rw [← hk];exact hfs.elemental u v huv S hu hv
      have hk1 : (k : ℝ)<1 := by rw [← hk];exact (hbound u v huv hadj S hu hv).trans_lt ha1
      have hk0' : (0 : ℤ)≤k := by exact_mod_cast hk0
      have hk1' : k<(1 : ℤ) := by exact_mod_cast hk1
      have hkeq : k=0 := by omega
      simpa only [hkeq,Int.cast_zero] using hk
    · exact hgraph u v huv hadj S hu hv
  have hz : normalize f=0 := by
    apply normalized_zero_elemental_eq_zero (normalize_translationNormalized hfn)
    intro u v huv S hu hv
    rw [delta_normalize f huv hu hv]
    exact hzero u v huv S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  rw [hz,basePolytope_zero] at hdim
  have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
      (⊥ : Submodule ℝ (Fin n → ℝ)) :=
    _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
  rw [hspan,_root_.finrank_bot] at hdim
  omega

end UnitLatticeDilation
end GraphicalZonotopes
