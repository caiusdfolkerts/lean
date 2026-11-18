module

public import Papers.GraphicalZonotopes.Translation
public import Papers.GraphicalZonotopes.SupportDimensionBound

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every actual weak summand has its genuine normalized graphical support
function, preserving affine dimension. Points are handled explicitly rather
than excluded by an extra hypothesis. -/
theorem weak_summand_extreme_or_zero {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ z : graphicalFunctionSpace G,Supermodular z.1 ∧
      (z.1=0 ∨ ExtremeSupermodular z.1) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by
  obtain ⟨c,hc,R,hR,hRc,hnR,hQR⟩:=hw
  have hTn : Normalized (c • graphFunction G) := by
    change c*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs:=(graphFunction_supermodular G).smul hc.le
  have hbase : Q+R=basePolytope (c • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) hc.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f:=lowerSupport Q
  have hfn : Normalized f:=lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f:=summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f:=summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs hc.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon S hu hv
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,hfs.normalize,?_,?_⟩
  · by_cases hz:normalize f=0
    · exact Or.inl hz
    · exact Or.inr (MinkowskiIndecomposable.extremeSupermodular_normalize
        hfn hfs hz (hbody ▸ hi))
  · rw [vectorSpan_basePolytope_normalize,← hbody]

theorem weak_summand_dimension_le {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤Fintype.card V-1 := by
  obtain ⟨z,hz,he,hd⟩:=weak_summand_extreme_or_zero hQ hi hw
  rw [hd]
  simpa only [card_univ] using finrank_vectorSpan_le_support z.2.1 hz
    (show DependsOn z.1 univ from fun T => by rw [inter_univ])

/-- Every actual witness contributes its real affine dimension to the
paper's maximum invariant; boundedness follows from ambient geometry. -/
theorem dimension_le_maximum {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤maximumIndecomposableDimension G := by
  apply le_csSup
  · refine ⟨Fintype.card V-1,?_⟩
    rintro d ⟨R,hR,hr,hs,hd⟩
    rw [← hd]
    exact weak_summand_dimension_le hR hr hs
  · exact ⟨Q,hQ,hi,hw,rfl⟩

theorem Graphical.mono_graph {G H : SimpleGraph V} {z : SetFunction V}
    (hHG : H≤G) (hz : Graphical H z) : Graphical G z := by
  intro u v huv hnon S hu hv
  exact hz u v huv (fun h => hnon (hHG h)) S hu hv

end GraphicalZonotopes
