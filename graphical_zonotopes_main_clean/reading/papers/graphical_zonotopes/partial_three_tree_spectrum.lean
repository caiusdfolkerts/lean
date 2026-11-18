module

public import Papers.GraphicalZonotopes.PartialThreeTreeSpectrumGraph

/-! # Dimension maxima and all intermediate dimensions in partial 3-trees

These are the mathematical assertions in Corollaries 6.7 and 6.8. The
algorithmic running-time assertion is not encoded by these theorems.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A simplex on any actual clique is a lattice indecomposable weak summand.
The affine dimension is the clique size minus one in the full ambient space. -/
theorem clique_simplex_witness {G : SimpleGraph V} {C : Finset V}
    (hC : 2 ≤ C.card) (hcl : G.IsClique C) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = C.card-1 := by
  let e₀ := (Fintype.equivFin C).symm
  let e : Fin (Fintype.card C) ↪ V := e₀.toEmbedding.trans
    ⟨Subtype.val,Subtype.val_injective⟩
  let f : SetFunction (Fin (Fintype.card C)) := setMonomial univ
  have hcard : 2 ≤ Fintype.card C := by simpa only [Fintype.card_coe] using hC
  have hf : ExtremeSupermodular f := setMonomial_extreme (by simpa only [card_univ,
    Fintype.card_fin] using hcard)
  have hfi : IntegerValued f := by
    intro S
    by_cases hs : (univ : Finset (Fin (Fintype.card C))) ⊆ S
    · exact ⟨1,by simp [f,setMonomial,hs]⟩
    · exact ⟨0,by simp [f,setMonomial,hs]⟩
  have hg : Graphical (G.comap e) f := by
    apply (setMonomial_graphical univ).mono_graph
    intro u v huv
    exact hcl (e₀ u).2 (e₀ v).2 (fun he => huv.1 (e.injective he))
  have hext : ExtremeSupermodular (extend e f) := extend_extreme e hf
  have hdim := complete_simplex_fullDimension hcard
  refine ⟨basePolytope (extend e f),(extend_integer e hfi).basePolytope hext.1.1 hext.2.1,
    hext.minkowskiIndecomposable,?_,?_⟩
  · exact (isWeakMinkowskiSummand_graphical_iff hext.1.1 hext.2.1).mpr (extend_graphical e hg)
  · rw [finrank_vectorSpan_extend e hf.1]
    simpa only [FullDimension,Fintype.card_fin,Fintype.card_coe] using hdim

theorem partial_threeTree_dimension_le_clique_count {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ maximumAdmissibleCliqueCount G+2 := by
  by_cases hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd
    have hF := ht.admissibleCliqueCollection hA (inducedOn_le G U)
    have hb := admissibleClique_count_le_maximum hF
    rw [ht.tetrahedra_card] at hb
    omega
  · omega

/-- The maximum admissible clique collection gives an actual lattice witness
for the supremum defining the dimension invariant. -/
theorem partial_threeTree_maximum_witness {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = maximumAdmissibleCliqueCount G+2 := by
  obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
  obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure hG
  obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
  exact ⟨Q,hQ,hi,hw,by omega⟩

theorem partial_threeTree_maximum_dimension {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact partial_threeTree_dimension_le_clique_count hG hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := partial_threeTree_maximum_witness hG hK
    rw [← hd]
    exact dimension_le_maximum hQ.finitePolytope hi hw

/-- Every positive integer through the sharp maximum occurs, with no gap and
with a lattice representative. The construction uses an arbitrary prefix of
a maximizing admissible three-tree and actual clique simplices at dimensions
one and two. -/
theorem partial_threeTree_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty)
    (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ maximumAdmissibleCliqueCount G+2) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hd3 : 3 ≤ d
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure hG
    obtain ⟨U,H,hU,hcardU,hH,htH⟩ := ht.prefix (m := d+1) (by omega) (by omega)
    have hHA : Admissible H := hA.mono hH
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_active_witness htH hHA
    refine ⟨basePolytope f,hfi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,?_⟩
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (hfg.mono_graph (hH.trans (inducedOn_le G _)))
    · omega
  · obtain ⟨C,hC⟩ := hK
    obtain ⟨hfour,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (s := C) (n := d+1) (by omega)
    obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
      (by omega : 2 ≤ D.card) (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q,hQ,hi,hw,by omega⟩

/-- Corollary 6.7's exact dimension and full positive spectrum. Algorithmic
complexity is a separate assertion and is not hidden in this statement. -/
theorem threeTree_dimension_and_spectrum {G : SimpleGraph V} (hG : IsThreeTree G) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 ∧
      ∀ d : ℕ,1 ≤ d → d ≤ maximumAdmissibleCliqueCount G+2 →
        ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  have hp : IsPartialThreeTree G := Or.inr ⟨G,hG,le_rfl⟩
  exact ⟨partial_threeTree_maximum_dimension hp hG.tetrahedra_nonempty,
    partial_threeTree_dimension_spectrum hp hG.tetrahedra_nonempty⟩

end GraphicalZonotopes
