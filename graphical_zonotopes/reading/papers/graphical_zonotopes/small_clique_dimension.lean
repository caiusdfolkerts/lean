module

public import Papers.GraphicalZonotopes.PartialThreeTreeSpectrum
public import Papers.GraphicalZonotopes.LocalDeltas

/-! # The low-dimensional cases of the partial-three-tree spectrum -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Triangle-free graphical cones have only segment rays. This uses the
complete nonnegative edge-coefficient decomposition, not a dimension premise. -/
theorem triangleFree_extreme_dimension_le_one {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hg : Graphical G z) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) ≤ 1 := by
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hzero : ∀ C : Finset V,C.card ≠ 2 → y C = 0 := by
    intro C hC
    apply coefficient_zero_of_not_clique hy C
    rintro ⟨hc,hcl⟩
    have hc3 : 3 ≤ C.card := by omega
    obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq hc3
    exact hG T ⟨fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv,hT⟩
  have hnonneg : ∀ C : Finset V,0 ≤ y C := by
    intro C
    by_cases hc : C.card = 2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
      have hh := hz.2.1.elemental u v huv ∅ (by simp) (by simp)
      rw [← zeta_mobius z,delta_zeta_empty _ huv] at hh
      exact hh
    · rw [hzero C hc]
  let p : Finset V → SetFunction V := fun C => y C • setMonomial C
  have hp : ∀ C,TranslationNormalized (p C) ∧ Supermodular (p C) := by
    intro C
    refine ⟨?_,(setMonomial_supermodular C).smul (hnonneg C)⟩
    by_cases hc : C.card = 2
    · have hn := setMonomial_translationNormalized (C := C) (by omega)
      exact ⟨by change y C*setMonomial C ∅=0; rw [hn.1,mul_zero],
        fun v => by change y C*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
    · simp only [p,hzero C hc,zero_smul]
      exact ⟨rfl,fun _ => rfl⟩
  have hsum : (∑ C,p C) = z := by
    rw [← zeta_mobius z,zeta_eq_sum_monomials]
  have hex : ∃ C,p C ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz.2.2.1 (hsum.symm.trans (sum_eq_zero (fun C _ => h C)))
  obtain ⟨C,hC⟩ := hex
  obtain ⟨a,ha,hscale⟩ := hz.finite_summand p (fun C => (hp C).1)
    (fun C => (hp C).2) hsum hC
  have hc : C.card = 2 := by
    by_contra hc
    exact hC (by simp only [p,hzero C hc,zero_smul])
  have hdep : DependsOn (p C) C := (setMonomial_dependsOn C).smul _
  rw [hscale] at hdep
  have hb := finrank_vectorSpan_le_support hz.1 hz.2.1
    (DependsOn.of_smul (ne_of_gt ha) hdep)
  simpa only [hc] using hb

theorem triangleFree_summand_dimension_le_one {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 1 := by
  obtain ⟨z,hzs,hze,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
  rw [hd]
  rcases hze with hz | hz
  · rw [hz,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot]
    omega
  · exact triangleFree_extreme_dimension_le_one hG hz z.2.2

theorem triangleFree_maximum_dimension {G : SimpleGraph V} (hG : G.CliqueFree 3)
    (hE : ∃ u v : V,G.Adj u v) : maximumIndecomposableDimension G = 1 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact triangleFree_summand_dimension_le_one hG hQ hi hw
  · obtain ⟨u,v,huv⟩ := hE
    have hcl : G.IsClique ({u,v} : Finset V) := by
      intro a ha b hb hab
      change a ∈ ({u,v} : Finset V) at ha
      change b ∈ ({u,v} : Finset V) at hb
      simp only [mem_insert,mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact huv
      · exact huv.symm
      · exact False.elim (hab rfl)
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness
      (by rw [card_pair huv.ne]) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,card_pair huv.ne] at hb
    exact hb

theorem edgeless_maximum_dimension {G : SimpleGraph V}
    (hG : ∀ u v : V,¬G.Adj u v) : maximumIndecomposableDimension G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  obtain ⟨z,hzs,hze,hqdim⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hz : z.1 = 0 := normalized_zero_elemental_eq_zero z.2.1
    (fun u v huv S hu hv => z.2.2 u v huv (hG u v) S hu hv)
  rw [hz,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hqdim
  omega

theorem partial_threeTree_no_tetrahedron_dimension_le_two {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : tetrahedra G = ∅)
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 2 := by
  by_contra hd
  have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by omega
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd3
  obtain ⟨C,hC⟩ := ht.tetrahedra_nonempty
  have hc := tetrahedra_mono (inducedOn_le G U) hC
  rw [hK] at hc
  exact notMem_empty C hc

theorem partial_threeTree_triangle_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : tetrahedra G = ∅)
    (hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T) :
    maximumIndecomposableDimension G = 2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact partial_threeTree_no_tetrahedron_dimension_le_two hG hK hQ hi hw
  · obtain ⟨T,hT,hcl⟩ := hT
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness (by omega) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,hT] at hb
    exact hb

/-- The complete piecewise dimension formula of Corollary 6.8. -/
def partialThreeTreeDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then maximumAdmissibleCliqueCount G+2
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0

theorem partial_threeTree_piecewise_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) :
    maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  unfold partialThreeTreeDimension
  by_cases hK : (tetrahedra G).Nonempty
  · rw [if_pos hK]
    exact partial_threeTree_maximum_dimension hG hK
  · rw [if_neg hK]
    have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [if_pos hT]
      exact partial_threeTree_triangle_maximum hG hKe hT
    · rw [if_neg hT]
      have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [if_pos hE]
        exact triangleFree_maximum_dimension hcf hE
      · rw [if_neg hE]
        exact edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)

/-- The full positive spectrum, including graphs with no tetrahedron. -/
theorem partial_threeTree_full_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ maximumIndecomposableDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hK : (tetrahedra G).Nonempty
  · apply partial_threeTree_dimension_spectrum hG hK d hd
    rwa [partial_threeTree_maximum_dimension hG hK] at hmax
  · have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [partial_threeTree_triangle_maximum hG hKe hT] at hmax
      obtain ⟨T,hT,hcl⟩ := hT
      obtain ⟨C,hCT,hC⟩ := exists_subset_card_eq (s := T) (n := d+1) (by omega)
      obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness (by omega : 2 ≤ C.card)
        (fun u hu v hv huv => hcl (hCT hu) (hCT hv) huv)
      exact ⟨Q,hQ,hi,hw,by omega⟩
    · have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [triangleFree_maximum_dimension hcf hE] at hmax
        have hd1 : d = 1 := by omega
        obtain ⟨u,v,huv⟩ := hE
        have hcl : G.IsClique ({u,v} : Finset V) := by
          intro a ha b hb hab
          change a ∈ ({u,v} : Finset V) at ha
          change b ∈ ({u,v} : Finset V) at hb
          simp only [mem_insert,mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact huv
          · exact huv.symm
          · exact False.elim (hab rfl)
        obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
          (by rw [card_pair huv.ne]) hcl
        refine ⟨Q,hQ,hi,hw,?_⟩
        simpa only [card_pair huv.ne,hd1] using hqdim
      · have hdim := edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)
        omega

end GraphicalZonotopes
