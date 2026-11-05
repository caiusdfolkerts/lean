module

public import Papers.GraphicalZonotopes.SaturatedGeneralBlocks
public import Papers.GraphicalZonotopes.BookIntervalArithmetic

/-! # Exact spoke counts in the saturated matching construction

The proper blocks avoiding a selected hub are exactly the response blocks on
the other hubs.  This identifies the missing spokes with their total dimension.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

theorem nonneighbor_count (hs : 5 ≤ s) (a : Fin s) :
    (univ.filter (fun j : ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s) =>
      a ∉ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)).card + 1 =
      cliqueCapacity (s - 1) := by
  classical
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_sum_type]
  simp only [scopedAnchorScope,mem_univ,not_true_eq_false,ite_false,sum_const_zero,zero_add]
  rw [Fintype.sum_sigma]
  have hc : ∀ C : BookBlock (Fin s),
      (∑ j : Fin (pureRank s C),if a ∉ C.1 then (1 : ℕ) else 0) =
        if a ∉ C.1 then C.1.card.choose 2 - 1 else 0 := by
    intro C
    by_cases ha : a ∈ C.1
    · simp only [ha,not_true_eq_false,ite_false,sum_const_zero]
    · have hCu : C.1 ≠ univ := by
        intro he
        apply ha
        rw [he]
        exact mem_univ a
      simp only [ha,not_false_eq_true,ite_true,sum_const,card_univ,Fintype.card_fin,
        smul_eq_mul,mul_one,pureRank,if_neg hCu]
  simp_rw [hc]
  rw [sum_coe_sort (largeBlocks (univ : Finset (Fin s)))
    (fun C => if a ∉ C then C.card.choose 2 - 1 else 0)]
  rw [← sum_filter]
  have hfilter : (largeBlocks (univ : Finset (Fin s))).filter (fun C => a ∉ C) =
      largeBlocks (univ.erase a) := by
    ext C
    simp only [mem_filter,mem_largeBlocks,subset_erase]
    tauto
  rw [hfilter,largeBlocks_dimension_sum,← cliqueCapacity_eq_dimension_sum,
    card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fin]

theorem neighbor_count (hs : 5 ≤ s) (a : Fin s) :
    (univ.filter (fun j : ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s) =>
      a ∈ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)).card =
        saturatedHubNeighbors s := by
  classical
  have hc := card_filter_add_card_filter_not
    (s := (univ : Finset (ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s))))
    (p := fun j => a ∈ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)
  rw [card_univ,general_circuit_card hs] at hc
  have hn := nonneighbor_count hs a
  have hmono := cliqueCapacity_pred_le (show 1 ≤ s by omega)
  unfold saturatedHubNeighbors
  rw [if_neg (by omega : s ≠ 2)]
  omega

/-- For every number of hubs at least five, the matching circuit gives an
actual full-dimensional lattice polytope with exactly the optimal number of
active spokes at each hub. -/
theorem spoke_attainment (s : ℕ) (hs : 5 ≤ s) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  let hs3 : 3 ≤ s := by omega
  let a₀ : anchorSet hs3 := ⟨⟨1,by omega⟩,by
    simp only [anchorSet,mem_erase,mem_univ,and_true,bookZero]
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv⟩
  obtain ⟨f,hn,hi,he,hG,hd,hl,hcount⟩ := scoped_book_of_anchor_circuit
    (anchorSet hs3) (eta s) (anchorFamily hs3) (anchorFamily_response hs3)
    (anchorWeights hs3) (2*s : ℕ) (pureRank s) (pureBlock hs) hs3
    (anchorFamily_boolean hs3) (anchorFamily_essential hs3) a₀
    (anchorWeights_positive hs3) (general_scale_rigidity hs) (general_circuit_card hs)
  exact ⟨f,hn,hi,he,hG,hd,hl,fun a => (hcount a).trans (neighbor_count hs a)⟩

end GraphicalZonotopes.BooleanModule.Saturated
