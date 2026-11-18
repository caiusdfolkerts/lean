module

public import Papers.GraphicalZonotopes.TwoHubLiteral

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.TwoHub
open Finset
open scoped BigOperators Pointwise

theorem two_pow_gt_add_one (p : ℕ) (hp : 2 ≤ p) : p+1 < 2^p := by
  induction p,hp using Nat.le_induction with
  | base => decide
  | succ p hp ih =>
    rw [pow_succ]
    omega

/-- The exponential family has no spanning admissible 3-tree. The proof
uses the previously verified exact four-part spanning criterion, with every
part and every vertex retained. -/
theorem exponential_no_admissible_spanning (p : ℕ) (hp : 2 ≤ p) :
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by
  have hp1 : 1 ≤ p := by omega
  have hpb : p ≤ 2^p+p := Nat.le_add_left p (2^p)
  intro h
  have hbound := (FourPartSpanning.four_partite_spanning_iff (![1,1,p,2^p+p])
    (by intro i; fin_cases i <;> simp <;> omega)).mp h
  rw [part_sum,part_sup p (2^p+p) hp1 hpb] at hbound
  have hpow := two_pow_gt_add_one p hp
  omega

/-- Corollary 8.5, with a lattice witness and the paper's ordinary
polytopal notion of indecomposability. -/
theorem paper_corollary_8_5 (p : ℕ) (hp : 2 ≤ p) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i)) → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by
  have hp1 : 1 ≤ p := by omega
  obtain ⟨Q,hQ,hi,hd,R,hR,hnR,he⟩ := exponential_polytopal_summand p hp1
  refine ⟨⟨Q,hQ,hi,?_,?_⟩,exponential_no_admissible_spanning p hp⟩
  · unfold FullDimension
    rw [hd,twoSingleton_card]
    have hpow : 0 < (2 : ℕ)^p := by positivity
    omega
  · exact ⟨_,by positivity,R,hR.compact,hR.convex,hnR,he⟩

end GraphicalZonotopes.TwoHub
