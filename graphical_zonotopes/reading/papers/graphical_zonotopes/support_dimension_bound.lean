module

public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.SupportGeometry
public import Papers.GraphicalZonotopes.SeparatorLifts
public import Papers.GraphicalZonotopes.SeparatorTheorems

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing inactive coordinates gives the full support-sensitive affine
dimension bound, including the empty support. -/
theorem finrank_vectorSpan_le_support {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hdep : DependsOn z S) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))≤S.card-1 := by
  let W:=vectorSpan ℝ (basePolytope z)
  have hzero : ∀ (x : W) v,v∉S → x.1 v=0 := by
    intro x v hv
    exact vectorSpan_le_evaluation_ker_of_dependsOn hn hs hdep hv x.2
  by_cases hS : S.Nonempty
  · let r : W →ₗ[ℝ] (S → ℝ) := {
      toFun x v:=x.1 v.1
      map_add' _ _:=rfl
      map_smul' _ _:=rfl }
    have hr : ∀ x : W,r x∈(totalLinear (V:=S)).ker := by
      intro x
      change (∑ v : S,x.1 v.1)=0
      rw [Finset.sum_coe_sort]
      have htotal : (∑ v : V,x.1 v)=0 :=
        vectorSpan_basePolytope_le_total_ker (basePolytope_nonempty hn.1 hs) x.2
      rw [← htotal]
      exact sum_subset (subset_univ S) (fun v hv hvS => hzero x v hvS)
    let q:=r.codRestrict (totalLinear (V:=S)).ker hr
    have hq : Function.Injective q := by
      intro x y hxy
      apply Subtype.ext
      funext v
      by_cases hv : v∈S
      · exact congrArg (fun t : (totalLinear (V:=S)).ker => t.1 ⟨v,hv⟩) hxy
      · rw [hzero x v hv,hzero y v hv]
    have hb:=LinearMap.finrank_le_finrank_of_injective hq
    obtain ⟨v,hv⟩:=hS
    rw [finrank_total_ker_fintype (⟨v,hv⟩ : S),Fintype.card_coe] at hb
    exact hb
  · have hW : W=⊥ := by
      apply le_antisymm
      · intro x hx
        change x=0
        funext v
        exact hzero ⟨x,hx⟩ v (fun hv => hS ⟨v,hv⟩)
      · exact bot_le
    change Module.finrank ℝ W≤_
    rw [hW,finrank_bot]
    exact Nat.zero_le _

namespace Separator
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The active separator blocks contain the complete Möbius support, even
when some of the original private branches are zero. -/
theorem dependsOn_active_branches (h : Partition G B A) (z : graphicalFunctionSpace G) :
    DependsOn z.1 (B ∪ univ.biUnion (fun j : Gluing.ActiveBranch
      (((functionEquiv h).symm z).2) => A j.1)) := by
  classical
  let f:=((functionEquiv h).symm z).2
  let T:=B ∪ univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1)
  have hy:=(mobius_cliqueSupported_iff G z.1).mpr z.2
  rw [← zeta_mobius z.1]
  apply zeta_dependsOn
  intro C hCT
  by_cases hcl : IsCliqueCoordinate G C
  · have hCB : ¬C⊆B:=fun hc => hCT (hc.trans subset_union_left)
    obtain ⟨j,hCj,huniq⟩:=h.clique_unique_branch ⟨C,hcl⟩ hCB
    let D : privateIndex G B A j:=⟨⟨C,hcl⟩,hCB,hCj⟩
    by_cases hf : f j=0
    · have hh:=congrFun hf D
      exact hh
    · apply False.elim
      apply hCT
      intro v hv
      rcases mem_union.mp (hCj hv) with hvB | hvA
      · exact mem_union_left _ hvB
      · exact mem_union_right _ (mem_biUnion.mpr ⟨⟨j,hf⟩,mem_univ _,hvA⟩)
  · exact coefficient_zero_of_not_clique hy C hcl

/-- For singleton private branches, the number of active branches controls
the genuine affine dimension. This does not assume full ambient dimension. -/
theorem finrank_le_boundary_add_active (h : Partition G B A)
    (hA : ∀ j,(A j).card≤1) (z : graphicalFunctionSpace G) (hz : Supermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤
      B.card+Fintype.card (Gluing.ActiveBranch (((functionEquiv h).symm z).2))-1 := by
  classical
  let f:=((functionEquiv h).symm z).2
  have hb:=finrank_vectorSpan_le_support z.2.1 hz (dependsOn_active_branches h z)
  have hu : (univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1)).card≤
      Fintype.card (Gluing.ActiveBranch f) := by
    apply card_biUnion_le.trans
    calc
      (∑ j : Gluing.ActiveBranch f,(A j.1).card)≤∑ j : Gluing.ActiveBranch f,1 :=
        sum_le_sum (fun j hj => hA j.1)
      _=Fintype.card (Gluing.ActiveBranch f):=by simp
  have hc:=card_union_le B (univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1))
  exact hb.trans (Nat.sub_le_sub_right (hc.trans (Nat.add_le_add_left hu B.card)) 1)

end Separator
end GraphicalZonotopes
