module

public import Papers.GraphicalZonotopes.CliqueSeparatorCapacity
public import Papers.GraphicalZonotopes.SeparatorLifts
public import Papers.GraphicalZonotopes.SupportGeometry
public import Papers.GraphicalZonotopes.Translation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators Pointwise
variable {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
variable {G : SimpleGraph (Fin n)} {B : Finset (Fin n)} {A : J → Finset (Fin n)}

/-- Full dimension activates every nonempty actual private component.
A zero private block would remove every coefficient containing one of its
vertices, contradicting the genuine affine dimension of the base polytope. -/
theorem private_block_ne_zero_of_fullDimension (hn : 2≤n) (h : Partition G B A)
    (z : graphicalFunctionSpace G) (hz : Supermodular z.1)
    (hd : FullDimension (basePolytope z.1)) (j : J) (hAj : (A j).Nonempty) :
    ((functionEquiv h).symm z).2 j≠0 := by
  classical
  intro hzero
  obtain ⟨v,hvj⟩:=hAj
  have hvB : v∉B:=fun hvB =>
    disjoint_left.mp (h.boundary_disjoint j) hvB hvj
  have hy:=(mobius_cliqueSupported_iff G z.1).mpr z.2
  have hkill : ∀ C : Finset (Fin n),v∈C → mobius z.1 C=0 := by
    intro C hvC
    by_cases hC : IsCliqueCoordinate G C
    · have hCB : ¬C⊆B:=fun hCB => hvB (hCB hvC)
      obtain ⟨k,hCk,hunique⟩:=h.clique_unique_branch ⟨C,hC⟩ hCB
      have hvk : v∈A k:=(mem_union.mp (hCk hvC)).resolve_left hvB
      have hkj : k=j := by
        by_contra hkj
        exact disjoint_left.mp (h.private_disjoint hkj) hvk hvj
      subst k
      let D : privateIndex G B A j:=⟨⟨C,hC⟩,hCB,hCk⟩
      have he:=congrFun hzero D
      simpa only [private_coordinate_eq_mobius,Pi.zero_apply] using he
    · exact coefficient_zero_of_not_clique hy C hC
  have hdep : DependsOn z.1 (univ.erase v) := by
    rw [← zeta_mobius z.1]
    apply zeta_dependsOn
    intro C hC
    apply hkill C
    by_contra hvC
    apply hC
    intro w hw
    exact mem_erase.mpr ⟨fun he => hvC (he ▸ hw),mem_univ _⟩
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))=n-1 := by
    simpa only [FullDimension,Fintype.card_fin] using hd
  have he:=fullDimension_dependsOn_eq_univ hn z.2.1 hz hdim hdep
  have hmem : v∈univ.erase v:=by rw [he]; exact mem_univ _
  exact notMem_erase _ _ hmem

theorem componentPart_nonempty (G : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (c : (outsideGraph G B).ConnectedComponent) : (componentPart G B c).Nonempty := by
  obtain ⟨v,hv⟩:=c.exists_rep
  exact ⟨v.1,(mem_componentPart G B c v.1).mpr ⟨v.2,hv⟩⟩

theorem full_dimension_clique_separator_bound (hn : 2≤n) (B : Finset (Fin n))
    (hB : G.IsClique B) (hs : 2≤B.card) (z : graphicalFunctionSpace G)
    (hz : ExtremeSupermodular z.1) (hd : FullDimension (basePolytope z.1)) :
    Nat.card ((outsideGraph G B).ConnectedComponent)≤cliqueCapacity B.card := by
  classical
  let x:=(functionEquiv (componentPartition G B)).symm z
  have hactive : ∀ j,x.2 j≠0:=fun j =>
    private_block_ne_zero_of_fullDimension hn (componentPartition G B) z hz.2.1 hd j
      (componentPart_nonempty G B j)
  let e : Gluing.ActiveBranch x.2 ≃ (outsideGraph G B).ConnectedComponent := {
    toFun:=Subtype.val
    invFun:=fun j => ⟨j,hactive j⟩
    left_inv:=fun _ => rfl
    right_inv:=fun _ => rfl }
  have hb:=clique_separator_capacity hB hs z hz
  change Fintype.card (Gluing.ActiveBranch x.2)≤cliqueCapacity B.card at hb
  rw [Fintype.card_congr e] at hb
  simpa only [Nat.card_eq_fintype_card] using hb

/-- Corollary5.3 for the literal normalized graphical cone and genuine
polytope dimension, including all connected components after deletion. -/
theorem full_dimension_triangle_separator_bound (hn : 2≤n) (T : Finset (Fin n))
    (hT : T.card=3) (hc : G.IsClique T) (z : graphicalFunctionSpace G)
    (hz : ExtremeSupermodular z.1) (hd : FullDimension (basePolytope z.1)) :
    Nat.card ((outsideGraph G T).ConnectedComponent)≤3 := by
  have hb:=full_dimension_clique_separator_bound hn T hc (by omega) z hz hd
  simpa only [hT,cliqueCapacity_three] using hb

end Separator

open scoped Pointwise

/-- Ordinary compact-convex weak summands are converted to their actual
normalized lower-support function. No generalized-permutahedron presentation
or coefficient-support condition is added to the geometric hypothesis. -/
theorem SupportsFullIndecomposable.exists_extreme_function {n : ℕ} (hn : 2≤n)
    {G : SimpleGraph (Fin n)} (h : SupportsFullIndecomposable G) :
    ∃ z : graphicalFunctionSpace G,ExtremeSupermodular z.1 ∧
      FullDimension (basePolytope z.1) := by
  obtain ⟨Q,hQ,hi,hd,a,ha,R,hR,hRc,hnR,hQR⟩:=h
  have hTn : Normalized (a • graphFunction G) := by
    change a*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs:=(graphFunction_supermodular G).smul ha.le
  have hbase : Q+R=basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) ha.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f:=lowerSupport Q
  have hfn : Normalized f:=lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f:=summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f:=summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs ha.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon A hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon A hu hv
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
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,?_,?_⟩
  · apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  · simpa only [FullDimension,Fintype.card_fin] using hdim

/-- The geometric form of Corollary5.3, with ordinary induced graph
deletion and no implicit active-branch hypothesis. -/
theorem SupportsFullIndecomposable.triangle_components_le_three {n : ℕ} (hn : 2≤n)
    {G : SimpleGraph (Fin n)} (h : SupportsFullIndecomposable G)
    (T : Finset (Fin n)) (hT : T.card=3) (hc : G.IsClique T) :
    Nat.card ((G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent)≤3 := by
  obtain ⟨z,hz,hd⟩:=h.exists_extreme_function hn
  exact Separator.full_dimension_triangle_separator_bound hn T hT hc z hz hd

end GraphicalZonotopes
