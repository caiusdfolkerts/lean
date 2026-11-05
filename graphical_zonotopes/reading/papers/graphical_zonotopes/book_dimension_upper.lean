module

public import Papers.GraphicalZonotopes.WeakSummandReduction
public import Papers.GraphicalZonotopes.SeparatorPaperStatements
public import Papers.GraphicalZonotopes.GraphDefinitions
public import Mathlib.Order.Sum.Order

/-! # The full upper bound and necessity in Theorem 7.1 -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BookDimension
open Finset
attribute [local instance] Classical.propDecidable

abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k

local instance vertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))

local instance vertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (vertexOrder s k).toDecidableEq

def boundary (s k : ℕ) : Finset (Vertex s k) :=
  univ.image (Sum.inl : Fin s → Vertex s k)

def privatePart (s k : ℕ) (j : Fin k) : Finset (Vertex s k) := {Sum.inr j}

@[simp] theorem boundary_card (s k : ℕ) : (boundary s k).card=s := by
  rw [boundary,card_image_of_injective _ Sum.inl_injective]
  simp

theorem boundary_clique (s k : ℕ) : (cliqueBook s k).IsClique (boundary s k) := by
  intro u hu v hv huv
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
  exact ⟨huv,Or.inl rfl⟩

theorem partition (s k : ℕ) :
    Separator.Partition (cliqueBook s k) (boundary s k) (privatePart s k) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro v hv hp
    have he : v=Sum.inr j := mem_singleton.mp hp
    obtain ⟨i,hi,hei⟩ := mem_image.mp hv
    exact Sum.inl_ne_inr (hei.trans he)
  private_disjoint := by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (Sum.inr_injective he))
  cover v := by
    cases v with
    | inl i => exact Or.inl (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    | inr j => exact Or.inr ⟨j,mem_singleton_self _⟩
  no_cross_edge := by
    intro i j u v hu hv huv
    have hu' : u=Sum.inr i := mem_singleton.mp hu
    have hv' : v=Sum.inr j := mem_singleton.mp hv
    subst u
    subst v
    have hf : False := by
      simpa only [cliqueBook,Sum.isLeft_inr,Bool.false_eq_true,or_self,and_false] using huv
    exact hf.elim

theorem extreme_dimension_bound (s k : ℕ) (hs : 2≤s)
    (z : graphicalFunctionSpace (cliqueBook s k)) (hz : ExtremeSupermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤s+cliqueCapacity s-1 := by
  have hb := Separator.finrank_le_boundary_add_active (partition s k)
    (fun j => by simp [privatePart]) z hz.2.1
  have hc := Separator.separator_capacity_for_function (partition s k) z hz
  rw [←Separator.boundaryRow_card,Separator.boundaryRow_card_of_clique (boundary_clique s k),
    Separator.boundaryCliques_card_of_clique (boundary_clique s k),boundary_card] at hc
  change _≤cliqueCapacity s at hc
  rw [boundary_card] at hb
  omega

/-- Every actual weak indecomposable polytope summand satisfies the sharp
upper bound. Lower-dimensional summands and points are included. -/
theorem actual_summand_dimension_bound (s k : ℕ) (hs : 2≤s)
    {Q : Set (Vertex s k → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤min (s+k-1) (s+cliqueCapacity s-1) := by
  apply le_min
  · simpa only [Fintype.card_sum,Fintype.card_fin] using weak_summand_dimension_le hQ hi hw
  · obtain ⟨z,hz,hzero|hext,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      exact Nat.zero_le _
    · rw [hd]
      exact extreme_dimension_bound s k hs z hext

theorem maximum_dimension_upper (s k : ℕ) (hs : 2≤s) :
    maximumIndecomposableDimension (cliqueBook s k)≤min (s+k-1) (s+cliqueCapacity s-1) := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [←hd]
  exact actual_summand_dimension_bound s k hs hQ hi hw

theorem capacity_necessary (s k : ℕ) (hs : 2≤s)
    (h : SupportsFullIndecomposable (cliqueBook s k)) : k≤cliqueCapacity s := by
  obtain ⟨Q,hQ,hi,hd,hw⟩ := h
  have hb := actual_summand_dimension_bound s k hs hQ hi hw
  simp only [FullDimension,Fintype.card_sum,Fintype.card_fin] at hd
  rw [hd] at hb
  omega

end GraphicalZonotopes.BookDimension
