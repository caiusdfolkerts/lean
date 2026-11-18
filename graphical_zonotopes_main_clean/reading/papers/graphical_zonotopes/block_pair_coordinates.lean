module

public import Papers.GraphicalZonotopes.PureResponseClasses
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J]

/-- All actual unordered pairs of a fixed clique, represented by the ambient
linear order. No pair is omitted from the quotient block. -/
abbrev PairIn (C : Finset H) :=
  {e : OrientedEdge (⊤ : SimpleGraph H) // e.1.1∈C ∧ e.1.2∈C}

def pairRow (C : Finset H) (e : PairIn C) : HubResponseRow H :=
  ⟨e.1,⟨(C.erase e.1.1.1).erase e.1.1.2,mem_powerset.mpr (by
    intro a ha
    obtain ⟨ha₂,ha'⟩:=mem_erase.mp ha
    obtain ⟨ha₁,_⟩:=mem_erase.mp ha'
    exact (mem_commonNeighbors _ _ _ _).mpr
      ⟨(SimpleGraph.top_adj _ _).mpr ha₁.symm,
        (SimpleGraph.top_adj _ _).mpr ha₂.symm⟩)⟩⟩

@[simp] theorem pairRow_edge (C : Finset H) (e : PairIn C) :
    (pairRow C e).1=e.1 := rfl

@[simp] theorem rowClique_pairRow (C : Finset H) (e : PairIn C) :
    rowClique (pairRow C e)=C := by
  change insert e.1.1.1 (insert e.1.1.2 ((C.erase e.1.1.1).erase e.1.1.2))=C
  ext a
  by_cases ha₁ : a=e.1.1.1
  · subst a
    simp [e.2.1]
  · by_cases ha₂ : a=e.1.1.2
    · subst a
      simp [e.2.2]
    · simp [mem_erase,ha₁,ha₂]

def pairAtRow (C : Finset H) (r : HubResponseRow H) (h : rowClique r=C) : PairIn C :=
  ⟨r.1,by
    rw [← h]
    exact ⟨mem_insert_self _ _,mem_insert_of_mem (mem_insert_self _ _)⟩⟩

/-- A vector on the pairs of `C` as an array in the full response-coordinate
space, with all other clique blocks explicitly zero. -/
def blockCoordinates (C : Finset H) : (PairIn C → ℝ) →ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun x r := if h : rowClique r=C then x (pairAtRow C r h) else 0
  map_add' x y := by
    funext r
    by_cases h : rowClique r=C <;> simp only [h,dite_true,dite_false,Pi.add_apply,add_zero]
  map_smul' c x := by
    funext r
    by_cases h : rowClique r=C <;>
      simp only [h,dite_true,dite_false,Pi.smul_apply,smul_eq_mul,mul_zero,RingHom.id_apply]

@[simp] theorem blockCoordinates_pairRow (C : Finset H) (x : PairIn C → ℝ)
    (e : PairIn C) : blockCoordinates C x (pairRow C e)=x e := by
  change (if h : rowClique (pairRow C e)=C then x (pairAtRow C (pairRow C e) h) else 0)=x e
  rw [dite_eq_left (rowClique_pairRow C e)]
  congr 1

def blockClass (C : Finset H) : (PairIn C → ℝ) →ₗ[ℝ] ResponseQuotient H :=
  coefficientClass ∘ₗ blockCoordinates C

/-- The kernel of the actual response-quotient map on one clique block is
exactly its constant vectors. This includes every pair of that clique. -/
theorem blockClass_eq_zero_iff (C : Finset H) (e₀ : PairIn C) (x : PairIn C → ℝ) :
    blockClass C x=0 ↔ ∃ c : ℝ,∀ e,x e=c := by
  change coefficientClass (blockCoordinates C x)=0 ↔ _
  rw [coefficientClass_eq_zero_iff]
  constructor
  · intro hx
    refine ⟨x e₀,?_⟩
    intro e
    have he : rowCliqueIndex (pairRow C e)=rowCliqueIndex (pairRow C e₀) := by
      apply Subtype.ext
      exact (rowClique_pairRow C e).trans (rowClique_pairRow C e₀).symm
    simpa only [blockCoordinates_pairRow] using hx _ _ he
  · rintro ⟨c,hc⟩ r t hrt
    have he : rowClique r=rowClique t:=congrArg Subtype.val hrt
    by_cases hr : rowClique r=C
    · have ht : rowClique t=C:=he.symm.trans hr
      change (if h : rowClique r=C then x (pairAtRow C r h) else 0)=
        if h : rowClique t=C then x (pairAtRow C t h) else 0
      rw [dite_eq_left hr,dite_eq_left ht,hc,hc]
    · have ht : rowClique t≠C:=fun h => hr (he.trans h)
      change (if h : rowClique r=C then x (pairAtRow C r h) else 0)=
        if h : rowClique t=C then x (pairAtRow C t h) else 0
      rw [dite_eq_right hr,dite_eq_right ht]

/-- Omitting one reference pair makes ordinary linear independence of pair
vectors equivalent to independence after passage to the actual quotient.
This is the precise reference-pair argument used in Lemma 7.7. -/
theorem blockClass_linearIndependent_of_reference (C : Finset H) (e₀ : PairIn C)
    (x : J → PairIn C → ℝ) (hx : LinearIndependent ℝ x)
    (hzero : ∀ j,x j e₀=0) :
    LinearIndependent ℝ (fun j => blockClass C (x j)) := by
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro c hc j
  have hmap : blockClass C (∑ i : J,c i • x i)=0 := by
    simpa only [map_sum,map_smul] using hc
  obtain ⟨a,ha⟩:=(blockClass_eq_zero_iff C e₀ _).mp hmap
  have ha0 : a=0 := by
    have hh:=ha e₀
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hzero,mul_zero,sum_const_zero] at hh
    exact hh.symm
  have hvec : (∑ i : J,c i • x i)=0 := by
    funext e
    exact (ha e).trans ha0
  exact hx c hvec j

theorem blockClass_linearIndependent_iff_reference (C : Finset H) (e₀ : PairIn C)
    (x : J → PairIn C → ℝ) (hzero : ∀ j,x j e₀=0) :
    LinearIndependent ℝ (fun j => blockClass C (x j)) ↔ LinearIndependent ℝ x := by
  constructor
  · intro hx
    exact LinearIndependent.of_comp (blockClass C) hx
  · intro hx
    exact blockClass_linearIndependent_of_reference C e₀ x hx hzero

end BooleanModule
end GraphicalZonotopes
