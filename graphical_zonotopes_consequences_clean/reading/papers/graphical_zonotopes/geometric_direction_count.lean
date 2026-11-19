module

public import Papers.GraphicalZonotopes.RootDirectionLines
public import Papers.GraphicalZonotopes.ActualDirectionsFromSlacks
public import Mathlib.Data.Set.Card

/-! # Counting actual geometric edge directions

An unoriented direction is the real line spanned by the difference of the
endpoints of an exposed edge. The final theorem identifies the cardinality of
this geometric set with `directionCount`, for every finite weak summand of a
graphical zonotope. Thus no chosen orientation or duplicate parallel edge
changes the count used by the principal theorems.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def actualEdgeDirectionLines (Q : Set (V → ℝ)) : Set (Submodule ℝ (V → ℝ)) :=
  {L | ∃ p q, IsExposedSegment Q p q ∧
    L = Submodule.span ℝ ({q - p} : Set (V → ℝ))}

abbrev ActualDirectionPair (Q : Set (V → ℝ)) :=
  {C : Finset V // C ∈ edgeFamily (actualDirectionGraph Q)}

def directionPairEndpoints {Q : Set (V → ℝ)} (e : ActualDirectionPair Q) :
    {p : V × V // p.1 ≠ p.2 ∧ e.1 = {p.1,p.2}} := by
  let h := card_eq_two.mp ((mem_edgeFamily _ _).mp e.2).1
  let u := Classical.choose h
  let v := Classical.choose (Classical.choose_spec h)
  exact ⟨(u,v),Classical.choose_spec (Classical.choose_spec h)⟩

def directionPairLine {Q : Set (V → ℝ)} (e : ActualDirectionPair Q) :
    Submodule ℝ (V → ℝ) :=
  Submodule.span ℝ ({(basisVector (directionPairEndpoints e).1.1 -
    basisVector (directionPairEndpoints e).1.2)} : Set (V → ℝ))

private theorem span_root_swap (u v : V) :
    Submodule.span ℝ ({basisVector v-basisVector u} : Set (V → ℝ)) =
      Submodule.span ℝ ({basisVector u-basisVector v} : Set (V → ℝ)) := by
  have he : basisVector v-basisVector u = (-1 : ℝ) •
      (basisVector u-basisVector v) := by module
  rw [he,Submodule.span_singleton_smul_eq
    (isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0))]

theorem directionPairLine_eq {Q : Set (V → ℝ)} (e : ActualDirectionPair Q)
    (u v : V) (he : e.1 = {u,v}) :
    directionPairLine e =
      Submodule.span ℝ ({basisVector u-basisVector v} : Set (V → ℝ)) := by
  let a := (directionPairEndpoints e).1.1
  let b := (directionPairEndpoints e).1.2
  have hab : a ≠ b := (directionPairEndpoints e).2.1
  have hc : ({a,b} : Finset V) = {u,v} := (directionPairEndpoints e).2.2.symm.trans he
  have ha : a=u ∨ a=v := by
    have hm : a ∈ ({u,v} : Finset V) := hc ▸ mem_insert_self a {b}
    simpa only [mem_insert,mem_singleton] using hm
  have hb : b=u ∨ b=v := by
    have hm : b ∈ ({u,v} : Finset V) := hc ▸ mem_insert_of_mem (mem_singleton_self b)
    simpa only [mem_insert,mem_singleton] using hm
  change Submodule.span ℝ ({basisVector a-basisVector b} : Set (V → ℝ)) = _
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · rw [ha,hb]
  · rw [ha,hb]
    exact span_root_swap u v
  · exact False.elim (hab (ha.trans hb.symm))

theorem directionPairLine_injective (Q : Set (V → ℝ)) :
    Function.Injective (directionPairLine (Q := Q)) := by
  intro e f h
  let a := (directionPairEndpoints e).1.1
  let b := (directionPairEndpoints e).1.2
  let u := (directionPairEndpoints f).1.1
  let v := (directionPairEndpoints f).1.2
  have hab : a ≠ b := (directionPairEndpoints e).2.1
  have huv : u ≠ v := (directionPairEndpoints f).2.1
  have he : e.1 = {a,b} := (directionPairEndpoints e).2.2
  have hf : f.1 = {u,v} := (directionPairEndpoints f).2.2
  rw [directionPairLine_eq e a b he,directionPairLine_eq f u v hf] at h
  have hm : basisVector a-basisVector b ∈
      Submodule.span ℝ ({basisVector u-basisVector v} : Set (V → ℝ)) :=
    h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have hp : ({a,b} : Finset V) = {u,v} :=
    root_parallel_pair_eq hab huv (by norm_num : (1 : ℝ) ≠ 0)
      (by simpa only [one_smul] using hc.symm)
  exact Subtype.ext (he.trans (hp.trans hf.symm))

theorem range_directionPairLine {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Set.range (directionPairLine (Q := Q)) = actualEdgeDirectionLines Q := by
  ext L
  constructor
  · rintro ⟨e,rfl⟩
    let u := (directionPairEndpoints e).1.1
    let v := (directionPairEndpoints e).1.2
    have huv : u ≠ v := (directionPairEndpoints e).2.1
    have he : e.1 = {u,v} := (directionPairEndpoints e).2.2
    have hm : ({u,v} : Finset V) ∈ edgeFamily (actualDirectionGraph Q) := he ▸ e.2
    have ha : ActualRootEdge Q u v := (pair_mem_edgeFamily _ huv).mp hm
    obtain ⟨_,p,q,hex,c,hc,hpq⟩ := ha
    refine ⟨p,q,hex,?_⟩
    rw [directionPairLine_eq e u v he,hpq,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]
  · rintro ⟨p,q,hex,rfl⟩
    obtain ⟨u,v,huv,c,hc,hpq⟩ := weak_summand_exposed_edge_direction hQ hw hex
    have hvu : v ≠ u := (G.ne_of_adj huv).symm
    have ha : ActualRootEdge Q v u := ⟨hvu,p,q,hex,c,hc,hpq⟩
    let e : ActualDirectionPair Q := ⟨{v,u},(pair_mem_edgeFamily _ hvu).mpr ha⟩
    refine ⟨e,?_⟩
    rw [directionPairLine_eq e v u rfl,hpq,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

theorem actualEdgeDirectionLines_finite {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    (actualEdgeDirectionLines Q).Finite := by
  classical
  rw [←range_directionPairLine hQ hw]
  exact Set.finite_range _

/-- The paper's number of geometric, unoriented edge directions is exactly
the finite root-pair count appearing in the verified numerical theorems. -/
theorem directionCount_eq_geometric_line_count {G : SimpleGraph V}
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    directionCount Q = (actualEdgeDirectionLines Q).ncard := by
  classical
  rw [←range_directionPairLine hQ hw,
    Set.ncard_range_of_injective (directionPairLine_injective Q),Nat.card_eq_fintype_card]
  simp only [ActualDirectionPair,Fintype.card_coe,directionCount]

end GraphicalZonotopes
