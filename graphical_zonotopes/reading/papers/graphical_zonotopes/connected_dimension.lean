module

public import Papers.GraphicalZonotopes.AffineDimension
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ambient zero-sum hyperplane has the expected dimension for every
finite nonempty vertex type, independently of a chosen enumeration. -/
theorem finrank_total_ker_fintype (v₀ : V) :
    Module.finrank ℝ (totalLinear (V := V)).ker=Fintype.card V-1 := by
  have hsurj : Function.Surjective (totalLinear (V := V)) := by
    intro a
    refine ⟨a • basisVector v₀,?_⟩
    change subsetSum (a • basisVector v₀) univ=a
    simp
  have hrange : (totalLinear (V := V)).range=⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := (totalLinear (V := V)).ker.finrank_quotient_add_finrank
  rw [(totalLinear (V := V)).quotKerEquivRange.finrank_eq,hrange] at h
  simp only [finrank_top,Module.finrank_self,Module.finrank_pi] at h
  omega

def pointedRoot (v₀ : V) (v : {v : V // v≠v₀}) : V → ℝ :=
  basisVector v.1-basisVector v₀

theorem pointedRoot_evaluation (v₀ : V) (v w : {v : V // v≠v₀}) :
    pointedRoot v₀ v w.1=if v=w then 1 else 0 := by
  have hne : w.1≠v₀ := w.2
  simp [pointedRoot,basisVector,Pi.single_apply,hne,Ne.symm hne,Subtype.ext_iff,eq_comm]

theorem pointedRoot_linearIndependent (v₀ : V) :
    LinearIndependent ℝ (pointedRoot v₀) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc w
  have h := congrFun hc w.1
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pointedRoot_evaluation] at h
  simpa using h

theorem card_ne_subtype (v₀ : V) : Fintype.card {v : V // v≠v₀}=Fintype.card V-1 := by
  simpa using Fintype.card_subtype_compl (fun v : V => v=v₀)

/-- Paths in an ordinary graph add their genuine root vectors. -/
theorem root_mem_of_reachable {G : SimpleGraph V} (W : Submodule ℝ (V → ℝ))
    (hW : ∀ u v,G.Adj u v → basisVector u-basisVector v∈W)
    {u v : V} (hpath : G.Reachable u v) : basisVector u-basisVector v∈W := by
  rw [SimpleGraph.reachable_eq_reflTransGen] at hpath
  induction hpath with
  | refl => simp
  | @tail v w hpath hstep ih =>
    have h := W.add_mem ih (hW v w hstep)
    convert h using 1 <;> module

/-- A connected set of actual root directions spans the entire zero-sum
hyperplane. This is an unbounded statement for arbitrary finite graphs. -/
theorem finrank_vectorSpan_eq_of_connected_roots {z : SetFunction V}
    (hne : (basePolytope z).Nonempty) {G : SimpleGraph V} (hG : G.Connected)
    (hroots : ∀ u v,G.Adj u v →
      basisVector u-basisVector v∈vectorSpan ℝ (basePolytope z)) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card V-1 := by
  obtain ⟨v₀⟩ := hG.nonempty
  have hu := Submodule.finrank_mono (vectorSpan_basePolytope_le_total_ker hne)
  rw [finrank_total_ker_fintype v₀] at hu
  have hspan : Submodule.span ℝ (Set.range (pointedRoot v₀))≤
      vectorSpan ℝ (basePolytope z) := by
    apply Submodule.span_le.mpr
    rintro x ⟨v,rfl⟩
    exact root_mem_of_reachable _ hroots (hG.preconnected v.1 v₀)
  have hl := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card (pointedRoot_linearIndependent v₀),card_ne_subtype v₀] at hl
  exact le_antisymm hu hl

theorem finrank_vectorSpan_eq_of_connected_slacks {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {G : SimpleGraph V} (hG : G.Connected)
    (hslack : ∀ u v,G.Adj u v → ∃ S : Finset V,
      u∉S ∧ v∉S ∧ delta z u v S≠0) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card V-1 := by
  apply finrank_vectorSpan_eq_of_connected_roots (basePolytope_nonempty hn hs) hG
  intro u v huv
  obtain ⟨S,hu,hv,hd⟩ := hslack u v huv
  exact root_mem_vectorSpan_of_delta_ne_zero hn hs (G.ne_of_adj huv) hu hv hd

end GraphicalZonotopes
