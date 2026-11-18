module

public import Papers.GraphicalZonotopes.SummandEdges
public import Papers.GraphicalZonotopes.Dilation
public import Papers.GraphicalZonotopes.ExposedSegments
public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.BoundaryContexts

/-! # Actual root edges and nonzero elemental slacks

The converse to the exposed-segment construction follows from the genuine
graphical weak-summand criterion, applied to the complete graph with one
pair removed.  No restriction on clique size is needed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- Every actual exposed edge of an arbitrary finite weak summand has an
ambient standard-root direction. This justifies counting all actual edge
directions by the unordered pairs in `actualDirectionGraph`. -/
theorem weak_summand_exposed_edge_direction {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    {p q : V → ℝ} (hex : IsExposedSegment Q p q) :
    ∃ u v,G.Adj u v ∧ ∃ t : ℝ,t ≠ 0 ∧
      q - p = t • (basisVector v - basisVector u) := by
  obtain ⟨a,ha,R,hR,hRc,hnR,hQR⟩ := hw
  have hzn : Normalized (a • graphFunction G) := by
    change a * graphFunction G ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hzs : Supermodular (a • graphFunction G) :=
    (graphFunction_supermodular G).smul ha.le
  have hbase : Q + R = basePolytope (a • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G)
      (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  obtain ⟨x,hx⟩ := basePolytope_nonempty hzn hzs
  rw [← hbase] at hx
  obtain ⟨xQ,hxQ,xR,hxR,hxsum⟩ := hx
  have hnQ : Q.Nonempty := ⟨xQ,hxQ⟩
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hnQ
  have hfs : Supermodular f :=
    summand_lowerSupport_supermodular hzn hzs hQ.compact hR hnQ hnR hbase
  have hbody : Q = basePolytope f :=
    summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hnQ hnR hbase
  exact basePolytope_summand_exposed_edge hfn hfs G ha.le R (hbody ▸ hQR) (hbody ▸ hex)

private def deletedPairGraph {V : Type*} (u v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (a ≠ u ∨ b ≠ v) ∧ (a ≠ v ∨ b ≠ u)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem actualRootEdge_iff_nonzero_elemental {V : Type*} [Fintype V] [DecidableEq V]
    {f : SetFunction V} (hn : Normalized f) (hs : Supermodular f) (u v : V) :
    ActualRootEdge (basePolytope f) u v ↔ u ≠ v ∧
      ∃ S : Finset V,u ∉ S ∧ v ∉ S ∧ delta f u v S ≠ 0 := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    by_contra hnone
    push_neg at hnone
    have hg : Graphical (deletedPairGraph u v) f := by
      intro a b hab hnon S ha hb
      have hp : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        change ¬(a ≠ b ∧ (a ≠ u ∨ b ≠ v) ∧ (a ≠ v ∨ b ≠ u)) at hnon
        tauto
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnone S ha hb
      · rw [delta_comm]
        exact hnone S hb ha
    obtain ⟨a,ha,R,hR,hRc,hnR,he⟩ :=
      (isWeakMinkowskiSummand_graphical_iff hn hs).mpr hg
    have hh := basePolytope_summand_actualRootEdge hn hs
      (deletedPairGraph u v) ha.le R he h
    exact hh.2.1.elim (fun hn => hn rfl) (fun hn => hn rfl)
  · rintro ⟨huv,S,hu,hv,hd⟩
    exact exposedSegment_of_positive_delta hn hs huv hu hv
      (lt_of_le_of_ne (hs.elemental u v huv S hu hv) (Ne.symm hd))

end GraphicalZonotopes
