import cubical.pl.cell_parity
import cubical.pl.simply_connected
import cubical.pl_abstract
import cubical.pl.facet_topology
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The cubical parity cocycle

Choose one vertex in every cell.  Comparable cells are joined with the parity
of the distance between their chosen vertices inside the larger cube.
Compatibility of local cube colorings makes this a genuine cocycle on the
face-chain triangulation.  Simple connectedness of its PL sphere realization
then supplies a global proper coloring of the original cubical graph.
-/

noncomputable section

open Classical Set

attribute [local instance] Classical.propDecidable

namespace Cubical.PL.CubeComplex

open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

def cellAnchor (F : K.Cell) : F.val := K.cellVertex F (fun _ => false)

def edgeParity (F G : K.Cell) : ZMod 2 :=
  if h : F ≤ G then
    K.localParity G (K.includeVertex F G h (K.cellAnchor F)) + K.localParity G (K.cellAnchor G)
  else if h : G ≤ F then
    K.localParity F (K.includeVertex G F h (K.cellAnchor G)) + K.localParity F (K.cellAnchor F)
  else 0

theorem edgeParity_of_le (F G : K.Cell) (hFG : F ≤ G) :
    K.edgeParity F G =
      K.localParity G (K.includeVertex F G hFG (K.cellAnchor F)) +
        K.localParity G (K.cellAnchor G) := by
  simp [edgeParity, hFG]

@[simp] theorem edgeParity_self (F : K.Cell) : K.edgeParity F F = 0 := by
  rw [K.edgeParity_of_le F F le_rfl]
  exact CharTwo.add_self_eq_zero _

theorem edgeParity_symm (F G : K.Cell) : K.edgeParity F G = K.edgeParity G F := by
  by_cases hFG : F ≤ G
  · by_cases hGF : G ≤ F
    · have : F = G := le_antisymm hFG hGF
      subst G
      rfl
    · simp [edgeParity, hFG, hGF]
  · by_cases hGF : G ≤ F <;> simp [edgeParity, hFG, hGF]

theorem edgeParity_in_cell (F G H : K.Cell) (hFG : F ≤ G ∨ G ≤ F)
    (hFH : F ≤ H) (hGH : G ≤ H) :
    K.edgeParity F G =
      K.localParity H (K.includeVertex F H hFH (K.cellAnchor F)) +
        K.localParity H (K.includeVertex G H hGH (K.cellAnchor G)) := by
  rcases hFG with hFG | hGF
  · rw [K.edgeParity_of_le F G hFG]
    exact K.localParity_pair_compatible G H hGH
      (K.includeVertex F G hFG (K.cellAnchor F)) (K.cellAnchor G)
  · rw [K.edgeParity_symm F G, K.edgeParity_of_le G F hGF]
    have h := K.localParity_pair_compatible F H hFH
      (K.includeVertex G F hGF (K.cellAnchor G)) (K.cellAnchor F)
    exact h.trans (add_comm _ _)

theorem edgeParity_triangle (F G H : K.Cell)
    (h : {F, G, H} ∈ K.orderComplex.faces) :
    K.edgeParity F G + K.edgeParity G H = K.edgeParity F H := by
  have hFG := h.2 F (by simp) G (by simp)
  have hGH := h.2 G (by simp) H (by simp)
  have hFH := h.2 F (by simp) H (by simp)
  have hm : ∃ M : K.Cell, F ≤ M ∧ G ≤ M ∧ H ≤ M := by
    rcases hFG with hFG | hGF
    · rcases hGH with hGH | hHG
      · exact ⟨H, hFG.trans hGH, hGH, le_rfl⟩
      · exact ⟨G, hFG, le_rfl, hHG⟩
    · rcases hFH with hFH | hHF
      · exact ⟨H, hFH, hGF.trans hFH, le_rfl⟩
      · exact ⟨F, le_rfl, hGF, hHF⟩
  obtain ⟨M, hFM, hGM, hHM⟩ := hm
  rw [K.edgeParity_in_cell F G M hFG hFM hGM,
    K.edgeParity_in_cell G H M hGH hGM hHM,
    K.edgeParity_in_cell F H M hFH hFM hHM]
  ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]

def orderVertexEquiv : K.Cell ≃ (standardRealization K.orderComplex).vertices :=
  standardVertexEquiv K.orderComplex K.singleton_mem_orderComplex

def ambientParity (x y : K.Cell → ℝ) : Bool :=
  if hx : x ∈ (standardRealization K.orderComplex).vertices then
    if hy : y ∈ (standardRealization K.orderComplex).vertices then
      zmod2Bool (K.edgeParity (K.orderVertexEquiv.symm ⟨x, hx⟩)
        (K.orderVertexEquiv.symm ⟨y, hy⟩))
    else false
  else false

theorem ambientParity_standard (F G : K.Cell) :
    K.ambientParity (standardVertex F) (standardVertex G) = zmod2Bool (K.edgeParity F G) := by
  have hF : standardVertex F ∈ (standardRealization K.orderComplex).vertices :=
    (K.orderVertexEquiv F).property
  have hG : standardVertex G ∈ (standardRealization K.orderComplex).vertices :=
    (K.orderVertexEquiv G).property
  simp only [ambientParity, dif_pos hF, dif_pos hG]
  change zmod2Bool (K.edgeParity (K.orderVertexEquiv.symm (K.orderVertexEquiv F))
    (K.orderVertexEquiv.symm (K.orderVertexEquiv G))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

def parityCocycle : SimplicialBoolCocycle (standardRealization K.orderComplex) where
  parity := K.ambientParity
  symm := by
    intro x y hxy
    unfold ambientParity
    split_ifs <;> try rfl
    exact congrArg zmod2Bool (K.edgeParity_symm _ _)
  self := by
    intro x hx
    change x ∈ (standardRealization K.orderComplex).vertices at hx
    unfold ambientParity
    rw [dif_pos hx, dif_pos hx, K.edgeParity_self]
    rfl
  cocycle := by
    intro x y z hxyz
    have hx : x ∈ (standardRealization K.orderComplex).vertices :=
      (standardRealization K.orderComplex).down_closed hxyz (by simp) (by simp)
    have hy : y ∈ (standardRealization K.orderComplex).vertices :=
      (standardRealization K.orderComplex).down_closed hxyz (by simp) (by simp)
    have hz : z ∈ (standardRealization K.orderComplex).vertices :=
      (standardRealization K.orderComplex).down_closed hxyz (by simp) (by simp)
    obtain ⟨F, hF⟩ := K.orderVertexEquiv.surjective ⟨x, hx⟩
    obtain ⟨G, hG⟩ := K.orderVertexEquiv.surjective ⟨y, hy⟩
    obtain ⟨H, hH⟩ := K.orderVertexEquiv.surjective ⟨z, hz⟩
    have hFx : standardVertex F = x := congrArg Subtype.val hF
    have hGy : standardVertex G = y := congrArg Subtype.val hG
    have hHz : standardVertex H = z := congrArg Subtype.val hH
    have hchain : {F, G, H} ∈ K.orderComplex.faces := by
      apply (image_mem_standardRealization_iff K.orderComplex {F, G, H}).mp
      convert hxyz using 1
      ext a
      simp [Finset.image_insert, Finset.image_singleton, hFx, hGy, hHz]
    rw [← hFx, ← hGy, ← hHz, K.ambientParity_standard, K.ambientParity_standard,
      K.ambientParity_standard, ← SimplicialBoolCocycle.zmod2Bool_add,
      K.edgeParity_triangle F G H hchain]

def singletonCell (v : V) : K.Cell := ⟨{v}, K.singleton_mem v⟩

@[simp] theorem cellAnchor_singletonCell (v : V) :
    (K.cellAnchor (K.singletonCell v)).val = v :=
  Finset.mem_singleton.mp (K.cellAnchor (K.singletonCell v)).property

theorem bipartite_of_orderSphere {n : ℕ} (hn : 2 ≤ n)
    (hK : IsPLSphere n (standardRealization K.orderComplex).space) :
    ∃ c : V → Bool, ∀ v w, K.graph.Adj v w → c v ≠ c w := by
  letI : Finite (standardRealization K.orderComplex).faces :=
    (standardRealization_finite_faces K.orderComplex).to_subtype
  obtain ⟨δ, hδ⟩ := cocycle_exact_of_sphere hn hK K.parityCocycle
  let f (F : K.Cell) : ZMod 2 := boolZMod2 (δ (standardVertex F))
  have hpair (F G : K.Cell) (hFG : F ≤ G) : K.edgeParity F G = f F + f G := by
    have hface : {standardVertex F, standardVertex G} ∈
        (standardRealization K.orderComplex).faces := by
      have h := (image_mem_standardRealization_iff K.orderComplex {F, G}).mpr
        ((K.pair_mem_orderComplex_iff F G).mpr (Or.inl hFG))
      simpa using h
    have h := congrArg boolZMod2 (hδ (standardVertex F) (standardVertex G) (by
      convert hface using 1 <;> ext a <;> simp))
    change boolZMod2 (K.ambientParity _ _) = _ at h
    rw [K.ambientParity_standard, boolZMod2_zmod2Bool, boolZMod2_xor] at h
    exact h
  refine ⟨fun v => δ (standardVertex (K.singletonCell v)), ?_⟩
  intro v w hvw heq
  let F : K.Cell := ⟨{v, w}, hvw.2.1⟩
  have hv : v ∈ F.val := by simp [F]
  have hw : w ∈ F.val := by simp [F]
  have hvF : K.singletonCell v ≤ F := Finset.singleton_subset_iff.mpr hv
  have hwF : K.singletonCell w ≤ F := Finset.singleton_subset_iff.mpr hw
  have hsum : f (K.singletonCell v) + f (K.singletonCell w) = 1 := by
    calc
      _ = (f (K.singletonCell v) + f F) + (f (K.singletonCell w) + f F) := by
        ring_nf
        simp [show (2 : ZMod 2) = 0 by decide]
      _ = K.edgeParity (K.singletonCell v) F + K.edgeParity (K.singletonCell w) F := by
        rw [hpair _ _ hvF, hpair _ _ hwF]
      _ = K.localParity F ⟨v, hv⟩ + K.localParity F ⟨w, hw⟩ := by
        rw [K.edgeParity_of_le _ _ hvF, K.edgeParity_of_le _ _ hwF]
        have hv' : K.includeVertex (K.singletonCell v) F hvF (K.cellAnchor (K.singletonCell v)) =
            (⟨v, hv⟩ : F.val) := Subtype.ext (K.cellAnchor_singletonCell v)
        have hw' : K.includeVertex (K.singletonCell w) F hwF (K.cellAnchor (K.singletonCell w)) =
            (⟨w, hw⟩ : F.val) := Subtype.ext (K.cellAnchor_singletonCell w)
        rw [hv', hw']
        ring_nf
        simp [show (2 : ZMod 2) = 0 by decide]
      _ = 1 := K.localParity_adj F ⟨v, hv⟩ ⟨w, hw⟩ hvw
  have hf : f (K.singletonCell v) = f (K.singletonCell w) := congrArg boolZMod2 heq
  rw [hf, CharTwo.add_self_eq_zero] at hsum
  exact zero_ne_one hsum

/-- Every cubical PL sphere of dimension at least two has a proper
coloring of its original vertices by two colors. -/
theorem IsSphere.bipartite {n : ℕ} (hK : K.IsSphere n) (hn : 2 ≤ n) :
    Nonempty (K.graph.Coloring Bool) := by
  obtain ⟨c, hc⟩ := K.bipartite_of_orderSphere hn hK
  exact ⟨{ toFun := c, map_rel' := fun h => hc _ _ h }⟩

end Cubical.PL.CubeComplex
