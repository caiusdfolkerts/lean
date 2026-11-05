import cubical.pl.cube_complex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Local cube parity and its independence from a containing cell. -/

noncomputable section

open Classical

namespace Cubical.PL

theorem cube_reachable {n : ℕ} (x y : Cube.Vertex n) :
    (Cube.graph n).Reachable x y := by
  have h (A : Finset (Fin n)) :
      (Cube.graph n).Reachable x (fun i => if i ∈ A then y i else x i) := by
    induction A using Finset.induction_on with
    | empty => simpa using (SimpleGraph.Reachable.refl (G := Cube.graph n) x)
    | @insert i A hi ih =>
        let z : Cube.Vertex n := fun j => if j ∈ A then y j else x j
        let w : Cube.Vertex n := fun j => if j ∈ insert i A then y j else x j
        change (Cube.graph n).Reachable x z at ih
        change (Cube.graph n).Reachable x w
        by_cases heq : z i = y i
        · have hw : w = z := by
            funext j
            by_cases hji : j = i
            · subst j
              simpa [w] using heq.symm
            · simp [w, z, hji]
          simpa only [hw] using ih
        · have hw : w = Cube.flip z i := by
            funext j
            by_cases hji : j = i
            · subst j
              rw [Cube.flip_same]
              simp only [w, Finset.mem_insert_self, ite_true]
              cases hz : z i <;> cases hy : y i <;> simp_all
            · rw [Cube.flip_other z i j hji]
              simp [w, z, hji]
          exact ih.trans (SimpleGraph.Adj.reachable ⟨i, hw⟩)
  simpa using h Finset.univ

def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

def cubeParity {n : ℕ} (x : Cube.Vertex n) : ZMod 2 := ∑ i, bitValue (x i)

theorem cubeParity_flip {n : ℕ} (x : Cube.Vertex n) (i : Fin n) :
    cubeParity (Cube.flip x i) + cubeParity x = 1 := by
  unfold cubeParity
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_eq_single i]
  · rw [Cube.flip_same]
    cases x i <;> norm_num [bitValue]
  · intro j hj hji
    rw [Cube.flip_other x i j hji]
    exact CharTwo.add_self_eq_zero _
  · simp

namespace CubeComplex

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

def localParity (F : K.Cell) (v : F.val) : ZMod 2 :=
  cubeParity ((K.cellVertex F).symm v)

theorem localParity_adj (F : K.Cell) (v w : F.val) (h : K.graph.Adj v.val w.val) :
    K.localParity F v + K.localParity F w = 1 := by
  have h' : (Cube.graph (K.dimension F.val)).Adj
      ((K.cellVertex F).symm v) ((K.cellVertex F).symm w) := by
    apply (K.chart_adj_iff F _ _).mp
    simpa using h
  obtain ⟨i, hi⟩ := h'
  unfold localParity
  rw [hi, add_comm]
  exact cubeParity_flip _ i

theorem cell_reachable (F : K.Cell) (v w : F.val) :
    (K.graph.induce (F.val : Set V)).Reachable v w := by
  have h := (cube_reachable ((K.cellVertex F).symm v) ((K.cellVertex F).symm w)).map
    (K.cellGraphIso F).toHom
  change (K.graph.induce (F.val : Set V)).Reachable
    ((K.cellVertex F) ((K.cellVertex F).symm v))
    ((K.cellVertex F) ((K.cellVertex F).symm w)) at h
  simpa using h

def includeVertex (F G : K.Cell) (hFG : F ≤ G) (v : F.val) : G.val :=
  ⟨v.val, hFG v.property⟩

theorem localParity_difference_constant (F G : K.Cell) (hFG : F ≤ G)
    (v w : F.val) :
    K.localParity F v + K.localParity G (K.includeVertex F G hFG v) =
      K.localParity F w + K.localParity G (K.includeVertex F G hFG w) := by
  obtain ⟨p⟩ := K.cell_reachable F v w
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      have hf := K.localParity_adj F a b hab
      have hg := K.localParity_adj G (K.includeVertex F G hFG a)
        (K.includeVertex F G hFG b) hab
      have heq : K.localParity F a + K.localParity G (K.includeVertex F G hFG a) =
          K.localParity F b + K.localParity G (K.includeVertex F G hFG b) := by
        linear_combination (norm := ring_nf) hf + hg
        simp [show (2 : ZMod 2) = 0 by decide]
      exact heq.trans ih

theorem localParity_pair_compatible (F G : K.Cell) (hFG : F ≤ G) (v w : F.val) :
    K.localParity F v + K.localParity F w =
      K.localParity G (K.includeVertex F G hFG v) +
        K.localParity G (K.includeVertex F G hFG w) := by
  have h := K.localParity_difference_constant F G hFG v w
  linear_combination (norm := ring_nf) h
  simp [show (2 : ZMod 2) = 0 by decide]

end CubeComplex

end Cubical.PL
