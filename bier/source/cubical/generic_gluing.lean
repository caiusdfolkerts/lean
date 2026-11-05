import cubical.generic_rigidity
import cubical.generic_vertex_splitting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Gluing a connected family of rigid subgraphs

A connected family of rigid subgraphs covering all vertices is rigid
when every adjacent pair overlaps in at least the ambient dimension
many points in general position. Local Euclidean motions agree on each
overlap; connectedness makes one Euclidean motion valid everywhere.
-/

namespace Cubical.Rigidity

open Module

variable {V I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At one general-position placement, rigidity glues across any
connected family of embedded subgraphs with sufficiently large overlaps. -/
theorem isRigid_of_connected_cover [Fintype V] [FiniteDimensional ℝ E]
    {W : I → Type*} [∀ i, Fintype (W i)]
    (G : SimpleGraph V) (K : SimpleGraph I) (hK : K.Connected)
    (piece : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hsub : ∀ i a b, (piece i).Adj a b → G.Adj (inc i a) (inc i b))
    (hcover : ∀ v, ∃ i w, inc i w = v)
    (common : I → I → Finset V)
    (hcommon : ∀ i j, K.Adj i j → ∀ v ∈ common i j,
      v ∈ Set.range (inc i) ∧ v ∈ Set.range (inc j))
    (hcard : ∀ i j, K.Adj i j → finrank ℝ E ≤ (common i j).card)
    (hdim : 0 < finrank ℝ E)
    (p : V → E) (hpos : InGeneralLinearPosition p)
    (hlocal : ∀ i, IsRigid (piece i) (p ∘ inc i)) :
    IsRigid G p := by
  classical
  intro u hu
  have hm : ∀ i, IsMotion (piece i) (p ∘ inc i) (u ∘ inc i) := by
    intro i a b hab
    exact hu (inc i a) (inc i b) (hsub i a b hab)
  choose t A hA heval using fun i => hlocal i (u ∘ inc i) (hm i)
  have hagree : ∀ i j, K.Adj i j → ∀ x : E, t i + A i x = t j + A j x := by
    intro i j hij
    obtain ⟨q⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin (finrank ℝ E)) (β := common i j) (by simpa using hcard i j hij)
    let c : Fin (finrank ℝ E) → V := fun a => (q a).val
    have hc : Function.Injective c := Subtype.val_injective.comp q.injective
    have hli : AffineIndependent ℝ (p ∘ c) :=
      (hpos.linearIndependent c hc (by simp)).affineIndependent
    have hpinned : ∀ a, t i + A i (p (c a)) = t j + A j (p (c a)) := by
      intro a
      obtain ⟨wi, hwi⟩ := (hcommon i j hij (c a) (q a).property).1
      obtain ⟨wj, hwj⟩ := (hcommon i j hij (c a) (q a).property).2
      have hi := heval i wi
      have hj := heval j wj
      simp only [Function.comp_apply, hwi, hwj] at hi hj
      exact hi.symm.trans hj
    have : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hdim⟩⟩
    exact trivial_motion_agreement (t i) (t j) (A i) (A j) (hA i) (hA j)
      (p ∘ c) hli (by simp) hpinned
  have hall : ∀ i j, ∀ x : E, t i + A i x = t j + A j x := by
    intro i j
    obtain ⟨walk⟩ := hK i j
    induction walk with
    | nil => intro x; rfl
    | @cons i k j hik walk ih =>
      intro x
      exact (hagree i k hik x).trans (ih x)
  let i₀ : I := Classical.choice hK.nonempty
  refine ⟨t i₀, A i₀, hA i₀, ?_⟩
  intro v
  obtain ⟨i, w, hw⟩ := hcover v
  have h := heval i w
  simp only [Function.comp_apply, hw] at h
  exact h.trans (hall i i₀ (p v))

/-- Generic rigidity glues across a finite connected covering family
of subgraphs, with overlap size at least the ambient dimension. -/
theorem genericallyRigid_of_connected_cover [Fintype V] [Finite I]
    [FiniteDimensional ℝ E] {W : I → Type*} [∀ i, Fintype (W i)]
    (G : SimpleGraph V) (K : SimpleGraph I) (hK : K.Connected)
    (piece : ∀ i, SimpleGraph (W i)) (inc : ∀ i, W i ↪ V)
    (hsub : ∀ i a b, (piece i).Adj a b → G.Adj (inc i a) (inc i b))
    (hcover : ∀ v, ∃ i w, inc i w = v)
    (common : I → I → Finset V)
    (hcommon : ∀ i j, K.Adj i j → ∀ v ∈ common i j,
      v ∈ Set.range (inc i) ∧ v ∈ Set.range (inc j))
    (hcard : ∀ i j, K.Adj i j → finrank ℝ E ≤ (common i j).card)
    (hdim : 0 < finrank ℝ E)
    (hlocal : ∀ i, GenericallyRigid (piece i) E) :
    GenericallyRigid G E := by
  obtain ⟨p, hp, hpos⟩ := exists_simultaneous_rigid_in_general_position piece inc hlocal
  exact ⟨p, isRigid_of_connected_cover G K hK piece inc hsub hcover common
    hcommon hcard hdim p hpos hp⟩

end Cubical.Rigidity
