import bier.self_dual_link
import bier.polytopal_link

/-! The self-dual construction preserves genuine nonpolytopality. -/

noncomputable section

namespace Bier.Complex

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsCentrallySymmetric (K : Bier.Complex V) : Prop :=
  ∃ τ : V ≃ V, (∀ v, τ (τ v) = v) ∧
    (∀ s, K.face (s.image τ) ↔ K.face s) ∧
    (∀ s, K.face s → Disjoint s (s.image τ))

theorem selfDualSuspension_bier_centrallySymmetric (K : Bier.Complex V) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).IsCentrallySymmetric := by
  refine ⟨Equiv.sumComm _ _, fun v => Sum.swap_swap v, ?_, ?_⟩
  · exact bier_swap_face _ _ K.selfDualSuspension_dual
  · exact bier_swap_disjoint _ _

theorem selfDualSuspension_bier_core_edge (K : Bier.Complex V) (v w : V) :
    (K.selfDualSuspension.bier K.selfDualSuspension_proper).face
      {Sum.inl (Sum.inl v), Sum.inl (Sum.inl w)} := by
  have hleft : ({Sum.inl (Sum.inl v), Sum.inl (Sum.inl w)} :
      Finset ((V ⊕ Bool) ⊕ (V ⊕ Bool))).toLeft = {Sum.inl v, Sum.inl w} := by ext; simp
  have hright : ({Sum.inl (Sum.inl v), Sum.inl (Sum.inl w)} :
      Finset ((V ⊕ Bool) ⊕ (V ⊕ Bool))).toRight = ∅ := by ext; simp
  rw [bier_face_iff, hleft, hright, Finset.compl_empty]
  exact ⟨by simp [selfDualSuspension], K.selfDualSuspension_proper, by simp⟩

theorem selfDualSuspension_nonpolytopal (K : Bier.Complex V) (hK : K.Proper)
    (hcard : 2 ≤ Fintype.card V)
    (hnonpoly : ¬ Bier.Polytopal (K.ghost.bier K.ghost_proper)) :
    ¬ Bier.Polytopal (K.selfDualSuspension.bier K.selfDualSuspension_proper) := by
  rintro ⟨n, ⟨r⟩⟩
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  let L := K.selfDualSuspension.bier K.selfDualSuspension_proper
  let a : ↥L.vertices := ⟨.inl (.inl v),
    (mem_vertices _ _).mpr (K.selfDualSuspension_bier_all_vertices hK _)⟩
  let b : ↥L.vertices := ⟨.inl (.inl w),
    (mem_vertices _ _).mpr (K.selfDualSuspension_bier_all_vertices hK _)⟩
  have hab : a ≠ b := by
    intro h
    exact hvw (Sum.inl.inj (Sum.inl.inj (congrArg Subtype.val h)))
  have hface : L.face (({a, b} : Finset ↥L.vertices).image Subtype.val) := by
    simpa only [Finset.image_insert, Finset.image_singleton] using
      K.selfDualSuspension_bier_core_edge v w
  have hdim : 2 ≤ r.polytope.dim := by
    have hh := r.face_card_le_dim hface
    simpa only [Finset.card_pair hab] using hh
  let apex : ↥L.vertices := ⟨.inl (.inr false),
    (mem_vertices _ _).mpr K.selfDualSuspension_a_vertex⟩
  have hlink := r.link_polytopal apex hdim
  change Bier.Polytopal ((K.selfDualSuspension.bier K.selfDualSuspension_proper).link
    (.inl (.inr false)) K.selfDualSuspension_a_vertex) at hlink
  rw [selfDualSuspension_link_eq_map] at hlink
  exact hnonpoly (((K.ghost.bier K.ghost_proper).polytopal_map_iff
    suspensionBierLabel suspensionBierLabel_injective).mp hlink)

end Bier.Complex
