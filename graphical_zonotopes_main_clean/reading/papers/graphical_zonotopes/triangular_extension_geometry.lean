module

public import Papers.GraphicalZonotopes.SingleVertexGraph

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem andOr_graphical {G : SimpleGraph V} {a b t : V}
    (hT : G.IsClique ({a,b,t} : Finset V)) : Graphical G (andOr a b t) := by
  intro u v huv hnon S hu hv
  by_cases huT : u ∈ ({a,b,t} : Finset V)
  · by_cases hvT : v ∈ ({a,b,t} : Finset V)
    · exact False.elim (hnon (hT huT hvT huv))
    · have hva : v ≠ a := fun he => hvT (by simp [he])
      have hvb : v ≠ b := fun he => hvT (by simp [he])
      have hvt : v ≠ t := fun he => hvT (by simp [he])
      rw [delta_comm]
      exact andOr_delta_outside hva hvb hvt u S
  · have hua : u ≠ a := fun he => huT (by simp [he])
    have hub : u ≠ b := fun he => huT (by simp [he])
    have hut : u ≠ t := fun he => huT (by simp [he])
    exact andOr_delta_outside hua hub hut v S

theorem triangular_append_graphical {G : SimpleGraph V} {z : SetFunction V} {a b t : V}
    (hz : Graphical G z) (hT : G.IsClique ({a,b,t} : Finset V)) :
    Graphical (SingleVertexGraph.graph G {a,b,t}) (append z (andOr a b t)) := by
  intro x y hxy hnon A hx hy
  have hF := andOr_graphical hT
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have huv : u ≠ v := fun he => hxy (congrArg Sum.inl he)
      have hu : u ∉ hubs A := by simpa using hx
      have hv : v ∉ hubs A := by simpa using hy
      rw [append_delta_old,hz u v huv hnon _ hu hv,hF u v huv hnon _ hu hv]
      split_ifs <;> simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change u ∉ ({a,b,t} : Finset V) at hnon
      have hua : u ≠ a := fun he => hnon (by simp [he])
      have hub : u ≠ b := fun he => hnon (by simp [he])
      have hut : u ≠ t := fun he => hnon (by simp [he])
      rw [append_delta_new _ _ _ _ hy,andOr_insert_outside hua hub hut,sub_self]
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      change v ∉ ({a,b,t} : Finset V) at hnon
      have hva : v ≠ a := fun he => hnon (by simp [he])
      have hvb : v ≠ b := fun he => hnon (by simp [he])
      have hvt : v ≠ t := fun he => hnon (by simp [he])
      rw [delta_comm,append_delta_new _ _ _ _ hx,andOr_insert_outside hva hvb hvt,sub_self]
    | inr j => exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim _ _)))

theorem triangular_append_old_positive {z : SetFunction V} {a b t u v : V}
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) (hp : 0 < delta z u v S) :
    Sum.inl u ∉ (hubSet (J := Fin 1) S) ∧ Sum.inl v ∉ (hubSet (J := Fin 1) S) ∧
      0 < delta (append z (andOr a b t)) (Sum.inl u) (Sum.inl v) (hubSet S) := by
  refine ⟨by simpa using hu,by simpa using hv,?_⟩
  rw [append_delta_old]
  simpa using hp

theorem triangular_append_spoke_positive {z : SetFunction V} {a b t : V}
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) {u : V}
    (hu : u ∈ ({a,b,t} : Finset V)) :
    ∃ A : Finset (Vertex V), Sum.inl u ∉ A ∧ Sum.inr 0 ∉ A ∧
      0 < delta (append z (andOr a b t)) (Sum.inl u) (Sum.inr 0) A := by
  simp only [mem_insert,mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨hubSet {b},by simpa using hab,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · refine ⟨hubSet {a},by simpa using hab.symm,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]
  · refine ⟨hubSet {b},by simpa using hbt.symm,by simp,?_⟩
    rw [append_delta_new _ _ _ _ (by simp)]
    simp [andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt]

theorem triangular_append_positive {G : SimpleGraph V} {z : SetFunction V} {a b t : V}
    (hb : UnitBoundary z a b t)
    (hz : ∀ u v, G.Adj u v → ∃ S : Finset V, u ∉ S ∧ v ∉ S ∧ 0 < delta z u v S) :
    ∀ x y, (SingleVertexGraph.graph G {a,b,t}).Adj x y →
      ∃ A : Finset (Vertex V), x ∉ A ∧ y ∉ A ∧
        0 < delta (append z (andOr a b t)) x y A := by
  intro x y hxy
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      obtain ⟨S,hu,hv,hp⟩ := hz u v hxy
      exact ⟨hubSet S,triangular_append_old_positive hu hv hp⟩
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact triangular_append_spoke_positive hb.1 hb.2.1 hb.2.2.1 hxy
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases y with
    | inl v =>
      obtain ⟨A,hv,hw,hp⟩ := triangular_append_spoke_positive
        (z := z) hb.1 hb.2.1 hb.2.2.1 hxy
      exact ⟨A,hw,hv,by simpa only [delta_comm] using hp⟩
    | inr j => exact False.elim hxy

theorem append_integerValued {z F : SetFunction V} (hz : IntegerValued z)
    (hF : IsMonotoneBoolean F) : IntegerValued (append z F) := by
  intro A
  obtain ⟨k,hk⟩ := hz (hubs A)
  have he : append z F A = z (hubs A) + if Sum.inr 0 ∈ A then F (hubs A) else 0 := by
    simp [append,assembled,boundaryLift,branchLift,Finset.sum_apply]
  rw [he,hk]
  by_cases hw : Sum.inr 0 ∈ A
  · rw [if_pos hw]
    rcases hF.values (hubs A) with hzero | hone
    · exact ⟨k,by rw [hzero,add_zero]⟩
    · exact ⟨k+1,by rw [hone]; norm_num⟩
  · exact ⟨k,by rw [if_neg hw,add_zero]⟩

theorem triangular_append_triangle {G : SimpleGraph V} {a b t : V}
    (hab : a ≠ b) (hT : G.IsClique ({a,b,t} : Finset V)) :
    (SingleVertexGraph.graph G {a,b,t}).IsClique
      ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) := by
  intro x hx y hy hxy
  change x ∈ ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) at hx
  change y ∈ ({Sum.inl b,Sum.inl a,Sum.inr 0} : Finset (Vertex V)) at hy
  simp only [mem_insert,mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact False.elim (hxy rfl)
  · exact hT (by simp) (by simp) hab.symm
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · exact hT (by simp) (by simp) hab
  · exact False.elim (hxy rfl)
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_insert_self _ _)
  · exact mem_insert_self _ _
  · exact False.elim (hxy rfl)

end BooleanVertexExtension
end GraphicalZonotopes
