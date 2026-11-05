module

public import Papers.GraphicalZonotopes.BooleanVertexExtension

/-! # The three-neighbor extension used in Theorem 8.2

The new marginal is the literal monotone Boolean function `b ∧ (a ∨ t)`.
Its sole negative elemental response is on `at` when `b` is present.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanVertexExtension
open Finset BooleanModule
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def andOr (a b t : V) : SetFunction V :=
  fun S => if b ∈ S ∧ (a ∈ S ∨ t ∈ S) then 1 else 0

theorem andOr_boolean (a b t : V) : IsMonotoneBoolean (andOr a b t) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro A B hAB
    by_cases h : b ∈ A ∧ (a ∈ A ∨ t ∈ A)
    · have hB : b ∈ B ∧ (a ∈ B ∨ t ∈ B) :=
        ⟨hAB h.1,h.2.elim (fun h => Or.inl (hAB h)) (fun h => Or.inr (hAB h))⟩
      simp only [andOr,if_pos h,if_pos hB,le_refl]
    · simp only [andOr,if_neg h]
      split_ifs <;> norm_num
  · intro S
    dsimp only [andOr]
    split_ifs <;> simp
  · simp [andOr]
  · simp [andOr]

theorem andOr_insert_outside {a b t u : V}
    (hua : u ≠ a) (hub : u ≠ b) (hut : u ≠ t) (S : Finset V) :
    andOr a b t (insert u S) = andOr a b t S := by
  simp [andOr,Ne.symm hua,Ne.symm hub,Ne.symm hut]

theorem andOr_delta_outside {a b t u : V}
    (hua : u ≠ a) (hub : u ≠ b) (hut : u ≠ t) (v : V) (S : Finset V) :
    delta (andOr a b t) u v S = 0 := by
  simp only [delta,andOr_insert_outside hua hub hut]
  ring

theorem andOr_delta_at {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {S : Finset V} (ha : a ∉ S) (ht : t ∉ S) :
    delta (andOr a b t) a t S = if b ∈ S then -1 else 0 := by
  by_cases hb : b ∈ S <;>
    simp [delta,andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt,ha,ht,hb]

theorem andOr_delta_ab {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {S : Finset V} (ha : a ∉ S) (hb : b ∉ S) :
    delta (andOr a b t) a b S = if t ∈ S then 0 else 1 := by
  by_cases ht : t ∈ S <;>
    simp [delta,andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt,ha,ht,hb]

theorem andOr_delta_bt {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {S : Finset V} (hb : b ∉ S) (ht : t ∉ S) :
    delta (andOr a b t) b t S = if a ∈ S then 0 else 1 := by
  by_cases ha : a ∈ S <;>
    simp [delta,andOr,hab,hat,hbt,Ne.symm hab,Ne.symm hat,Ne.symm hbt,ha,ht,hb]

theorem andOr_negative_iff {a b t : V} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {u v : V} (huv : u ≠ v) {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (andOr a b t) u v S = -1 ↔
      ((u = a ∧ v = t) ∨ (u = t ∧ v = a)) ∧ b ∈ S := by
  by_cases hua : u = a
  · subst u
    by_cases hvb : v = b
    · subst v
      rw [andOr_delta_ab hab hat hbt hu hv]
      split_ifs <;> simp_all <;> norm_num
    · by_cases hvt : v = t
      · subst v
        rw [andOr_delta_at hab hat hbt hu hv]
        split_ifs <;> simp_all <;> norm_num
      · rw [delta_comm,andOr_delta_outside (Ne.symm huv) hvb hvt]
        simp_all
  · by_cases hub : u = b
    · subst u
      by_cases hva : v = a
      · subst v
        rw [delta_comm,andOr_delta_ab hab hat hbt hv hu]
        split_ifs <;> simp_all <;> norm_num
      · by_cases hvt : v = t
        · subst v
          rw [andOr_delta_bt hab hat hbt hu hv]
          split_ifs <;> simp_all <;> norm_num
        · rw [delta_comm,andOr_delta_outside hva (Ne.symm huv) hvt]
          simp_all
    · by_cases hut : u = t
      · subst u
        by_cases hva : v = a
        · subst v
          rw [delta_comm,andOr_delta_at hab hat hbt hv hu]
          split_ifs <;> simp_all <;> norm_num
        · by_cases hvb : v = b
          · subst v
            rw [delta_comm,andOr_delta_bt hab hat hbt hv hu]
            split_ifs <;> simp_all <;> norm_num
          · rw [delta_comm,andOr_delta_outside hva hvb (Ne.symm huv)]
            simp_all
      · rw [andOr_delta_outside hua hub hut]
        simp_all

/-- The boundary condition is literal: every context containing the second
hub gives slack one on the first-hub–tip edge. -/
def UnitBoundary (z : SetFunction V) (a b t : V) : Prop :=
  a ≠ b ∧ a ≠ t ∧ b ≠ t ∧
    ∀ S : Finset V, a ∉ S → t ∉ S → b ∈ S → delta z a t S = 1

theorem andOr_add_supermodular {z : SetFunction V} {a b t : V}
    (hz : Supermodular z) (hb : UnitBoundary z a b t) :
    Supermodular (z + andOr a b t) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_add]
  have hnn := hz.elemental u v huv S hu hv
  rcases delta_values (andOr_boolean a b t) u v S with hneg | hzero | hone
  · obtain ⟨hpair,hbS⟩ := (andOr_negative_iff hb.1 hb.2.1 hb.2.2.1 huv hu hv).mp hneg
    rcases hpair with ⟨hua,hvt⟩ | ⟨hut,hva⟩
    · subst u
      subst v
      rw [hb.2.2.2 S hu hv hbS,hneg]
      norm_num
    · subst u
      subst v
      rw [delta_comm (z := z) t a S,hb.2.2.2 S hv hu hbS,hneg]
      norm_num
  · rw [hzero]
    linarith
  · rw [hone]
    linarith

theorem triangular_append_extreme {z : SetFunction V} {a b t : V}
    (hz : ExtremeSupermodular z) (hb : UnitBoundary z a b t) :
    ExtremeSupermodular (append z (andOr a b t)) := by
  apply append_extreme hz (andOr_boolean a b t) (andOr_add_supermodular hz.2.1 hb)
  refine ⟨a,t,hb.2.1,{b},?_,?_,?_,?_⟩
  · simpa using hb.1
  · simpa using hb.2.2.1.symm
  · exact hb.2.2.2 _ (by simpa using hb.1) (by simpa using hb.2.2.1.symm) (by simp)
  · rw [andOr_delta_at hb.1 hb.2.1 hb.2.2.1 (by simpa using hb.1)
      (by simpa using hb.2.2.1.symm)]
    simp

/-- Swapping the hubs makes the newly appended vertex a boundary of exactly
the same kind. This is the uniform induction for every requested order. -/
theorem triangular_append_boundary {z : SetFunction V} {a b t : V}
    (hb : UnitBoundary z a b t) :
    UnitBoundary (append z (andOr a b t)) (Sum.inl b) (Sum.inl a) (Sum.inr 0) := by
  refine ⟨by simpa using hb.1.symm,by simp,by simp,?_⟩
  intro A hbA hwA haA
  rw [append_delta_new _ _ _ _ hwA]
  have ha : a ∈ hubs A := by simpa using haA
  have hb' : b ∉ hubs A := by simpa using hbA
  simp [andOr,ha,hb',hb.1,hb.1.symm]

end BooleanVertexExtension
end GraphicalZonotopes
