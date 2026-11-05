module

public import Papers.GraphicalZonotopes.Mobius

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The elemental rows on an empty, one-point or two-point conditioning set,
expanded in the complete Möbius coordinates. -/
theorem delta_zeta_empty (y : SetFunction V) {a b : V} (hab : a ≠ b) :
    delta (zeta y) a b ∅ = y {a,b} := by
  rw [delta_zeta hab (by simp) (by simp)]
  have he : (({a,b} : Finset V).powerset.filter (fun C => a ∈ C ∧ b ∈ C)) = {{a,b}} := by
    ext C
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨hc, ha, hb⟩
      apply subset_antisymm hc
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rintro rfl
      simp
  change (∑ C ∈ ({a,b} : Finset V).powerset.filter (fun C => a∈C ∧ b∈C),y C)=y {a,b}
  rw [he]
  simp

theorem delta_zeta_singleton (y : SetFunction V) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    delta (zeta y) a b {c} = y {a,b} + y {a,b,c} := by
  rw [delta_zeta hab (by simpa) (by simpa)]
  have he : (({a,b,c} : Finset V).powerset.filter (fun C => a ∈ C ∧ b ∈ C)) =
      {{a,b}, {a,b,c}} := by
    ext C
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hc, ha, hb⟩
      by_cases hcc : c ∈ C
      · right
        apply subset_antisymm hc
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc
          · exact Or.inl hxa
          · exact Or.inr hxb
          · exact False.elim (hcc (hxc ▸ hx))
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    · rintro (rfl | rfl) <;> simp
  rw [he]
  have hne : ({a,b} : Finset V) ≠ {a,b,c} := by
    intro h
    have hc : c ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc] at hc
  simp [hne]

theorem delta_zeta_pair (y : SetFunction V) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    delta (zeta y) a b {c,d} =
      y {a,b} + y {a,b,c} + y {a,b,d} + y {a,b,c,d} := by
  rw [delta_zeta hab (by simp [hac, had]) (by simp [hbc, hbd])]
  have he : (({a,b,c,d} : Finset V).powerset.filter (fun C => a ∈ C ∧ b ∈ C)) =
      {{a,b}, {a,b,c}, {a,b,d}, {a,b,c,d}} := by
    ext C
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hc, ha, hb⟩
      by_cases hcc : c ∈ C <;> by_cases hdc : d ∈ C
      · right; right; right
        apply subset_antisymm hc
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      · right; left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc | hxd
          · exact Or.inl hxa
          · exact Or.inr (Or.inl hxb)
          · exact Or.inr (Or.inr hxc)
          · exact False.elim (hdc (hxd ▸ hx))
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
      · right; right; left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc | hxd
          · exact Or.inl hxa
          · exact Or.inr (Or.inl hxb)
          · exact False.elim (hcc (hxc ▸ hx))
          · exact Or.inr (Or.inr hxd)
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
      · left
        apply subset_antisymm
        · intro x hx
          have hm := hc hx
          simp only [mem_insert, mem_singleton] at hm ⊢
          rcases hm with hxa | hxb | hxc | hxd
          · exact Or.inl hxa
          · exact Or.inr hxb
          · exact False.elim (hcc (hxc ▸ hx))
          · exact False.elim (hdc (hxd ▸ hx))
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  rw [he]
  have habc : ({a,b} : Finset V) ≠ {a,b,c} := by
    intro h; have hc : c ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc] at hc
  have habd : ({a,b} : Finset V) ≠ {a,b,d} := by
    intro h; have hd : d ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm had, Ne.symm hbd] at hd
  have habcd : ({a,b} : Finset V) ≠ {a,b,c,d} := by
    intro h; have hc : c ∈ ({a,b} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc] at hc
  have hacd : ({a,b,c} : Finset V) ≠ {a,b,d} := by
    intro h; have hc : c ∈ ({a,b,d} : Finset V) := by rw [← h]; simp
    simp [Ne.symm hac, Ne.symm hbc, hcd] at hc
  have hacd' : ({a,b,c} : Finset V) ≠ {a,b,c,d} := by
    intro h; have hd : d ∈ ({a,b,c} : Finset V) := by rw [h]; simp
    simp [Ne.symm had, Ne.symm hbd, Ne.symm hcd] at hd
  have hadc' : ({a,b,d} : Finset V) ≠ {a,b,c,d} := by
    intro h; have hc : c ∈ ({a,b,d} : Finset V) := by rw [h]; simp
    simp [Ne.symm hac, Ne.symm hbc, hcd] at hc
  simp [habc, habd, habcd, hacd, hacd', hadc', add_assoc]

end GraphicalZonotopes
