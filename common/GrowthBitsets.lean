module
prelude
public import FastGrowthCompatibility
public import Init.Data.Nat.Bitwise.Lemmas

@[expose] public section

/-! Natural-number bitsets used only through proved membership laws. -/

namespace Papers.RationalityTen.GrowthBitsets

open ConcreteGrowth SparseGrowthDAG

theorem bitAt_eq_testBit (bits index : Nat) : bitAt bits index = bits.testBit index :=
  Nat.testBit_eq_decide_div_mod_eq.symm

theorem bitAt_or (a b i : Nat) : bitAt (Nat.lor a b) i = (bitAt a i || bitAt b i) := by
  simp only [bitAt_eq_testBit]
  exact Nat.testBit_or a b i

theorem bitAt_and (a b i : Nat) : bitAt (Nat.land a b) i = (bitAt a i && bitAt b i) := by
  simp only [bitAt_eq_testBit]
  exact Nat.testBit_and a b i

theorem bitAt_zero (i : Nat) : bitAt 0 i = false := by
  simp only [bitAt_eq_testBit, Nat.zero_testBit]

theorem bitAt_power (a i : Nat) : bitAt (2^a) i = decide (a = i) := by
  simp only [bitAt_eq_testBit, Nat.testBit_two_pow]

def unionValues {α : Type} (value : α → Nat) (items : List α) : Nat :=
  items.foldr (fun a rest => Nat.lor (value a) rest) 0

theorem bitAt_unionValues {α : Type} (value : α → Nat) (items : List α) (i : Nat) :
    bitAt (unionValues value items) i = true ↔ ∃ a, a ∈ items ∧ bitAt (value a) i = true := by
  induction items with
  | nil => simp [unionValues, bitAt_zero]
  | cons a rest ih =>
    rw [unionValues, List.foldr_cons, bitAt_or, Bool.or_eq_true_iff]
    change bitAt (value a) i = true ∨ bitAt (unionValues value rest) i = true ↔ _
    rw [ih]
    constructor
    · intro h
      rcases h with ha | ⟨b, hb, hbit⟩
      · exact ⟨a, List.mem_cons_self, ha⟩
      · exact ⟨b, List.mem_cons_of_mem _ hb, hbit⟩
    · rintro ⟨b, hb, hbit⟩
      rcases List.mem_cons.mp hb with heq | hb
      · exact Or.inl (heq ▸ hbit)
      · exact Or.inr ⟨b, hb, hbit⟩

def ofList {n : Nat} (items : List (Fin n)) : Nat :=
  unionValues (fun c => 2^c.val) items

theorem bitAt_ofList {n : Nat} (items : List (Fin n)) (c : Fin n) :
    bitAt (ofList items) c.val = true ↔ c ∈ items := by
  rw [ofList, bitAt_unionValues]
  constructor
  · rintro ⟨a, ha, hbit⟩
    rw [bitAt_power] at hbit
    have heq : a = c := Fin.ext (of_decide_eq_true hbit)
    exact heq ▸ ha
  · intro hc
    refine ⟨c, hc, ?_⟩
    rw [bitAt_power]
    exact decide_eq_true rfl

theorem bitAt_ofList_eq_has {n : Nat} (items : List (Fin n)) (c : Fin n) :
    bitAt (ofList items) c.val = has items c := by
  apply Bool.eq_iff_iff.mpr
  change bitAt (ofList items) c.val = true ↔ has items c = true
  rw [bitAt_ofList, has_true]

theorem bitAt_cover (candidates blocked children i : Nat)
    (hcover : Nat.land candidates (Nat.lor blocked children) = candidates)
    (hcandidate : bitAt candidates i = true) (hblocked : bitAt blocked i = false) :
    bitAt children i = true := by
  have hbit := congrArg (fun bits => bitAt bits i) hcover
  simpa only [bitAt_and, bitAt_or, hcandidate, hblocked, Bool.false_or, Bool.true_and] using hbit

end Papers.RationalityTen.GrowthBitsets
