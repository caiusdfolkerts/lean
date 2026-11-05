module
prelude
public import FiniteMaskSets
public import Init.Data.List.Count
public import Init.Data.List.FinRange
public import Init.Data.Nat.Bitwise.Lemmas

@[expose] public section

namespace Papers.RationalityTen.FastMaskCardinality

def count : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, bits => count n (bits / 2) + if bits.testBit 0 then 1 else 0

theorem card_eq_count (n bits : Nat) : FiniteMaskSets.card n bits = count n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
      simp only [FiniteMaskSets.card, FiniteMaskSets.elements,
        ← List.countP_eq_length_filter, List.finRange_succ, List.countP_cons,
        List.countP_map, Fin.val_zero, Fin.val_succ, Function.comp_def,
        Nat.testBit_add_one, count]
      congr 1
      simpa only [FiniteMaskSets.card, FiniteMaskSets.elements,
        ← List.countP_eq_length_filter] using ih (bits / 2)

theorem count_add (a b bits : Nat) :
    count (a + b) bits = count a bits + count b (bits / 2 ^ a) := by
  induction a generalizing bits with
  | zero => simp only [Nat.zero_add, count, Nat.pow_zero, Nat.div_one]
  | succ a ih =>
      rw [Nat.succ_add, count, ih, count]
      have hdiv : bits / 2 / 2 ^ a = bits / 2 ^ (a + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
      rw [hdiv]
      omega

theorem count_mod (n bits : Nat) : count n (bits % 2 ^ n) = count n bits := by
  rw [← card_eq_count, ← card_eq_count]
  unfold FiniteMaskSets.card FiniteMaskSets.elements
  congr 1
  apply List.filter_congr
  intro i _
  simp only [Nat.testBit_mod_two_pow, i.isLt, decide_true, Bool.true_and]


/-- The two lookup tables are checked over their complete finite domains. -/
def byteCode : Nat := 95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224
def fiveCode : Nat := 55157063682984551670960690248

def byte (bits : Nat) : Nat := (byteCode >>> (4 * (bits % 256))) % 16
def five (bits : Nat) : Nat := (fiveCode >>> (3 * (bits % 32))) % 8

theorem byte_table : ∀ i : Fin 256, byte i.val = count 8 i.val := by decide +kernel
theorem five_table : ∀ i : Fin 32, five i.val = count 5 i.val := by decide +kernel

theorem byte_eq_count (bits : Nat) : byte bits = count 8 bits := by
  have h := byte_table ⟨bits % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [byte, Nat.mod_mod, ← count_mod 8 bits] using h

theorem five_eq_count (bits : Nat) : five bits = count 5 bits := by
  have h := five_table ⟨bits % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [five, Nat.mod_mod, ← count_mod 5 bits] using h

def card45 (bits : Nat) : Nat :=
  byte bits + byte (bits / 256) + byte (bits / 65536) +
    byte (bits / 16777216) + byte (bits / 4294967296) + five (bits / 1099511627776)

theorem card45_eq (bits : Nat) : card45 bits = FiniteMaskSets.card 45 bits := by
  rw [card_eq_count]
  unfold card45
  simp only [byte_eq_count, five_eq_count]
  rw [count_add 8 37 bits, count_add 8 29 (bits / 2 ^ 8),
    count_add 8 21 (bits / 2 ^ 8 / 2 ^ 8),
    count_add 8 13 (bits / 2 ^ 8 / 2 ^ 8 / 2 ^ 8),
    count_add 8 5 (bits / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)]
  simp only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul, Nat.add_assoc]

end Papers.RationalityTen.FastMaskCardinality
