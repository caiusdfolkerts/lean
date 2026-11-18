module
prelude
public import GrowthBitsets
public import PrimitiveBitsetGrowth
public import Init.Data.List.FinRange

@[expose] public section

/-!
# Packed incidence matrices checked by their columns

The bit for the incidence of column `c` with row `q` has position `n*q+c`.
Column bounds make this coding injective. A single equality between a literal
matrix and the OR of its sparse column incidences therefore certifies every
row simultaneously. Neither a list of empty rows nor separate row membership
checks are needed.
-/

namespace Papers.RationalityTen.PackedIncidenceMatrix

open ConcreteGrowth SparseGrowthDAG GrowthBitsets

variable {n r : Nat}

def code (columns : Fin n → List (Fin r)) : Nat :=
  unionValues
    (fun c => unionValues (fun q => PrimitiveBitsetGrowth.singleton (n * q.val + c.val)) (columns c))
    (List.finRange n)

def row (n matrix q : Nat) : Nat := (matrix >>> (n * q)) % PrimitiveBitsetGrowth.singleton n

theorem index_injective (a c : Fin n) (b q : Fin r)
    (h : n * b.val + a.val = n * q.val + c.val) : a = c ∧ b = q := by
  have ha : a.val = c.val := by
    have hm := congrArg (fun z => z % n) h
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
      Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_of_lt c.isLt] using hm
  have hq : b.val = q.val := by
    rw [ha] at h
    exact Nat.mul_left_cancel (Nat.zero_lt_of_lt c.isLt) (Nat.add_right_cancel h)
  exact ⟨Fin.ext ha, Fin.ext hq⟩

theorem code_bit (columns : Fin n → List (Fin r)) (q : Fin r) (c : Fin n) :
    bitAt (code columns) (n * q.val + c.val) = has (columns c) q := by
  apply Bool.eq_iff_iff.mpr
  rw [code, bitAt_unionValues, has_true]
  constructor
  · rintro ⟨a, _, ha⟩
    obtain ⟨b, hb, heq⟩ := (bitAt_unionValues _ _ _).mp ha
    rw [PrimitiveBitsetGrowth.singleton_eq, bitAt_power] at heq
    obtain ⟨rfl, rfl⟩ := index_injective a c b q (of_decide_eq_true heq)
    exact hb
  · intro hq
    refine ⟨c, List.mem_finRange c, (bitAt_unionValues _ _ _).mpr ⟨q, hq, ?_⟩⟩
    rw [PrimitiveBitsetGrowth.singleton_eq, bitAt_power]
    exact decide_eq_true rfl

theorem row_testBit (n matrix q : Nat) (c : Fin n) :
    (row n matrix q).testBit c.val = matrix.testBit (n * q + c.val) := by
  simp only [row, PrimitiveBitsetGrowth.singleton_eq, Nat.testBit_mod_two_pow, decide_eq_true c.isLt,
    Bool.true_and, Nat.testBit_shiftRight]

/-- Sparse column encoding gives the full row membership law. -/
theorem rows_exact (columns : Fin n → List (Fin r)) (q : Fin r) (c : Fin n) :
    bitAt (row n (code columns) q.val) c.val = has (columns c) q := by
  rw [bitAt_eq_testBit, row_testBit]
  exact (bitAt_eq_testBit _ _).symm.trans (code_bit columns q c)

/-- The producer checks one exact literal matrix equality. All candidate
rows then follow without any separate row certificates. -/
theorem rows_exact_of_code (columns : Fin n → List (Fin r)) (matrix : Nat)
    (h : matrix = code columns) (q : Fin r) (c : Fin n) :
    bitAt (row n matrix q.val) c.val = has (columns c) q := by
  rw [h]
  exact rows_exact columns q c

/-- The same matrix certificate establishes edge and missing-edge row laws
when the cell masks are the masks of their sparse column incidences. -/
theorem feature_rows_exact (columns : Fin n → List (Fin r))
    (masks : Fin n → Nat) (matrix : Nat)
    (hmatrix : matrix = code columns)
    (hmasks : ∀ c, masks c = PrimitiveBitsetGrowth.mask (columns c))
    (q : Fin r) (c : Fin n) :
    (row n matrix q.val).testBit c.val = (masks c).testBit q.val := by
  rw [← bitAt_eq_testBit, ← bitAt_eq_testBit, rows_exact_of_code columns matrix hmatrix]
  rw [hmasks, PrimitiveBitsetGrowth.mask_eq, bitAt_ofList_eq_has]

/-- A singleton column is a kind assignment. This supplies exact kind rows,
with the same coding used for ridge and edge incidence. -/
theorem kind_rows_exact (kind : Fin n → Fin r) (matrix : Nat)
    (h : matrix = code (fun c => [kind c])) (j : Fin r) (c : Fin n) :
    (row n matrix j.val).testBit c.val = decide (kind c = j) := by
  rw [← bitAt_eq_testBit, rows_exact_of_code (fun c => [kind c]) matrix h]
  simp only [has, List.any_cons, List.any_nil, Bool.or_false]

#print axioms rows_exact_of_code
#print axioms feature_rows_exact
#print axioms kind_rows_exact

end Papers.RationalityTen.PackedIncidenceMatrix
