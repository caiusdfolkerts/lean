module
prelude
public import FiniteMaskSets

@[expose] public section

/-!
# Shared incompatibility rows from exact vertex intersections

For a fixed cell, each possible intersection mask is recognized using one
bitwise intersection of the global vertex-incidence rows. A term rejects
that intersection when it is not a proper face of one of the two cells.
Any chosen union of such terms is a sound incompatibility cache. The proof
requires no quadratic table of cell pairs and no completeness assumption
about the chosen rejection terms.
-/

namespace Papers.RationalityTen.IntersectionIncompatibilityRows

open ConcreteGrowth GrowthBitsets FiniteMaskSets

variable {n v : Nat}

theorem testBit_xor (a b i : Nat) :
    (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

structure Rows (cells : Fin n → Cell) (v : Nat) where
  vertices : Fin v → Nat
  vertex_exact : ∀ j c, (vertices j).testBit c.val = (cells c).vertices.testBit j.val
  faces : Nat → Nat
  edge_complete : ∀ c q, q ∈ (cells c).edges → (faces q).testBit c.val = true
  ridge_complete : ∀ c q, q ∈ (cells c).ridgeMasks → (faces q).testBit c.val = true

def meetRows {α : Type} (n : Nat) (row : α → Nat) : List α → Nat
  | [] => allMask n
  | a :: rest => Nat.land (row a) (meetRows n row rest)

theorem meetRows_bit {α : Type} (row : α → Nat) (items : List α) (c : Fin n) :
    (meetRows n row items).testBit c.val = true ↔
      ∀ a, a ∈ items → (row a).testBit c.val = true := by
  induction items with
  | nil => simp only [meetRows, allMask_bit, List.not_mem_nil, false_implies, implies_true]
  | cons a rest ih =>
    rw [meetRows, testBit_land, Bool.and_eq_true_iff, ih]
    constructor
    · rintro ⟨ha, hrest⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hrest b hb
    · intro h
      exact ⟨h a List.mem_cons_self, fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

def coordinateRow {cells : Fin n → Cell} (R : Rows cells v)
    (a : Fin n) (q : Nat) (j : Fin v) : Nat :=
  if (cells a).vertices.testBit j.val then
    if q.testBit j.val then R.vertices j else Nat.xor (allMask n) (R.vertices j)
  else allMask n

def intersectionRow {cells : Fin n → Cell} (R : Rows cells v)
    (a : Fin n) (q : Nat) : Nat :=
  meetRows n (coordinateRow R a q) (List.finRange v)

theorem coordinateRow_bit {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (q : Nat) (j : Fin v) :
    (coordinateRow R a q j).testBit b.val = true ↔
      (cells a).vertices.testBit j.val = true →
        (cells b).vertices.testBit j.val = q.testBit j.val := by
  cases ha : (cells a).vertices.testBit j.val <;>
    cases hq : q.testBit j.val <;>
    cases hb : (cells b).vertices.testBit j.val <;>
    simp [coordinateRow, ha, hq, hb, allMask_bit, R.vertex_exact]

theorem intersectionRow_pointwise {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (q : Nat) :
    (intersectionRow R a q).testBit b.val = true ↔
      ∀ j : Fin v, (cells a).vertices.testBit j.val = true →
        (cells b).vertices.testBit j.val = q.testBit j.val := by
  simp only [intersectionRow, meetRows_bit, List.mem_finRange, true_implies,
    coordinateRow_bit]

/-- The checked subset condition is essential: coordinates outside the
first cell are absent from every intersection recognized by its row. -/
theorem intersectionRow_correct {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (q : Nat) (ha : (cells a).vertices < 2 ^ v)
    (hq : Nat.land q (cells a).vertices = q) :
    (intersectionRow R a q).testBit b.val = true ↔
      Nat.land (cells a).vertices (cells b).vertices = q := by
  rw [intersectionRow_pointwise]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < v
    · cases hbit : (cells a).vertices.testBit j with
      | false =>
        have hqbit := congrArg (fun mask => mask.testBit j) hq
        rw [testBit_land, hbit, Bool.and_false] at hqbit
        rw [testBit_land, hbit, Bool.false_and]
        exact hqbit
      | true =>
        rw [testBit_land, hbit, Bool.true_and]
        exact h ⟨j, hj⟩ hbit
    · have hpow : 2 ^ v ≤ 2 ^ j :=
        Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj)
      have hbit : (cells a).vertices.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hpow)
      have hqbit := congrArg (fun mask => mask.testBit j) hq
      rw [testBit_land, hbit, Bool.and_false] at hqbit
      rw [testBit_land, hbit, Bool.false_and]
      exact hqbit
  · intro h j hj
    have hbit := congrArg (fun mask => mask.testBit j.val) h
    simpa only [testBit_land, hj, Bool.true_and] using hbit

/-- Empty and singleton intersections are handled exactly; the other face
rows need only contain every literal listed edge and ridge. -/
def properRow {cells : Fin n → Cell} (R : Rows cells v) (q : Nat) : Nat :=
  if Nat.land q (q - 1) = 0 then allMask n else R.faces q

theorem properRow_complete {cells : Fin n → Cell} (R : Rows cells v)
    (b : Fin n) (q : Nat) (h : proper (cells b) q = true) :
    (properRow R q).testBit b.val = true := by
  by_cases hsmall : Nat.land q (q - 1) = 0
  · simp only [properRow, hsmall, ite_true, allMask_bit]
  · rw [properRow, ite_eq_right hsmall]
    obtain hhead | hridge := Bool.or_eq_true_iff.mp h
    · obtain hhead | hedge := Bool.or_eq_true_iff.mp hhead
      · exact False.elim (hsmall (of_decide_eq_true hhead))
      · obtain ⟨edge, he, heq⟩ := List.any_eq_true.mp hedge
        have heq := of_decide_eq_true heq
        exact heq ▸ R.edge_complete b edge he
    · obtain ⟨ridge, hr, heq⟩ := List.any_eq_true.mp hridge
      have heq := of_decide_eq_true heq
      exact heq ▸ R.ridge_complete b ridge hr

def badTerm {cells : Fin n → Cell} (R : Rows cells v) (a : Fin n) (q : Nat) : Nat :=
  Nat.land (intersectionRow R a q)
    (if proper (cells a) q then Nat.xor (allMask n) (properRow R q) else allMask n)

theorem badTerm_sound {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (q : Nat) (ha : (cells a).vertices < 2 ^ v)
    (hq : Nat.land q (cells a).vertices = q)
    (h : (badTerm R a q).testBit b.val = true) :
    compatible (cells a) (cells b) = false := by
  apply Bool.eq_false_of_ne_true
  intro hcompatible
  rw [badTerm, testBit_land] at h
  obtain ⟨hintersection, hbad⟩ := Bool.and_eq_true_iff.mp h
  have hcommon := (intersectionRow_correct R a b q ha hq).mp hintersection
  obtain ⟨hproper, _⟩ := Bool.and_eq_true_iff.mp hcompatible
  obtain ⟨hap, hbp⟩ := Bool.and_eq_true_iff.mp hproper
  change proper (cells a) (Nat.land (cells a).vertices (cells b).vertices) = true at hap
  change proper (cells b) (Nat.land (cells a).vertices (cells b).vertices) = true at hbp
  rw [hcommon] at hap hbp
  have hrow := properRow_complete R b q hbp
  change (if proper (cells a) q then
    Nat.xor (allMask n) (properRow R q) else allMask n).testBit b.val = true at hbad
  simp only [hap, ite_true] at hbad
  rw [testBit_xor, allMask_bit, hrow] at hbad
  exact Bool.noConfusion hbad

def incompatibleRow {cells : Fin n → Cell} (R : Rows cells v)
    (a : Fin n) (terms : List Nat) : Nat := unionValues (badTerm R a) terms

/-- This is exactly the one-sided soundness law required by
`BatchedGrowthPruning.Cache.incompatible_sound`. -/
theorem incompatibleRow_sound {cells : Fin n → Cell} (R : Rows cells v)
    (a b : Fin n) (terms : List Nat) (ha : (cells a).vertices < 2 ^ v)
    (hterms : ∀ q, q ∈ terms → Nat.land q (cells a).vertices = q)
    (h : bitAt (incompatibleRow R a terms) b.val = true) :
    compatible (cells a) (cells b) = false := by
  obtain ⟨q, hq, hterm⟩ := (bitAt_unionValues (badTerm R a) terms b.val).mp h
  exact badTerm_sound R a b q ha (hterms q hq)
    (by simpa only [bitAt_eq_testBit] using hterm)

#print axioms incompatibleRow_sound

end Papers.RationalityTen.IntersectionIncompatibilityRows
