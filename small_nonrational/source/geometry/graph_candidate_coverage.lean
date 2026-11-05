module
prelude
public import FiniteMaskSets

@[expose] public section

/-!
# Complete induced-graph candidate universes

The global vertex and edge incidence rows are checked once.  For any graph,
only one bitset exclusion per edge is then needed to compute its complete
candidate universe.  Equality with an emitted local embedding certifies both
its soundness and its completeness.
-/

namespace Papers.RationalityTen.GraphCandidateCoverage

open GrowthBitsets FiniteMaskSets

variable {n v e : Nat}

structure IncidenceRows (n v e : Nat) where
  first : Fin e → Fin v
  second : Fin e → Fin v
  vertices : Fin n → Nat
  edges : Fin n → Nat
  vertexRows : Fin v → Nat
  edgeRows : Fin e → Nat
  vertexRows_exact : ∀ a c,
    (vertexRows a).testBit c.val = (vertices c).testBit a.val
  edgeRows_exact : ∀ q c,
    (edgeRows q).testBit c.val = (edges c).testBit q.val

def withinRow (R : IncidenceRows n v e) (q : Fin e) : Nat :=
  Nat.land (R.vertexRows (R.first q)) (R.vertexRows (R.second q))

def excludedRow (R : IncidenceRows n v e) (complement : Nat) (q : Fin e) : Nat :=
  if complement.testBit q.val then R.edgeRows q
  else Nat.land (withinRow R q) (Nat.xor (allMask n) (R.edgeRows q))

def excludedMask (R : IncidenceRows n v e) (complement : Nat) : Nat :=
  unionValues (excludedRow R complement) (List.finRange e)

def eligibleMask (R : IncidenceRows n v e) (allowed complement : Nat) : Nat :=
  Nat.land allowed (Nat.xor (allMask n) (excludedMask R complement))

/-- Exact induced-edge equality, with no condition on how the global cells
were generated. -/
def Induced (R : IncidenceRows n v e) (complement : Nat) (c : Fin n) : Prop :=
  ∀ q, (R.edges c).testBit q.val =
    ((R.vertices c).testBit (R.first q).val &&
      (R.vertices c).testBit (R.second q).val && !complement.testBit q.val)

theorem testBit_xor (a b i : Nat) :
    (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := by
  exact Nat.testBit_xor a b i

theorem excludedRow_false_iff (R : IncidenceRows n v e)
    (complement : Nat) (q : Fin e) (c : Fin n)
    (hedge : (R.edges c).testBit q.val = true →
      (R.vertices c).testBit (R.first q).val = true ∧
        (R.vertices c).testBit (R.second q).val = true) :
    (excludedRow R complement q).testBit c.val = false ↔
      (R.edges c).testBit q.val =
        ((R.vertices c).testBit (R.first q).val &&
          (R.vertices c).testBit (R.second q).val && !complement.testBit q.val) := by
  cases hc : complement.testBit q.val <;>
    cases he : (R.edges c).testBit q.val <;>
    cases ha : (R.vertices c).testBit (R.first q).val <;>
    cases hb : (R.vertices c).testBit (R.second q).val <;>
    simp_all [excludedRow, withinRow, testBit_land, testBit_xor,
      allMask_bit c, R.vertexRows_exact, R.edgeRows_exact]

theorem excludedMask_false_iff (R : IncidenceRows n v e)
    (complement : Nat) (c : Fin n) :
    (excludedMask R complement).testBit c.val = false ↔
      ∀ q, (excludedRow R complement q).testBit c.val = false := by
  constructor
  · intro h q
    apply Bool.eq_false_of_ne_true
    intro hq
    have hh : (excludedMask R complement).testBit c.val = true := by
      exact (bitAt_eq_testBit _ _).symm.trans
        ((bitAt_unionValues _ _ _).mpr
          ⟨q, List.mem_finRange q, (bitAt_eq_testBit _ _).trans hq⟩)
    exact Bool.noConfusion (h.symm.trans hh)
  · intro h
    apply Bool.eq_false_of_ne_true
    intro hmask
    obtain ⟨q, _, hq⟩ := (bitAt_unionValues _ _ _).mp
      ((bitAt_eq_testBit _ _).trans hmask)
    have hh := (bitAt_eq_testBit _ _).symm.trans hq
    exact Bool.noConfusion ((h q).symm.trans hh)

theorem eligibleMask_bit_iff (R : IncidenceRows n v e)
    (allowed complement : Nat) (c : Fin n)
    (hedges : ∀ q, (R.edges c).testBit q.val = true →
      (R.vertices c).testBit (R.first q).val = true ∧
        (R.vertices c).testBit (R.second q).val = true) :
    (eligibleMask R allowed complement).testBit c.val = true ↔
      allowed.testBit c.val = true ∧ Induced R complement c := by
  have hxor : (true ^^ (excludedMask R complement).testBit c.val) = true ↔
      (excludedMask R complement).testBit c.val = false := by
    cases (excludedMask R complement).testBit c.val <;> decide
  simp only [eligibleMask, testBit_land, testBit_xor, allMask_bit c,
    Bool.and_eq_true_iff, hxor, excludedMask_false_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun q => (excludedRow_false_iff R complement q c (hedges q)).mp (h q)⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, fun q => (excludedRow_false_iff R complement q c (hedges q)).mpr (h q)⟩

/-- A single literal mask equality certifies the complete local candidate
list; it does not assume the search producer found all candidates. -/
theorem mem_embedding_iff (R : IncidenceRows n v e)
    (allowed complement : Nat) (embedding : List (Fin n))
    (hmask : eligibleMask R allowed complement = ofList embedding)
    (c : Fin n)
    (hedges : ∀ q, (R.edges c).testBit q.val = true →
      (R.vertices c).testBit (R.first q).val = true ∧
        (R.vertices c).testBit (R.second q).val = true) :
    c ∈ embedding ↔ allowed.testBit c.val = true ∧ Induced R complement c := by
  rw [← bitAt_ofList, bitAt_eq_testBit, ← hmask]
  exact eligibleMask_bit_iff R allowed complement c hedges

#print axioms mem_embedding_iff

end Papers.RationalityTen.GraphCandidateCoverage
