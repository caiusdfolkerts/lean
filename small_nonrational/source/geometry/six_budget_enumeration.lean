module
prelude
public import Init.Data.List.Nat.Range
public import Init.Data.List.Nat.Sum
public import Init.Data.List.Lemmas
public import Init.Omega

@[expose] public section

noncomputable section

/-!
# The complete numerical six-vertex-facet budget

The seven entries of `types` count all seven combinatorial types of a
six-vertex three-polytope.  In the literal polygon catalogue, type 4 is the
pentagonal pyramid and type 6 is the triangular prism.  No type is omitted.

The enumerator uses weak compositions, rather than a Cartesian product of
seven independent counts.  Its completeness theorem applies to arbitrary
natural parameters satisfying the geometric inequalities.  A separate,
kernel-reduced certificate identifies its finite output with the literal
478-row catalogue used to generate the boundary searches.
-/

namespace Papers.RationalityTen.SixBudgetEnumeration

/-- All lists of `length` nonnegative integers whose sum is `total`. -/
def compositions : Nat → Nat → List (List Nat)
  | 0, total => if total = 0 then [[]] else []
  | length + 1, total =>
      (List.range (total + 1)).flatMap fun first =>
        (compositions length (total - first)).map (first :: ·)

theorem mem_compositions (xs : List Nat) (length total : Nat)
    (hlength : xs.length = length) (hsum : xs.sum = total) :
    xs ∈ compositions length total := by
  induction length generalizing xs total with
  | zero =>
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero hlength
      subst xs
      have ht : total = 0 := by simpa using hsum.symm
      subst total
      simp [compositions]
  | succ length ih =>
      cases xs with
      | nil => simp at hlength
      | cons first rest =>
          have hlen : rest.length = length := by simpa using hlength
          have htotal : first + rest.sum = total := by simpa using hsum
          have hfirst : first < total + 1 := by omega
          have hrest : rest.sum = total - first := by omega
          apply List.mem_flatMap.mpr
          refine ⟨first, List.mem_range.mpr hfirst, ?_⟩
          exact List.mem_map.mpr ⟨rest, ih rest _ hlen hrest, rfl⟩

structure Row where
  m : Nat
  E : Nat
  q : Nat
  types : List Nat
  deriving DecidableEq, Repr

namespace Row

def L (B : Row) : Nat := B.types.sum
def t (B : Row) : Nat := B.types.getD 6 0
def p (B : Row) : Nat := B.types.getD 4 0 / 2
def quadTotal (B : Row) : Nat :=
  B.types.getD 1 0 + B.types.getD 3 0 +
    2 * B.types.getD 5 0 + 3 * B.types.getD 6 0
def SP (B : Row) : Nat := 2 * B.q - B.quadTotal
def BP (B : Row) : Nat := B.E - 2 * B.L - B.SP
def T (B : Row) : Nat := B.m + B.L - B.E

/-- Necessary intrinsic inequalities and the exact local polygon profiles.
The inequalities involving `quadTotal` ensure that no truncated subtraction
silently admits a negative square-pyramid or bipyramid count. -/
def Admissible (B : Row) : Prop :=
  B.types.length = 7 ∧
  10 ≤ B.m ∧ 1 ≤ B.L ∧ B.L + 10 ≤ B.E ∧
  B.E ≤ B.m + B.L ∧ B.m + B.E ≤ 26 ∧ B.t ≤ B.L ∧
  B.types.getD 4 0 = 2 * B.p ∧
  B.quadTotal ≤ 2 * B.q ∧ B.SP + 2 * B.L ≤ B.E ∧
  B.q + 2 * B.p + 9 ≤ B.E + B.t ∧
  2 * B.E + B.m + B.L ≤ 35 + B.q + 3 * B.p

instance (B : Row) : Decidable B.Admissible := by
  unfold Admissible
  infer_instance

theorem parameter_bounds (B : Row) (h : B.Admissible) :
    1 ≤ B.L ∧ B.L < 7 ∧ 10 ≤ B.m ∧ B.m < 10 + (7 - B.L) ∧
      B.L + 10 ≤ B.E ∧ B.E < (B.L + 10) + (17 - B.L - B.m) ∧
      B.q < 17 := by
  rcases h with ⟨_, hm, hL, hEL, hE, hmE, ht, _, _, _, hq, _⟩
  omega

/-- A cheap consequence of the allocation inequality, used before expanding
the ranges of `m`, `E`, and `q`.  This is a proved necessary condition. -/
theorem type_bound (B : Row) (h : B.Admissible) :
    7 * B.L ≤ 20 + B.quadTotal + 6 * B.p := by
  rcases h with ⟨_, hm, hL, hEL, hE, hmE, ht, hp, hquad, hSP, hq, halloc⟩
  unfold SP at hSP
  omega

end Row

/-- All admissible numerical rows with the given complete seven-type list. -/
def rowsForTypes (L : Nat) (types : List Nat) : List Row :=
  ((List.range' 10 (7 - L)).flatMap fun m =>
    (List.range' (L + 10) (17 - L - m)).flatMap fun E =>
      (List.range 17).map fun q => Row.mk m E q types).filter fun B => decide B.Admissible

def eligibleTypes (L : Nat) (types : List Nat) : Bool :=
  let B : Row := ⟨0, 0, 0, types⟩
  decide (types.getD 4 0 = 2 * B.p ∧ 7 * L ≤ 20 + B.quadTotal + 6 * B.p)

def typeLists (L : Nat) : List (List Nat) :=
  (compositions 7 L).filter (eligibleTypes L)

def rowsForTotal (L : Nat) : List Row :=
  (typeLists L).flatMap (rowsForTypes L)

def enumeratedRows : List Row :=
  (List.range' 1 6).flatMap rowsForTotal

theorem mem_rowsForTypes (B : Row) (h : B.Admissible) :
    B ∈ rowsForTypes B.L B.types := by
  have hb := B.parameter_bounds h
  apply List.mem_filter.mpr
  refine ⟨?_, decide_eq_true h⟩
  apply List.mem_flatMap.mpr
  refine ⟨B.m, List.mem_range'_1.mpr ⟨hb.2.2.1, hb.2.2.2.1⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨B.E, List.mem_range'_1.mpr ⟨hb.2.2.2.2.1, hb.2.2.2.2.2.1⟩, ?_⟩
  exact List.mem_map.mpr ⟨B.q, List.mem_range.mpr hb.2.2.2.2.2.2, rfl⟩

/-- Every admissible numerical budget occurs in the finite enumerator. -/
theorem enumerated_complete (B : Row) (h : B.Admissible) : B ∈ enumeratedRows := by
  have hb := B.parameter_bounds h
  apply List.mem_flatMap.mpr
  refine ⟨B.L, List.mem_range'_1.mpr ⟨hb.1, hb.2.1⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨B.types, List.mem_filter.mpr ⟨mem_compositions B.types 7 B.L h.1 rfl, ?_⟩, ?_⟩
  · apply decide_eq_true
    exact ⟨h.2.2.2.2.2.2.2.1, B.type_bound h⟩
  exact mem_rowsForTypes B h

#print axioms enumerated_complete

end Papers.RationalityTen.SixBudgetEnumeration
