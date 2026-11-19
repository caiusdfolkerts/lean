module
prelude
public import FiniteChecks
public import GrowthBitsets

@[expose] public section

/-!
# Pure mask computations for complete facet-embedding certificates

All large literal checks use only natural numbers and lists. The separate
semantic bridge proves that these computations transport the complete
vertex, edge, and ridge families of a template. No executable evaluator is
used as a proof rule.
-/

namespace Papers.RationalityTen.RawFacetEmbedding

open ConcreteGrowth GrowthBitsets

/-- Falling-factorial decoding, using natural coordinates during replay. -/
def decode (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, code, i =>
      let a := code % n
      if i = 0 then a else
        let j := decode (n - 1) k (code / n) (i - 1)
        if j < a then j else j + 1

def mapMask (size : Nat) (f : Nat → Nat) (mask : Nat) : Nat :=
  unionValues (fun i => if mask.testBit i then 2 ^ f i else 0) (List.range size)

def mapCell (size : Nat) (f : Nat → Nat) (cell : Cell) : Cell where
  kind := cell.kind
  vertices := mapMask size f cell.vertices
  edges := cell.edges.map (mapMask size f)
  ridgeMasks := cell.ridgeMasks.map (mapMask size f)

/-- Set equality of lists, independent of their chosen enumeration order. -/
def sameMembers (left right : List Nat) : Bool :=
  left.all (hasMask right) && right.all (hasMask left)

def sameGeometry (left right : Cell) : Bool :=
  decide (left.vertices = right.vertices) &&
    sameMembers left.edges right.edges && sameMembers left.ridgeMasks right.ridgeMasks

def embeddingCheck {count : Nat} (size : Nat) (template : Cell)
    (cells : Fin count → Cell) (code : Nat) (witness : Fin count) : Bool :=
  sameGeometry (cells witness) (mapCell size (decode 10 size code) template)

def wellFormedCheck (cell : Cell) : Bool :=
  decide (cell.vertices < 1024) &&
    cell.edges.all (fun edge => decide (edge < 1024)) &&
    cell.ridgeMasks.all (fun ridge => decide (ridge < 1024)) &&
    decide (cell.edges.Pairwise (fun a b => a < b))

theorem hasMask_iff (xs : List Nat) (i : Nat) : hasMask xs i = true ↔ i ∈ xs := by
  simp only [hasMask, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem sameMembers_iff (left right : List Nat) :
    sameMembers left right = true ↔ ∀ i, i ∈ left ↔ i ∈ right := by
  rw [sameMembers, Bool.and_eq_true_iff]
  constructor
  · rintro ⟨hleft, hright⟩ i
    exact ⟨fun hi => (hasMask_iff right i).mp (List.all_eq_true.mp hleft i hi),
      fun hi => (hasMask_iff left i).mp (List.all_eq_true.mp hright i hi)⟩
  · intro h
    constructor
    · exact List.all_eq_true.mpr fun i hi => (hasMask_iff right i).mpr ((h i).mp hi)
    · exact List.all_eq_true.mpr fun i hi => (hasMask_iff left i).mpr ((h i).mpr hi)

theorem sameGeometry_sound {left right : Cell} (h : sameGeometry left right = true) :
    left.vertices = right.vertices ∧
      (∀ i, i ∈ left.edges ↔ i ∈ right.edges) ∧
      (∀ i, i ∈ left.ridgeMasks ↔ i ∈ right.ridgeMasks) := by
  obtain ⟨hfirst, hridges⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hvertices, hedges⟩ := Bool.and_eq_true_iff.mp hfirst
  exact ⟨of_decide_eq_true hvertices, (sameMembers_iff _ _).mp hedges,
    (sameMembers_iff _ _).mp hridges⟩

theorem mapMask_bit (size : Nat) (f : Nat → Nat) (mask i : Nat) :
    (mapMask size f mask).testBit i = true ↔
      ∃ j, j < size ∧ mask.testBit j = true ∧ f j = i := by
  rw [mapMask, ← bitAt_eq_testBit, bitAt_unionValues]
  constructor
  · rintro ⟨j, hj, hbit⟩
    have hmem : mask.testBit j = true := by
      cases hm : mask.testBit j
      · simp only [hm, Bool.false_eq_true, ite_false, bitAt_zero] at hbit
      · rfl
    rw [hmem, ite_eq_left rfl, bitAt_power] at hbit
    exact ⟨j, List.mem_range.mp hj, hmem, of_decide_eq_true hbit⟩
  · rintro ⟨j, hj, hm, hji⟩
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [hm, ite_eq_left rfl, bitAt_power]
    exact decide_eq_true hji

theorem wellFormedCheck_sound (cell : Cell) (h : wellFormedCheck cell = true) :
    cell.vertices < 1024 ∧ (∀ e ∈ cell.edges, e < 1024) ∧
      (∀ q ∈ cell.ridgeMasks, q < 1024) ∧ cell.edges.Pairwise (fun a b => a < b) := by
  obtain ⟨hfirst, hsorted⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hfirst, hridges⟩ := Bool.and_eq_true_iff.mp hfirst
  obtain ⟨hvertices, hedges⟩ := Bool.and_eq_true_iff.mp hfirst
  refine ⟨of_decide_eq_true hvertices, ?_, ?_, of_decide_eq_true hsorted⟩
  · intro e he
    exact of_decide_eq_true (List.all_eq_true.mp hedges e he)
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp hridges q hq)

end Papers.RationalityTen.RawFacetEmbedding
