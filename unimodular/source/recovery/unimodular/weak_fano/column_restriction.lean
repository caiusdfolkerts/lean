module

public import Recovery.Unimodular.WeakFano.EffectiveBinaryMoves

@[expose] public section

set_option autoImplicit false

namespace Unimodular.ColumnRestriction

variable {I M : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup M] [DecidableEq M] (p : I → Prop) [DecidablePred p]

/-- Literal deletion of columns is implemented by extension by zero. -/
def extend : ({i // p i} → ℤ) →+ (I → ℤ) where
  toFun c i := if hi : p i then c ⟨i, hi⟩ else 0
  map_zero' := by ext i; by_cases hi : p i <;> simp [hi]
  map_add' c d := by ext i; by_cases hi : p i <;> simp [hi]

/-- Restriction retains exactly the selected coordinates. -/
def restrict : (I → ℤ) →+ ({i // p i} → ℤ) where
  toFun c i := c i.val
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem extend_apply (c : {i // p i} → ℤ) (i : I) :
    extend p c i = if hi : p i then c ⟨i, hi⟩ else 0 := rfl

@[simp] theorem extend_subtype (c : {i // p i} → ℤ) (i : {i // p i}) :
    extend p c i.val = c i := by simp [i.property]

@[simp] theorem restrict_apply (c : I → ℤ) (i : {i // p i}) :
    restrict p c i = c i.val := rfl

@[simp] theorem restrict_extend (c : {i // p i} → ℤ) : restrict p (extend p c) = c := by
  ext i
  exact extend_subtype p c i

theorem extend_injective : Function.Injective (extend p) := by
  intro c d h
  simpa only [restrict_extend] using congrArg (restrict p) h

theorem extend_restrict (c : I → ℤ) (hc : ∀ i, ¬p i → c i = 0) :
    extend p (restrict p c) = c := by
  ext i
  by_cases hi : p i
  · simp [hi]
  · simp [hi, hc i hi]

/-- The actual restricted matrix is the original map composed with the
explicit column inclusion. -/
def equation (A : (I → ℤ) →+ M) : ({i // p i} → ℤ) →+ M := A.comp (extend p)

@[simp] theorem equation_apply (A : (I → ℤ) →+ M) (c : {i // p i} → ℤ) :
    equation p A c = A (extend p c) := rfl

theorem extend_conformal_iff (g h : {i // p i} → ℤ) :
    Graver.ConformalLE (extend p g) (extend p h) ↔ Graver.ConformalLE g h := by
  constructor
  · intro hgh i
    simpa only [extend_subtype] using hgh i.val
  · intro hgh i
    by_cases hi : p i
    · simpa [hi] using hgh ⟨i, hi⟩
    · simp [hi]

theorem conformal_supported {g : {i // p i} → ℤ} {h : I → ℤ}
    (hh : Graver.ConformalLE h (extend p g)) : ∀ i, ¬p i → h i = 0 := by
  intro i hi
  have hc := (Graver.conformalLE_iff h (extend p g)).1 hh i
  simp only [extend_apply, dif_neg hi] at hc
  omega

/-- Primitive replacements for the deleted-column matrix are exactly the
original primitive replacements supported in those columns. This prevents
an unverified change of meaning of primitivehood after restriction. -/
theorem primitive_extend_iff (A : (I → ℤ) →+ M) (g : {i // p i} → ℤ) :
    Graver.Primitive A.ker (extend p g) ↔ Graver.Primitive (equation p A).ker g := by
  constructor
  · rintro ⟨hgA, hg0, hgmin⟩
    refine ⟨hgA, ?_, ?_⟩
    · intro he
      apply hg0
      rw [he, map_zero]
    · intro h hhA hh0 hhg
      have hex0 : extend p h ≠ 0 := by
        intro hz
        apply hh0
        apply extend_injective p
        simpa only [map_zero] using hz
      exact extend_injective p
        (hgmin (extend p h) hhA hex0 ((extend_conformal_iff p h g).2 hhg))
  · rintro ⟨hgA, hg0, hgmin⟩
    refine ⟨hgA, ?_, ?_⟩
    · intro he
      apply hg0
      have h := congrArg (restrict p) he
      simpa only [restrict_extend, map_zero] using h
    · intro h hhA hh0 hhg
      have hs : extend p (restrict p h) = h := extend_restrict p h (conformal_supported p hhg)
      have hrA : restrict p h ∈ (equation p A).ker := by
        change A (extend p (restrict p h)) = 0
        rw [hs]
        exact hhA
      have hr0 : restrict p h ≠ 0 := by
        intro hz
        apply hh0
        rw [← hs, hz, map_zero]
      have hrconf : Graver.ConformalLE (restrict p h) g := by
        apply (extend_conformal_iff p _ _).1
        rwa [hs]
      have hr := hgmin (restrict p h) hrA hr0 hrconf
      rw [← hs, hr]

theorem extend_binary_iff (c : {i // p i} → ℤ) :
    extend p c ∈ EffectiveBinaryMoves.binaryCube ↔ c ∈ EffectiveBinaryMoves.binaryCube := by
  rw [EffectiveBinaryMoves.mem_binaryCube, EffectiveBinaryMoves.mem_binaryCube]
  constructor
  · intro h i
    simpa only [extend_subtype] using h i.val
  · intro h i
    by_cases hi : p i
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi]

theorem extend_moveCube_iff (g : {i // p i} → ℤ) :
    extend p g ∈ EffectiveBinaryMoves.moveCube ↔ g ∈ EffectiveBinaryMoves.moveCube := by
  rw [EffectiveBinaryMoves.mem_moveCube, EffectiveBinaryMoves.mem_moveCube]
  constructor
  · intro h i
    simpa only [extend_subtype] using h i.val
  · intro h i
    by_cases hi : p i
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi]

theorem extend_mem_moves_iff (A : (I → ℤ) →+ M) (g : {i // p i} → ℤ) :
    extend p g ∈ EffectiveBinaryMoves.moves A ↔
      g ∈ EffectiveBinaryMoves.moves (equation p A) := by
  simp only [EffectiveBinaryMoves.mem_moves, extend_moveCube_iff, primitive_extend_iff]

theorem extend_mem_solutions_iff (A : (I → ℤ) →+ M) (b : M) (c : {i // p i} → ℤ) :
    extend p c ∈ EffectiveBinaryMoves.solutions A b ↔
      c ∈ EffectiveBinaryMoves.solutions (equation p A) b := by
  constructor
  · intro h
    have he := (EffectiveBinaryMoves.mem_solutions A b (extend p c)).1 h
    apply (EffectiveBinaryMoves.mem_solutions (equation p A) b c).2
    exact ⟨(EffectiveBinaryMoves.mem_binaryCube c).1
      ((extend_binary_iff p c).1 ((EffectiveBinaryMoves.mem_binaryCube _).2 he.1)), he.2⟩
  · intro h
    have he := (EffectiveBinaryMoves.mem_solutions (equation p A) b c).1 h
    apply (EffectiveBinaryMoves.mem_solutions A b (extend p c)).2
    exact ⟨(EffectiveBinaryMoves.mem_binaryCube _).1
      ((extend_binary_iff p c).2 ((EffectiveBinaryMoves.mem_binaryCube c).2 he.1)), he.2⟩

theorem extend_between {c d x : {i // p i} → ℤ} (hx : Graver.Between c d x) :
    Graver.Between (extend p c) (extend p d) (extend p x) := by
  intro i
  by_cases hi : p i
  · simpa [hi] using hx ⟨i, hi⟩
  · simp [hi]

/-- The finite computed graph after column deletion is complete for every
binary fiber of the restricted matrix; its extended moves are genuine
primitive replacements of the full matrix. -/
theorem restricted_connectivity (A : (I → ℤ) →+ M) (b : M)
    (c d : {i // p i} → ℤ)
    (hc : c ∈ EffectiveBinaryMoves.solutions (equation p A) b)
    (hd : d ∈ EffectiveBinaryMoves.solutions (equation p A) b) :
    Relation.ReflTransGen
      (fun x y : {i // p i} → ℤ =>
        y - x ∈ EffectiveBinaryMoves.moves (equation p A) ∧
        Graver.Primitive A.ker (extend p (y - x)) ∧
        x ∈ EffectiveBinaryMoves.solutions (equation p A) b ∧
        y ∈ EffectiveBinaryMoves.solutions (equation p A) b ∧
        Graver.Between c d x ∧ Graver.Between c d y) c d := by
  have h := EffectiveBinaryMoves.connectivity (equation p A) b c d hc hd
  apply Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ h
  exact ⟨hxy.1, (primitive_extend_iff p A _).2
    ((EffectiveBinaryMoves.mem_moves _ _).1 hxy.1).2, hxy.2⟩

end Unimodular.ColumnRestriction

#print axioms Unimodular.ColumnRestriction.primitive_extend_iff
#print axioms Unimodular.ColumnRestriction.extend_mem_moves_iff
#print axioms Unimodular.ColumnRestriction.restricted_connectivity
#check Unimodular.ColumnRestriction.restricted_connectivity
