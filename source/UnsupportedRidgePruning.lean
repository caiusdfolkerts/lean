module
prelude
public import BatchedGrowthPruning
public import PrimitiveBitsetGrowth

@[expose] public section

/-!
# Removing cells whose ridge has no possible second owner

The certificate records each removed cell and one of its ridges.  At that
step every possible second owner is already excluded, while the ridge has no
selected owner.  A target has two owners at every ridge, so the removed cell
cannot belong to any target extension.  Iterating these elementary deductions
is a checked propagation rule, not a producer-side heuristic assumption.
-/

namespace Papers.RationalityTen.UnsupportedRidgePruning

open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming ConcreteGrowth
open GrowthBitsets BatchedGrowthPruning

variable {n r : Nat}

structure Removal (n r : Nat) where
  cell : Fin n
  ridge : Fin r

def stepCheck {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected blocked : Nat)
    (w : Removal n r) : Bool :=
  ((cache.candidates w.ridge).testBit w.cell.val &&
    decide (Nat.land selected (cache.candidates w.ridge) = 0)) &&
    decide (Nat.land (cache.candidates w.ridge)
      (Nat.lor blocked (PrimitiveBitsetGrowth.singleton w.cell.val)) =
        cache.candidates w.ridge)

theorem step_excludes {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (S B : List (Fin n))
    (selected blocked : Nat) (hselected : selected = ofList S)
    (hblocked : ∀ c, family B c = true → family S c = false → bitAt blocked c.val = false)
    (hmates : HasMate (fun c => has (ridgeList c)) (family B))
    (w : Removal n r) (hcheck : stepCheck cache selected blocked w = true) :
    family B w.cell = false := by
  obtain ⟨hfirst, hcover⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hinc, hempty⟩ := Bool.and_eq_true_iff.mp hfirst
  have hinc' : has (ridgeList w.cell) w.ridge = true := by
    rw [← cache.candidates_exact, bitAt_eq_testBit]
    exact hinc
  cases hcell : family B w.cell with
  | false => rfl
  | true =>
    obtain ⟨d, ⟨hdB, hdr⟩, hne⟩ := hmates w.ridge w.cell ⟨hcell, hinc'⟩
    change has (ridgeList d) w.ridge = true at hdr
    have hdS : family S d = false := by
      have heq := congrArg (fun bits => bitAt bits d.val) (of_decide_eq_true hempty)
      rw [bitAt_and, hselected, bitAt_ofList_eq_has,
        cache.candidates_exact, hdr, bitAt_zero, Bool.and_true] at heq
      exact heq
    have hdblocked := hblocked d hdB hdS
    have hdnotpower : bitAt (PrimitiveBitsetGrowth.singleton w.cell.val) d.val = false := by
      rw [PrimitiveBitsetGrowth.singleton_eq, bitAt_power]
      apply decide_eq_false
      intro hval
      exact hne (Fin.ext hval.symm)
    have heq := congrArg (fun bits => bitAt bits d.val) (of_decide_eq_true hcover)
    rw [bitAt_and, bitAt_or, hdblocked, hdnotpower,
      cache.candidates_exact, hdr] at heq
    exact False.elim (Bool.noConfusion heq)

def resultingMask (blocked : Nat) : List (Removal n r) → Nat
  | [] => blocked
  | w :: rest => resultingMask
      (Nat.lor blocked (PrimitiveBitsetGrowth.singleton w.cell.val)) rest

def checks {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (selected blocked : Nat) :
    List (Removal n r) → Bool
  | [] => true
  | w :: rest => stepCheck cache selected blocked w &&
      checks cache selected (Nat.lor blocked (PrimitiveBitsetGrowth.singleton w.cell.val)) rest

/-- Every sequentially checked deletion preserves the missing cells of every
paired target.  The final exclusion mask can therefore replace the initial
mask in the exhaustive branch-coverage equation. -/
theorem checks_sound {ridgeList : Fin n → List (Fin r)}
    {compatible : Fin n → Fin n → Bool} {kind : Fin n → Nat}
    (cache : Cache ridgeList compatible kind) (S B : List (Fin n))
    (selected blocked : Nat) (hselected : selected = ofList S)
    (hblocked : ∀ c, family B c = true → family S c = false → bitAt blocked c.val = false)
    (hmates : HasMate (fun c => has (ridgeList c)) (family B))
    (removals : List (Removal n r)) (hcheck : checks cache selected blocked removals = true) :
    ∀ c, family B c = true → family S c = false →
      bitAt (resultingMask blocked removals) c.val = false := by
  induction removals generalizing blocked with
  | nil => exact hblocked
  | cons w rest ih =>
    obtain ⟨hstep, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
    have hw := step_excludes cache S B selected blocked hselected hblocked hmates w hstep
    apply ih _ ?_ hrest
    intro c hcB hcS
    have hne : c.val ≠ w.cell.val := by
      intro heq
      have hcw : c = w.cell := Fin.ext heq
      rw [hcw, hw] at hcB
      exact Bool.noConfusion hcB
    rw [bitAt_or, hblocked c hcB hcS, PrimitiveBitsetGrowth.singleton_eq,
      bitAt_power, decide_eq_false (Ne.symm hne)]
    rfl

#print axioms checks_sound

end Papers.RationalityTen.UnsupportedRidgePruning
