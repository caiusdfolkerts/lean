module

public import PaperVerification.AlternatingFormsBoolean
public import PaperVerification.AlternatingFormsEvenWalkPartition
public import Mathlib.Data.Nat.Find

/-!
# Boolean good subsets and actual strip walks

A selected position is a downward step.  Both strip inequalities are
expressed without truncated subtraction.  A failed inequality supplies an
odd prefix containing a strict majority of selected positions, either in
the original order or in the reversed order.  This is the prefix on which
the central Boolean inverse applies.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.BooleanWalks

variable {m q : ℕ}

def prefixCount (S : Finset (Fin m)) (r : ℕ) : ℕ :=
  (S.filter fun i ↦ i.val < r).card

@[simp] theorem prefixCount_zero (S : Finset (Fin m)) : prefixCount S 0 = 0 := by
  simp [prefixCount]

theorem prefixCount_all (S : Finset (Fin m)) (r : ℕ) (hr : m ≤ r) :
    prefixCount S r = S.card := by
  unfold prefixCount
  congr 1
  exact Finset.filter_true_of_mem (fun i hi ↦ lt_of_lt_of_le i.isLt hr)

theorem prefixCount_le (S : Finset (Fin m)) (r : ℕ) : prefixCount S r ≤ S.card :=
  Finset.card_filter_le _ _

def selectedAt (S : Finset (Fin m)) (r : ℕ) : ℕ :=
  if ∃ i ∈ S, i.val = r then 1 else 0

theorem selectedAt_le_one (S : Finset (Fin m)) (r : ℕ) : selectedAt S r ≤ 1 := by
  unfold selectedAt
  split_ifs <;> omega

theorem prefixCount_succ (S : Finset (Fin m)) (r : ℕ) :
    prefixCount S (r+1) = prefixCount S r + selectedAt S r := by
  by_cases h : ∃ i ∈ S, i.val = r
  · obtain ⟨i, hi, rfl⟩ := h
    have hf : (S.filter fun j ↦ j.val < i.val+1) =
        insert i (S.filter fun j ↦ j.val < i.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hj, hji⟩
        by_cases he : j = i
        · exact Or.inl he
        · exact Or.inr ⟨hj, by have hne : j.val ≠ i.val := fun h ↦ he (Fin.ext h); omega⟩
      · rintro (rfl | ⟨hj, hji⟩)
        · exact ⟨hi, Nat.lt_succ_self _⟩
        · exact ⟨hj, by omega⟩
    have hn : i ∉ S.filter (fun j ↦ j.val < i.val) := by simp
    simp only [prefixCount, hf, Finset.card_insert_of_notMem hn]
    have hsel : ∃ j ∈ S, j.val = i.val := ⟨i, hi, rfl⟩
    simp [selectedAt, hsel]
  · have hf : (S.filter fun j ↦ j.val < r+1) =
        (S.filter fun j ↦ j.val < r) := by
      ext j
      simp only [Finset.mem_filter]
      have hn : j ∈ S → j.val ≠ r := fun hj he ↦ h ⟨j, hj, he⟩
      constructor <;> rintro ⟨hj, hlt⟩ <;> exact ⟨hj, by have := hn hj; omega⟩
    simp only [prefixCount, hf, selectedAt, if_neg h, Nat.add_zero]

@[simp] theorem selectedAt_position (S : Finset (Fin m)) (i : Fin m) :
    selectedAt S i.val = if i ∈ S then 1 else 0 := by
  have h : (∃ j ∈ S, j.val = i.val) ↔ i ∈ S := by
    constructor
    · rintro ⟨j, hj, he⟩
      exact (Fin.ext he) ▸ hj
    · intro hi
      exact ⟨i, hi, rfl⟩
  simp only [selectedAt, h]

def reverse (S : Finset (Fin m)) : Finset (Fin m) := S.image Fin.rev

@[simp] theorem reverse_card (S : Finset (Fin m)) : (reverse S).card = S.card := by
  exact Finset.card_image_of_injective _ (fun i j h ↦ Fin.rev_inj.mp h)

@[simp] theorem reverse_reverse (S : Finset (Fin m)) : reverse (reverse S) = S := by
  simp [reverse, Finset.image_image, Function.comp_def]

theorem prefixCount_reverse (S : Finset (Fin m)) (r : ℕ) (hr : r ≤ m) :
    prefixCount S r + prefixCount (reverse S) (m-r) = S.card := by
  have hf : ((reverse S).filter fun i ↦ i.val < m-r) =
      (S.filter fun i ↦ ¬i.val < r).image Fin.rev := by
    rw [reverse, Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro i hi
    have hi' := i.isLt
    simp only [Fin.val_rev]
    omega
  unfold prefixCount
  rw [hf, Finset.card_image_of_injective _ (fun i j h ↦ Fin.rev_inj.mp h)]
  exact Finset.card_filter_add_card_filter_not (fun i : Fin m ↦ i.val < r)

/-- The exact two wall inequalities for a Boolean monomial of degree q. -/
def Good (S : FixedSubsets (Fin m) q) : Prop :=
  ∀ r, r ≤ m → 2*prefixCount S.val r ≤ r ∧
    r+2*q ≤ m+2*prefixCount S.val r

abbrev GoodSubset (m q : ℕ) := {S : FixedSubsets (Fin m) q // Good S}

instance goodSubsetFintype (m q : ℕ) : Fintype (GoodSubset m q) := Fintype.ofFinite _

/-- The ordinary nonnegative height of the walk attached to a good subset. -/
def height (S : GoodSubset m q) (r : ℕ) : ℕ := r - 2*prefixCount S.val.val r

@[simp] theorem height_zero (S : GoodSubset m q) : height S 0 = 0 := by
  simp [height]

theorem good_degree_bound (S : GoodSubset m q) : 2*q ≤ m := by
  have h := (S.property m le_rfl).1
  rw [prefixCount_all _ _ le_rfl, S.val.property] at h
  exact h

theorem height_final (S : GoodSubset m q) : height S m = m-2*q := by
  rw [height, prefixCount_all _ _ le_rfl, S.val.property]

theorem height_bound (S : GoodSubset m q) (r : ℕ) (hr : r ≤ m) :
    height S r ≤ m-2*q := by
  have h := S.property r hr
  have hq := good_degree_bound S
  unfold height
  omega

theorem height_step (S : GoodSubset m q) (r : ℕ) (hr : r < m) :
    EvenWalkPartition.UnitStep (height S) r := by
  have h₀ := (S.property r (by omega)).1
  have h₁ := (S.property (r+1) (by omega)).1
  have hc := prefixCount_succ S.val.val r
  have hδ := selectedAt_le_one S.val.val r
  unfold EvenWalkPartition.UnitStep height
  omega

theorem height_downward_iff (S : GoodSubset m q) (i : Fin m) :
    height S (i.val+1)+1 = height S i.val ↔ i ∈ S.val.val := by
  have h₀ := (S.property i.val (by omega)).1
  have h₁ := (S.property (i.val+1) (by omega)).1
  change (i.val+1 - 2*prefixCount S.val.val (i.val+1))+1 =
    i.val - 2*prefixCount S.val.val i.val ↔ i ∈ S.val.val
  rw [prefixCount_succ, selectedAt_position] at h₁ ⊢
  by_cases hi : i ∈ S.val.val
  · simp only [if_pos hi] at h₁ ⊢
    constructor
    · intro _; exact hi
    · intro _; omega
  · simp only [if_neg hi, Nat.add_zero] at h₁ ⊢
    constructor
    · intro he; omega
    · intro h; exact False.elim (hi h)

theorem goodSubset_ext_of_downward (S T : GoodSubset m q)
    (h : ∀ i : Fin m,
      (height S (i.val+1)+1 = height S i.val) ↔
        (height T (i.val+1)+1 = height T i.val)) : S = T := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  exact (height_downward_iff S i).symm.trans ((h i).trans (height_downward_iff T i))

/-- The first lower-wall crossing has an odd length and a strict majority.
No assumption on the total degree or the width is needed for this fact. -/
theorem lower_failure_has_central_prefix (S : Finset (Fin m))
    (hbad : ∃ r, r ≤ m ∧ r < 2*prefixCount S r) :
    ∃ h, 2*h+1 ≤ m ∧ prefixCount S (2*h+1) = h+1 := by
  let r := Nat.find hbad
  have hr : r ≤ m ∧ r < 2*prefixCount S r := Nat.find_spec hbad
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    have h := hr.2
    rw [hz, prefixCount_zero] at h
    omega
  have hmin : ¬(r-1 ≤ m ∧ r-1 < 2*prefixCount S (r-1)) :=
    Nat.find_min hbad (by dsimp only [r] at *; omega)
  have hpre : 2*prefixCount S (r-1) ≤ r-1 := by omega
  have hsucc := prefixCount_succ S (r-1)
  rw [show r-1+1=r by omega] at hsucc
  have hδ := selectedAt_le_one S (r-1)
  refine ⟨prefixCount S (r-1), ?_, ?_⟩
  · omega
  · have he : 2*prefixCount S (r-1)+1 = r := by omega
    rw [he]
    omega

/-- Every bad monomial admits one of the two local inverses.  The right
wall is the left wall after reversing all positions. -/
theorem bad_has_central_prefix (S : FixedSubsets (Fin m) q) (hbad : ¬Good S) :
    (∃ h, 2*h+1 ≤ m ∧ prefixCount S.val (2*h+1) = h+1) ∨
      (∃ h, 2*h+1 ≤ m ∧ prefixCount (reverse S.val) (2*h+1) = h+1) := by
  by_cases hl : ∃ r, r ≤ m ∧ r < 2*prefixCount S.val r
  · exact Or.inl (lower_failure_has_central_prefix S.val hl)
  · right
    apply lower_failure_has_central_prefix
    by_contra hr
    apply hbad
    intro r hle
    constructor
    · exact Nat.le_of_not_gt (fun h ↦ hl ⟨r, hle, h⟩)
    · have hsum := prefixCount_reverse S.val r hle
      rw [S.property] at hsum
      have hrev : 2*prefixCount (reverse S.val) (m-r) ≤ m-r :=
        Nat.le_of_not_gt (fun h ↦ hr ⟨m-r, by omega, h⟩)
      omega

end PaperVerification.AlternatingForms.BooleanWalks
