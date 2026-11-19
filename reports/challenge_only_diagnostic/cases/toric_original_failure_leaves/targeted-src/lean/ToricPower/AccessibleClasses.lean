module

public import ToricPower.ThomsenClasses

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

def shiftSignPattern (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ)
    (w : Fin n → ℤ) : Fin s → ℤ :=
  fun i => if 0 ≤ b i + rayMap A w i then 0 else -1

theorem shiftSignPattern_isSign (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (w : Fin n → ℤ) : IsSignPattern (shiftSignPattern A b w) := by
  intro i
  dsimp [shiftSignPattern]
  split_ifs <;> simp

def AccessiblePattern (A : Matrix (Fin s) (Fin n) ℤ)
    (b e : Fin s → ℤ) : Prop :=
  ∃ w : Fin n → ℤ, shiftSignPattern A b w = e

theorem AccessiblePattern.isSign {A : Matrix (Fin s) (Fin n) ℤ}
    {b e : Fin s → ℤ} (he : AccessiblePattern A b e) : IsSignPattern e := by
  obtain ⟨w, rfl⟩ := he
  exact shiftSignPattern_isSign A b w

/-- This is precisely the integer feasibility condition for the boundary signs. -/
theorem accessiblePattern_iff (A : Matrix (Fin s) (Fin n) ℤ)
    (b e : Fin s → ℤ) (he : IsSignPattern e) :
    AccessiblePattern A b e ↔
      ∃ w : Fin n → ℤ, ∀ i,
        (e i = 0 → 0 ≤ b i + rayMap A w i) ∧
        (e i = -1 → b i + rayMap A w i ≤ -1) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun i => ?_⟩
    have hi := congrFun hw i
    dsimp [shiftSignPattern] at hi
    split_ifs at hi with hb <;> constructor <;> intro h <;> omega
  · rintro ⟨w, hw⟩
    refine ⟨w, funext fun i => ?_⟩
    rcases he i with hi | hi
    · simp [shiftSignPattern, (hw i).1 hi, hi]
    · have hb : ¬0 ≤ b i + rayMap A w i := by
        have := (hw i).2 hi
        omega
      simp [shiftSignPattern, hb, hi]

def allSignPatterns (s : ℕ) : Finset (Fin s → ℤ) :=
  Finset.univ.image (fun p : Fin s → Bool => fun i => if p i then 0 else -1)

theorem mem_allSignPatterns (e : Fin s → ℤ) :
    e ∈ allSignPatterns s ↔ IsSignPattern e := by
  constructor
  · intro he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    intro i
    cases p i <;> simp
  · intro he
    apply Finset.mem_image.mpr
    refine ⟨fun i => decide (e i = 0), Finset.mem_univ _, funext fun i => ?_⟩
    rcases he i with hi | hi <;> simp [hi]

def accessiblePatterns (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : Finset (Fin s → ℤ) := by
  classical
  exact (allSignPatterns s).filter (AccessiblePattern A b)

@[simp] theorem mem_accessiblePatterns (A : Matrix (Fin s) (Fin n) ℤ)
    (b e : Fin s → ℤ) :
    e ∈ accessiblePatterns A b ↔ AccessiblePattern A b e := by
  classical
  simp only [accessiblePatterns, Finset.mem_filter, mem_allSignPatterns]
  exact ⟨And.right, fun he => ⟨he.isSign, he⟩⟩

def patternWitness (A : Matrix (Fin s) (Fin n) ℤ) (b e : Fin s → ℤ) :
    Fin n → ℤ := by
  classical
  exact if he : AccessiblePattern A b e then Classical.choose he else 0

theorem patternWitness_spec (A : Matrix (Fin s) (Fin n) ℤ) (b e : Fin s → ℤ)
    (he : AccessiblePattern A b e) :
    shiftSignPattern A b (patternWitness A b e) = e := by
  classical
  simp only [patternWitness, dif_pos he]
  exact Classical.choose_spec he

/-- The manuscript's K_b for the displayed, fixed choice of one witness per
accessible pattern. Empty ray sets give K_b=1. -/
def accessibilityBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  1 + (accessiblePatterns A b).sup (fun e =>
    Finset.univ.sup (fun i => (b i + rayMap A (patternWitness A b e) i).natAbs))

theorem accessibilityBound_pos (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    0 < accessibilityBound A b := by unfold accessibilityBound; omega

theorem patternWitness_bound (A : Matrix (Fin s) (Fin n) ℤ)
    (b e : Fin s → ℤ) (he : AccessiblePattern A b e)
    (k : ℕ) (hk : accessibilityBound A b ≤ k) (i : Fin s) :
    |b i + rayMap A (patternWitness A b e) i| < (k : ℤ) := by
  have hi := Finset.le_sup (f := fun i : Fin s =>
    (b i + rayMap A (patternWitness A b e) i).natAbs) (Finset.mem_univ i)
  have he' := Finset.le_sup (f := fun e : Fin s → ℤ =>
    Finset.univ.sup (fun i => (b i + rayMap A (patternWitness A b e) i).natAbs))
    ((mem_accessiblePatterns A b e).mpr he)
  have hnat : (b i + rayMap A (patternWitness A b e) i).natAbs < k := by
    unfold accessibilityBound at hk
    omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hnat

def accessibleThomsenClasses (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    Set (DivisorClass A) :=
  ⋃ e : Fin s → ℤ, ⋃ (_he : AccessiblePattern A b e), thomsenClasses A e

theorem accessibleThomsenClasses_subset_power
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (k : ℕ)
    (hk : accessibilityBound A b ≤ k) :
    accessibleThomsenClasses A b ⊆
      frobeniusClasses A b ((universalDenominator A * k : ℕ) : ℤ) := by
  have hkpos : 0 < k := lt_of_lt_of_le (accessibilityBound_pos A b) hk
  have hkint : (0 : ℤ) < k := by exact_mod_cast hkpos
  intro a ha
  obtain ⟨e, ha⟩ := Set.mem_iUnion.mp ha
  obtain ⟨he, ha⟩ := Set.mem_iUnion.mp ha
  rw [thomsenClasses_eq_frobenius_universal A e he.isSign] at ha
  have hfloor : powerCoefficient A b (k : ℤ) (patternWitness A b e) = e := by
    rw [accessible_pattern_occurs A b _ _ (patternWitness_bound A b e he k hk)]
    exact patternWitness_spec A b e he
  have hcompose := frobeniusClasses_compose A b (universalDenominator A : ℤ)
    (k : ℤ) hkint
  have hc : a ∈ frobeniusClasses A b ((k : ℤ) * (universalDenominator A : ℤ)) := by
    rw [hcompose]
    apply Set.mem_iUnion.mpr
    refine ⟨patternWitness A b e, ?_⟩
    rw [hfloor]
    exact ha
  simpa only [Nat.cast_mul, mul_comm] using hc

end ToricPower

