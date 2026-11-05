import cubical.cube
import Mathlib.Data.Fintype.Option

/-! # The ordinary coordinate face poset of a cube -/

namespace Cubical.Cube

inductive FaceCoordinate where
  | free
  | fixed (bit : Bool)
  deriving DecidableEq, Fintype

namespace FaceCoordinate

instance : PartialOrder FaceCoordinate where
  le a b := b = free ∨ a = b
  le_refl _ := Or.inr rfl
  le_trans a b c hab hbc := by
    rcases hbc with h | h
    · exact Or.inl h
    · exact h ▸ hab
  le_antisymm a b hab hba := by
    rcases hab with h | h
    · subst b
      rcases hba with h | h
      · exact h
      · exact h.symm
    · exact h

@[simp] theorem le_free (a : FaceCoordinate) : a ≤ free := Or.inl rfl

@[simp] theorem le_fixed_iff (a : FaceCoordinate) (b : Bool) :
    a ≤ fixed b ↔ a = fixed b := by
  change (fixed b = free ∨ a = fixed b) ↔ _
  simp

end FaceCoordinate

abbrev FaceCode (d : ℕ) := Fin d → FaceCoordinate

def Matches {d : ℕ} (p : FaceCode d) (s : Vertex d) : Prop :=
  ∀ i, p i = .free ∨ p i = .fixed (s i)

def baseCode {d : ℕ} (p : FaceCode d) : Vertex d :=
  fun i => match p i with
    | .free => false
    | .fixed b => b

theorem baseCode_matches {d : ℕ} (p : FaceCode d) : Matches p (baseCode p) := by
  intro i
  cases h : p i <;> simp [baseCode, h]

def freeCoords {d : ℕ} (p : FaceCode d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => p i = .free)

@[simp] theorem mem_freeCoords {d : ℕ} (p : FaceCode d) (i : Fin d) :
    i ∈ freeCoords p ↔ p i = .free := by simp [freeCoords]

def faceCode {d : ℕ} (s : Vertex d) (A : Finset (Fin d)) : FaceCode d :=
  fun i => if i ∈ A then .free else .fixed (s i)

@[simp] theorem freeCoords_faceCode {d : ℕ} (s : Vertex d) (A : Finset (Fin d)) :
    freeCoords (faceCode s A) = A := by
  ext i
  by_cases hi : i ∈ A <;> simp [faceCode, hi]

theorem matches_faceCode_iff {d : ℕ} (s t : Vertex d) (A : Finset (Fin d)) :
    Matches (faceCode s A) t ↔ t ∈ FaceAt s A := by
  constructor
  · intro h i hi
    have hh := h i
    simpa [faceCode, hi, eq_comm] using hh
  · intro h i
    by_cases hi : i ∈ A
    · simp [faceCode, hi]
    · simp [faceCode, hi, h i hi]

theorem matches_of_le {d : ℕ} {p q : FaceCode d} (hpq : p ≤ q)
    {s : Vertex d} (hs : Matches p s) : Matches q s := by
  intro i
  rcases hpq i with h | h
  · exact Or.inl h
  · rw [← h]
    exact hs i

theorem le_of_matches {d : ℕ} {p q : FaceCode d}
    (h : ∀ s, Matches p s → Matches q s) : p ≤ q := by
  intro i
  cases hq : q i with
  | free => exact Or.inl rfl
  | fixed b =>
    apply Or.inr
    cases hp : p i with
    | fixed a =>
      have hh := h (baseCode p) (baseCode_matches p) i
      simpa [hq, baseCode, hp, eq_comm] using hh
    | free =>
      let s : Vertex d := Function.update (baseCode p) i (!b)
      have hs : Matches p s := by
        intro j
        by_cases hji : j = i
        · subst j
          exact Or.inl hp
        · simpa [s, hji] using baseCode_matches p j
      have hh := h s hs i
      simp [hq, s] at hh

theorem faceCode_le_iff {d : ℕ} (p q : FaceCode d) :
    p ≤ q ↔ ∀ s, Matches p s → Matches q s :=
  ⟨fun h _ => matches_of_le h, le_of_matches⟩

theorem faceCode_eq_iff {d : ℕ} (p q : FaceCode d) :
    p = q ↔ ∀ s, Matches p s ↔ Matches q s := by
  constructor
  · rintro rfl s
    rfl
  · intro h
    exact le_antisymm (le_of_matches fun s => (h s).mp)
      (le_of_matches fun s => (h s).mpr)

end Cubical.Cube
