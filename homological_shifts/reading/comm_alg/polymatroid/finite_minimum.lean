import Mathlib.Data.Finset.Lattice.Fold

/-! # Exact minima of nonempty finite families of natural numbers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMinimum (f : ι → ℕ) : ℕ :=
  univ.inf' univ_nonempty f

theorem finiteMinimum_le (f : ι → ℕ) (j : ι) : finiteMinimum f ≤ f j :=
  Finset.inf'_le _ (mem_univ j)

theorem le_finiteMinimum {f : ι → ℕ} {n : ℕ} (h : ∀ j, n ≤ f j) :
    n ≤ finiteMinimum f := Finset.le_inf' _ _ (fun j _ => h j)

theorem finiteMinimum_attained (f : ι → ℕ) : ∃ j, f j = finiteMinimum f := by
  obtain ⟨j, _, hj⟩ := (Finset.inf'_le_iff univ_nonempty).mp
    (le_rfl : finiteMinimum f ≤ finiteMinimum f)
  exact ⟨j, le_antisymm hj (finiteMinimum_le f j)⟩

theorem finiteMinimum_mono {f g : ι → ℕ} (h : ∀ j, f j ≤ g j) :
    finiteMinimum f ≤ finiteMinimum g := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained g
  exact ((finiteMinimum_le f j).trans (h j)).trans_eq hj

theorem finiteMinimum_add_const (f : ι → ℕ) (n : ℕ) :
    finiteMinimum (fun j => n + f j) = n + finiteMinimum f := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained f
  apply le_antisymm
  · exact (finiteMinimum_le (fun j => n + f j) j).trans_eq (congrArg (n + ·) hj)
  · exact le_finiteMinimum (fun j => Nat.add_le_add_left (finiteMinimum_le f j) n)

theorem finiteMinimum_min_left (f : ι → ℕ) (n : ℕ) :
    finiteMinimum (fun j => min n (f j)) = min n (finiteMinimum f) := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained f
  apply le_antisymm
  · exact (finiteMinimum_le (fun j => min n (f j)) j).trans_eq (congrArg (min n) hj)
  · exact le_finiteMinimum (fun j => min_le_min_left n (finiteMinimum_le f j))

theorem le_finiteMinimum_iff (f : ι → ℕ) (n : ℕ) :
    n ≤ finiteMinimum f ↔ ∀ j, n ≤ f j :=
  ⟨fun h j => h.trans (finiteMinimum_le f j), le_finiteMinimum⟩

end CommAlg.Polymatroid
