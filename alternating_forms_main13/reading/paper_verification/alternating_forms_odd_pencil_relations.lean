module

public import PaperVerification.AlternatingFormsSingletonStates
public import PaperVerification.AlternatingFormsWeights
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Fin
import Lean.Elab.Tactic.Omega

/-!
# The literal odd-pencil relation obtained from prefix division

This file places the local inverse inside the complete matching quadratic.
It proves the paper's equation (5) in the actual exterior algebra, including
arbitrary suffix words, and defines both canonical path quadrics explicitly.
The first-exit and reflection lemmas identify the prefixes to which division
applies.  An initial-ideal assertion additionally requires the monomial-weight
comparison, and a basis assertion additionally requires independence.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

section Matching

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [Fintype ι] [DecidableEq ι]

/-- The actual homogeneous quadratic associated to a finite matching. -/
def matchingQuadratic (u v : ι → M) : ⋀[K]^2 M :=
  ∑ i, exteriorPair (K := K) (u i) (v i)

@[simp] theorem matchingQuadratic_coe (u v : ι → M) :
    (matchingQuadratic (K := K) u v : ExteriorAlgebra K M) =
      ∑ i, ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i) := by
  simp only [matchingQuadratic, AddSubmonoidClass.coe_finsetSum, exteriorPair_coe]

/-- The full matching relation, with the original prefix as its leading
displayed summand.  The inverse has the genuine degree `|H|-1`; the second
summand uses only matching pairs outside `H`.  No quotient relation is assumed. -/
theorem matching_prefix_relation [CharZero K] (u v : ι → M) (H : Finset ι)
    (A B : Finset H) (hdegree : A.card + B.card = H.card + 1) (L : List M) :
    ∃ η : ⋀[K]^(H.card - 1) M,
      (matchingQuadratic (K := K) u v : ExteriorAlgebra K M) *
          ((η : ExteriorAlgebra K M) * (L.map (ExteriorAlgebra.ι K)).prod) =
        (((A.toList.map (fun i : H => u i.val) ++
          B.toList.map (fun i : H => v i.val)).map (ExteriorAlgebra.ι K)).prod *
            (L.map (ExteriorAlgebra.ι K)).prod) +
        (∑ i : {i : ι // i ∉ H},
          ExteriorAlgebra.ι K (u i.val) * ExteriorAlgebra.ι K (v i.val)) *
            ((η : ExteriorAlgebra K M) * (L.map (ExteriorAlgebra.ι K)).prod) := by
  obtain ⟨η, hη⟩ := prefix_selection_division
    (K := K) (fun i : H => u i.val) (fun i : H => v i.val) A B
    (by simpa only [Fintype.card_coe] using hdegree)
  refine ⟨⟨η, by simpa only [Fintype.card_coe] using η.property⟩, ?_⟩
  have hsplit :
      (matchingQuadratic (K := K) u v : ExteriorAlgebra K M) =
        (∑ i : H, ExteriorAlgebra.ι K (u i.val) * ExteriorAlgebra.ι K (v i.val)) +
        ∑ i : {i : ι // i ∉ H},
          ExteriorAlgebra.ι K (u i.val) * ExteriorAlgebra.ι K (v i.val) := by
    rw [matchingQuadratic_coe]
    have hs := (Fintype.sum_subtype_add_sum_subtype (fun i : ι => i ∈ H)
      (fun i => ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ι K (v i))).symm
    refine hs.trans ?_
    refine congrArg₂ (fun a b : ExteriorAlgebra K M => a + b) ?_ rfl
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_univ]
    · intro i hi
      rfl
  change (matchingQuadratic (K := K) u v : ExteriorAlgebra K M) *
      ((η : ExteriorAlgebra K M) * _) = _
  rw [hsplit, add_mul, ← mul_assoc, hη]

end Matching

section OddPath

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Zero-based indices of the first matching in the paper's odd path. -/
def oddPathFirstLeft {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

def oddPathMiddle {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

def oddPathSecondRight {k : ℕ} (i : Fin k) : Fin (2 * k + 1) :=
  ⟨2 * i.val + 2, by have := i.isLt; omega⟩

/-- The literal form `F = Σ z_(2i-1) z_(2i)` in zero-based indexing. -/
def oddPathFirstQuadratic {k : ℕ} (z : Fin (2 * k + 1) → M) : ⋀[K]^2 M :=
  matchingQuadratic (fun i => z (oddPathFirstLeft i)) (fun i => z (oddPathMiddle i))

/-- The literal form `G = Σ z_(2i) z_(2i+1)` in the same indexing. -/
def oddPathSecondQuadratic {k : ℕ} (z : Fin (2 * k + 1) → M) : ⋀[K]^2 M :=
  matchingQuadratic (fun i => z (oddPathMiddle i)) (fun i => z (oddPathSecondRight i))

theorem oddPathFirstLeft_rev {k : ℕ} (i : Fin k) :
    (oddPathFirstLeft i).rev = oddPathSecondRight i.rev := by
  apply Fin.ext
  simp only [Fin.val_rev, oddPathFirstLeft, oddPathSecondRight]
  have hi := i.isLt
  omega

theorem oddPathMiddle_rev {k : ℕ} (i : Fin k) :
    (oddPathMiddle i).rev = oddPathMiddle i.rev := by
  apply Fin.ext
  simp only [Fin.val_rev, oddPathMiddle]
  have hi := i.isLt
  omega

/-- Reflection interchanges the two canonical quadrics with the exterior
sign.  Thus the same prefix division applies at the right endpoint. -/
theorem oddPath_reflection {k : ℕ} (z : Fin (2 * k + 1) → M) :
    oddPathFirstQuadratic (K := K) (fun i => z i.rev) =
      -oddPathSecondQuadratic (K := K) z := by
  apply Subtype.ext
  simp only [oddPathFirstQuadratic, oddPathSecondQuadratic, matchingQuadratic_coe,
    Submodule.coe_neg, oddPathFirstLeft_rev, oddPathMiddle_rev]
  calc
    _ = ∑ i : Fin k, -(ExteriorAlgebra.ι K (z (oddPathMiddle i.rev)) *
        ExteriorAlgebra.ι K (z (oddPathSecondRight i.rev))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    _ = _ := by
      rw [Finset.sum_neg_distrib]
      congr 1
      exact Equiv.sum_comp (Fin.revPerm : Fin k ≃ Fin k)
        (fun i : Fin k => ExteriorAlgebra.ι K (z (oddPathMiddle i)) *
          ExteriorAlgebra.ι K (z (oddPathSecondRight i)))

/-- The paper's two edge-cost sequences, with path edges indexed from zero. -/
def oddPathEdgeCost (k j : ℕ) : ℤ :=
  if Even j then (2 : ℤ) ^ (j / 2 + 1) else (2 : ℤ) ^ (k - j / 2)

/-- The integer vertex costs simultaneously solving both matchings. -/
def oddPathVertexCost (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  pathVertexCost (oddPathEdgeCost k) i.val

/-- A single positive weight vector for both canonical quadrics. -/
def oddPathVertexWeight (k : ℕ) (i : Fin (2 * k + 1)) : ℤ :=
  positiveWeightShift (oddPathVertexCost k) - oddPathVertexCost k i

theorem oddPathVertexWeight_positive (k : ℕ) (i : Fin (2 * k + 1)) :
    0 < oddPathVertexWeight k i :=
  shiftedVertexWeight_pos (oddPathVertexCost k) i

theorem oddPathFirst_pair_cost {k : ℕ} (i : Fin k) :
    oddPathVertexCost k (oddPathFirstLeft i) +
      oddPathVertexCost k (oddPathMiddle i) = (2 : ℤ) ^ (i.val + 1) := by
  change pathVertexCost (oddPathEdgeCost k) (2 * i.val) +
    pathVertexCost (oddPathEdgeCost k) (2 * i.val + 1) = _
  rw [pathVertexCost_adjacent]
  have he : Even (2 * i.val) := ⟨i.val, by omega⟩
  have hd : (2 * i.val) / 2 = i.val := by omega
  simp only [oddPathEdgeCost, if_pos he, hd]

theorem oddPathSecond_pair_cost {k : ℕ} (i : Fin k) :
    oddPathVertexCost k (oddPathMiddle i) +
      oddPathVertexCost k (oddPathSecondRight i) = (2 : ℤ) ^ (k - i.val) := by
  change pathVertexCost (oddPathEdgeCost k) (2 * i.val + 1) +
    pathVertexCost (oddPathEdgeCost k) ((2 * i.val + 1) + 1) = _
  rw [pathVertexCost_adjacent]
  have he : ¬Even (2 * i.val + 1) := by
    rintro ⟨m, hm⟩
    omega
  have hd : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [oddPathEdgeCost, if_neg he, hd]

/-- After reflection the second matching has the same increasing power-of-two
costs as the first, while retaining this very same vertex-cost vector. -/
theorem oddPathSecond_pair_cost_reflected {k : ℕ} (i : Fin k) :
    oddPathVertexCost k (oddPathMiddle i.rev) +
      oddPathVertexCost k (oddPathSecondRight i.rev) = (2 : ℤ) ^ (i.val + 1) := by
  rw [oddPathSecond_pair_cost]
  congr 1
  simp only [Fin.val_rev]
  have hi := i.isLt
  omega

/-- The actual shifted weights on the first matching have exactly the
prescribed pair weights, not merely some separately chosen admissible order. -/
theorem oddPathFirst_pair_weight {k : ℕ} (i : Fin k) :
    oddPathVertexWeight k (oddPathFirstLeft i) +
      oddPathVertexWeight k (oddPathMiddle i) =
        2 * positiveWeightShift (oddPathVertexCost k) - (2 : ℤ) ^ (i.val + 1) := by
  have h := oddPathFirst_pair_cost i
  simp only [oddPathVertexWeight]
  omega

theorem oddPathSecond_pair_weight {k : ℕ} (i : Fin k) :
    oddPathVertexWeight k (oddPathMiddle i) +
      oddPathVertexWeight k (oddPathSecondRight i) =
        2 * positiveWeightShift (oddPathVertexCost k) - (2 : ℤ) ^ (k - i.val) := by
  have h := oddPathSecond_pair_cost i
  simp only [oddPathVertexWeight]
  omega

end OddPath

section FirstFailure

/-- At the first failed lower inequality, the selected variable is exactly
the last position of an even prefix containing one more than half its positions.
This is the first-exit argument in Lemma 3.2 for every finite increasing tuple. -/
theorem first_left_failure {s : ℕ} (I : Fin s → ℕ) (hI : StrictMono I)
    (hbad : ∃ i, I i < 2 * i.val) :
    ∃ j : Fin s, 0 < j.val ∧ I j = 2 * j.val - 1 ∧
      ∀ i : Fin s, I i < 2 * j.val ↔ i ≤ j := by
  classical
  let bad : Finset (Fin s) := Finset.univ.filter fun i => I i < 2 * i.val
  have hbadne : bad.Nonempty := by
    obtain ⟨i, hi⟩ := hbad
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := bad.min' hbadne
  have hjbad : I j < 2 * j.val := (Finset.mem_filter.mp (bad.min'_mem hbadne)).2
  have hjpos : 0 < j.val := by omega
  have hprevious : ∀ i : Fin s, i < j → 2 * i.val ≤ I i := by
    intro i hij
    by_contra hi
    have hibad : i ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
    have hji : j ≤ i := bad.min'_le _ hibad
    exact (not_le_of_gt hij) hji
  let a : Fin s := ⟨j.val - 1, by have := j.isLt; omega⟩
  have haj : a < j := by change j.val - 1 < j.val; omega
  have ha := hprevious a haj
  have hai := hI haj
  have hjeq : I j = 2 * j.val - 1 := by
    have hav : a.val = j.val - 1 := rfl
    omega
  refine ⟨j, hjpos, hjeq, ?_⟩
  intro i
  constructor
  · intro hi
    by_contra hij
    have hji : j < i := lt_of_not_ge hij
    have hgt := hI hji
    omega
  · intro hij
    have hle := hI.monotone hij
    omega

/-- The failure prefix lies inside the actual odd matching and has exactly
`h+1` selected positions.  There is no restriction on the exterior degree. -/
theorem odd_left_failure_prefix {k s : ℕ} (I : Fin s → Fin (2 * k + 1))
    (hI : StrictMono I) (hbad : ∃ i, (I i).val < 2 * i.val) :
    ∃ h : ℕ, 0 < h ∧ h ≤ k ∧
      ((Finset.univ : Finset (Fin s)).filter fun i => (I i).val < 2 * h).card = h + 1 := by
  obtain ⟨j, hj, hpos, hprefix⟩ := first_left_failure
    (fun i => (I i).val) (fun i j hij => hI hij) hbad
  refine ⟨j.val, hj, ?_, ?_⟩
  · have hi := (I j).isLt
    omega
  · have heq : ((Finset.univ : Finset (Fin s)).filter fun i => (I i).val < 2 * j.val) =
        Finset.Iic j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic,
        hprefix]
    rw [heq, Fin.card_Iic]

/-- Reversing both the selected tuple and the ambient path retains increasing
order; it is the actual reflection used to turn a right failure into a left one. -/
def reflectSelection {n s : ℕ} (I : Fin s → Fin n) : Fin s → Fin n :=
  fun i => (I i.rev).rev

theorem reflectSelection_strictMono {n s : ℕ} (I : Fin s → Fin n)
    (hI : StrictMono I) : StrictMono (reflectSelection I) := by
  intro i j hij
  exact Fin.rev_lt_rev.mpr (hI (Fin.rev_lt_rev.mpr hij))

theorem right_failure_becomes_left {n s : ℕ} (I : Fin s → Fin n)
    (hbad : ∃ j, n + 2 * j.val + 1 < (I j).val + 2 * s) :
    ∃ i, (reflectSelection I i).val < 2 * i.val := by
  obtain ⟨j, hj⟩ := hbad
  refine ⟨j.rev, ?_⟩
  simp only [reflectSelection, Fin.rev_rev, Fin.val_rev]
  have hjlt := j.isLt
  have hIlt := (I j).isLt
  omega

end FirstFailure

end PaperVerification.AlternatingForms
