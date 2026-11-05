import CommAlg.IntegralClosure.MultiRees
import CommAlg.IntegralClosure.Ideal
import CommAlg.Polymatroid.ShiftMultiplication

/-! # The exact linear inequalities of homological-shift Rees ideals

There are two families of integer weights: the ordinary polymatroid lower
bounds, and one weight for every partition. The empty partition supplies
the total-degree inequality. No positivity assumption on ranks is used.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

def ShiftCut (V : Type*) [DecidableEq V] :=
  Finset V ⊕ (Σ A : Finset V, Finpartition A)

def cutWeight (c : J → ℤ) (A : Finset V) : J ⊕ V → ℤ :=
  Sum.elim c (fun v => if v ∈ Aᶜ then 1 else 0)

theorem weight_cutWeight (c : J → ℤ) (A : Finset V) (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (cutWeight c A) e =
      (∑ j, (reesDegree e j : ℤ) * c j) + (subsetSum (ordinaryDegree e) Aᶜ : ℤ) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply sum_congr rfl
    intro j hj
    simp [cutWeight, nsmul_eq_mul]
  · simp only [cutWeight, Sum.elim_inr, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem]
    simp [subsetSum]

def shiftWeight (ρ : J → RankFunction V) : ShiftCut V → J ⊕ V → ℤ
  | .inl A => cutWeight (fun j => (ρ j A : ℤ) - ρ j univ) A
  | .inr ⟨A, P⟩ => cutWeight (fun j => (∑ C ∈ P.parts, (ρ j C : ℤ)) - ρ j univ) A

def shiftThreshold (η : RankFunction V) (i : ℕ) : ShiftCut V → ℤ
  | .inl A => (η univ : ℤ) - η A
  | .inr ⟨A, P⟩ => (η univ : ℤ) + i + P.parts.card - A.card - ∑ C ∈ P.parts, (η C : ℤ)

theorem shiftWeight_lower (ρ : J → RankFunction V) (A : Finset V)
    (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (shiftWeight ρ (.inl A)) e =
      (subsetSum (ordinaryDegree e) Aᶜ : ℤ) +
        multiRank ρ (reesDegree e) A - multiRank ρ (reesDegree e) univ := by
  rw [shiftWeight, weight_cutWeight]
  simp only [mul_sub, sum_sub_distrib, multiRank_apply, Nat.cast_sum, Nat.cast_mul]
  ring

theorem shiftWeight_partition (ρ : J → RankFunction V) (A : Finset V)
    (P : Finpartition A) (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (shiftWeight ρ (.inr ⟨A, P⟩)) e =
      (subsetSum (ordinaryDegree e) Aᶜ : ℤ) +
        (∑ C ∈ P.parts, (multiRank ρ (reesDegree e) C : ℤ)) -
          multiRank ρ (reesDegree e) univ := by
  rw [shiftWeight, weight_cutWeight]
  simp only [mul_sub, sum_sub_distrib, mul_sum, multiRank_apply, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_comm (s := univ) (t := P.parts)]
  ring

theorem shiftWeight_nonneg (ρ : J → RankFunction V) (e : J ⊕ V →₀ ℕ)
    (he : LowerFeasible (multiRank ρ (reesDegree e)).lower (ordinaryDegree e))
    (t : ShiftCut V) : 0 ≤ Finsupp.weight (shiftWeight ρ t) e := by
  rcases t with A | ⟨A, P⟩
  · rw [shiftWeight_lower]
    have hb := he Aᶜ
    have hL := (multiRank ρ (reesDegree e)).lower_add_compl Aᶜ
    simp only [compl_compl] at hL
    omega
  · rw [shiftWeight_partition]
    have hb := he Aᶜ
    have hL := (multiRank ρ (reesDegree e)).lower_add_compl Aᶜ
    have hP := (multiRank ρ (reesDegree e)).le_sum_partition P
    simp only [compl_compl] at hL
    have hPz : (multiRank ρ (reesDegree e) A : ℤ) ≤
        ∑ C ∈ P.parts, (multiRank ρ (reesDegree e) C : ℤ) := by exact_mod_cast hP
    omega

theorem shiftWeight_bounds_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (e : J ⊕ V →₀ ℕ) :
    (∀ t, shiftThreshold η i t ≤ Finsupp.weight (shiftWeight ρ t) e) ↔
      MvPolynomial.monomial (ordinaryDegree e) (1 : k) ∈
        rankShiftIdeal k (η.add (multiRank ρ (reesDegree e))) i := by
  rw [monomial_mem_rankShiftIdeal_partition_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hc := h (.inr ⟨∅, Finpartition.empty (Finset V)⟩)
      rw [shiftWeight_partition] at hc
      simp only [shiftThreshold, Finpartition.empty_parts, card_empty, sum_empty,
        compl_empty, subsetSum_univ, Nat.cast_zero, add_zero, sub_zero] at hc
      change η univ + multiRank ρ (reesDegree e) univ + i ≤ (ordinaryDegree e).degree
      omega
    · intro U
      have hc := h (.inl Uᶜ)
      rw [shiftWeight_lower] at hc
      simp only [shiftThreshold, compl_compl] at hc
      have hL := (η.add (multiRank ρ (reesDegree e))).lower_add_compl U
      change (η.add (multiRank ρ (reesDegree e))).lower U +
        (η Uᶜ + multiRank ρ (reesDegree e) Uᶜ) =
          η univ + multiRank ρ (reesDegree e) univ at hL
      omega
    · intro A hA P
      have hc := h (.inr ⟨A, P⟩)
      rw [shiftWeight_partition] at hc
      simp only [shiftThreshold, ← Nat.cast_sum] at hc
      change η univ + multiRank ρ (reesDegree e) univ + i + P.parts.card ≤
        subsetSum (ordinaryDegree e) Aᶜ + A.card +
          ∑ C ∈ P.parts, (η C + multiRank ρ (reesDegree e) C)
      rw [sum_add_distrib]
      omega
  · rintro ⟨hdeg, hLower, hPart⟩ t
    rcases t with A | ⟨A, P⟩
    · rw [shiftWeight_lower]
      simp only [shiftThreshold]
      have hb := hLower Aᶜ
      have hL := (η.add (multiRank ρ (reesDegree e))).lower_add_compl Aᶜ
      simp only [compl_compl] at hL
      change (η.add (multiRank ρ (reesDegree e))).lower Aᶜ +
        (η A + multiRank ρ (reesDegree e) A) =
          η univ + multiRank ρ (reesDegree e) univ at hL
      omega
    · rw [shiftWeight_partition]
      simp only [shiftThreshold, ← Nat.cast_sum]
      by_cases hA : A = ∅
      · subst A
        have hP : P.parts = ∅ := P.parts_eq_empty_iff.mpr rfl
        simp only [hP, card_empty, sum_empty, compl_empty, subsetSum_univ,
          Nat.cast_zero, add_zero, sub_zero]
        change η univ + multiRank ρ (reesDegree e) univ + i ≤
          (ordinaryDegree e).degree at hdeg
        omega
      · have hp := hPart A (Finset.nonempty_iff_ne_empty.mpr hA) P
        change η univ + multiRank ρ (reesDegree e) univ + i + P.parts.card ≤
          subsetSum (ordinaryDegree e) Aᶜ + A.card +
            ∑ C ∈ P.parts, (η C + multiRank ρ (reesDegree e) C) at hp
        rw [sum_add_distrib] at hp
        omega

end CommAlg
