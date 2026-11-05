import CommAlg.IntegralClosure.ShiftWeights

/-! # Integral closure of the actual multi-Rees coefficient ideal

The carrier is the literal coefficientwise direct sum in the multi-Rees
subalgebra. Its equality with the ideal of genuine homological shifts is
obtained from the separately proved graded-Tor rank formula.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {k : Type*} [CommRing k] [Nontrivial k]

def rankShiftMultiFamily (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (s : J →₀ ℕ) : Ideal (MvPolynomial V k) :=
  rankShiftIdeal k (η.add (multiRank ρ s)) i

theorem rankShiftMulti_action (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (s t : J →₀ ℕ) :
    powerProduct (fun j => rankIdeal k (ρ j)) s * rankShiftMultiFamily η ρ i t ≤
      rankShiftMultiFamily η ρ i (s + t) := by
  rw [powerProduct, ← rankIdeal_multiRank]
  have hr : (multiRank ρ s).add (η.add (multiRank ρ t)) =
      η.add (multiRank ρ (s + t)) := by
    apply RankFunction.ext_fun
    intro A
    simp only [multiRank_add, RankFunction.add]
    omega
  unfold rankShiftMultiFamily
  rw [← hr]
  exact rankIdeal_mul_rankShiftIdeal_le _ _ i

def rankShiftMultiIdeal (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ) :
    Ideal (multiReesAlgebra (fun j => rankIdeal k (ρ j))) :=
  multiReesIdeal (fun j => rankIdeal k (ρ j)) (rankShiftMultiFamily η ρ i)
    (rankShiftMulti_action η ρ i)

@[simp] theorem mem_rankShiftMultiIdeal (η : RankFunction V) (ρ : J → RankFunction V)
    (i : ℕ) (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    p ∈ rankShiftMultiIdeal η ρ i ↔
      ∀ s, p.val.coeff s ∈ rankShiftIdeal k (η.add (multiRank ρ s)) i := Iff.rfl

theorem rankShiftMulti_mem_iff_weights (η : RankFunction V) (ρ : J → RankFunction V)
    (i : ℕ) (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    p ∈ rankShiftMultiIdeal η ρ i ↔
      ∀ t, Weight.Bound (shiftWeight ρ t) (shiftThreshold η i t)
        (multiReesFlatten (fun j => rankIdeal k (ρ j)) p) := by
  rw [mem_rankShiftMultiIdeal]
  constructor
  · intro hp t e he
    have ha : ordinaryDegree e ∈ (p.val.coeff (reesDegree e)).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rwa [multiReesFlatten_coeff] at he
    have hm := (mem_rankShiftIdeal_iff_coeff _ i _).mp (hp (reesDegree e))
      (ordinaryDegree e) ha
    exact (shiftWeight_bounds_iff η ρ i e).mpr hm t
  · intro hp s
    apply (mem_rankShiftIdeal_iff_coeff _ i _).mpr
    intro a ha
    let e := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)
    have hs : reesDegree e = s := by simp [e, reesDegree]
    have ha' : ordinaryDegree e = a := by simp [e, ordinaryDegree]
    have he : (multiReesFlatten (fun j => rankIdeal k (ρ j)) p).coeff e ≠ 0 := by
      rw [multiReesFlatten_coeff, hs, ha']
      exact MvPolynomial.mem_support_iff.mp ha
    have hm := (shiftWeight_bounds_iff (k := k) η ρ i e).mp (fun t => hp t e he)
    simpa only [hs, ha'] using hm

theorem shiftWeight_bound_zero (ρ : J → RankFunction V) (t : ShiftCut V)
    (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    Weight.Bound (shiftWeight ρ t) 0
      (multiReesFlatten (fun j => rankIdeal k (ρ j)) p) := by
  intro e he
  apply shiftWeight_nonneg ρ e _ t
  exact (mem_polymatroid_multiRees ρ p.val).mp p.property e he

/-- The multi-Rees ideal described by the exact shift-rank formula is
integrally closed over every domain. This includes every field, all
multidegrees, fixed twists, unit ideals, and inactive variables. -/
theorem rankShiftMultiIdeal_integrallyClosed [IsDomain k]
    (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ) :
    IsIntegrallyClosedIdeal (rankShiftMultiIdeal (k := k) η ρ i) := by
  apply Weight.integrallyClosed_of_weight_bounds
    (multiReesFlatten (fun j => rankIdeal k (ρ j)))
    (shiftWeight ρ) (shiftThreshold η i)
    (shiftWeight_bound_zero ρ)
  exact rankShiftMulti_mem_iff_weights η ρ i

end CommAlg
