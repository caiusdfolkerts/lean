module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Rational solutions of finite rational weak linear systems

Fourier--Motzkin elimination is proved over an arbitrary ordered field.
For a system whose coefficients are rational, the same finite eliminated
system works over the rationals and over the reals. Induction on the
number of variables therefore supplies an actual rational solution to
every nonempty real rational polyhedron. Boundary solutions are included;
no strict-feasibility or full-dimensionality assumption is used.
-/

noncomputable section

namespace PaperVerification.ToricRationalGeometry

open scoped BigOperators Classical

theorem exists_linear_inequality_variable_iff {K ι : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    (a b : ι → K) :
    (∃ t : K,∀ i,0≤a i*t+b i) ↔
      (∀ i,a i=0 → 0≤b i) ∧
      (∀ i j,0<a i → a j<0 → -b i/a i≤-b j/a j) := by
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i hi => by simpa [hi] using ht i,?_⟩
    intro i j hi hj
    have hlo : -b i/a i≤t := (div_le_iff₀ hi).mpr (by nlinarith [ht i])
    have hup : t≤-b j/a j := (le_div_iff_of_neg hj).mpr (by nlinarith [ht j])
    exact hlo.trans hup
  · rintro ⟨hz,hpair⟩
    let L : Finset ι := Finset.univ.filter (fun i => 0<a i)
    let U : Finset ι := Finset.univ.filter (fun i => a i<0)
    have hrow (t : K) (hlo : ∀ i,0<a i → -b i/a i≤t)
        (hup : ∀ i,a i<0 → t≤-b i/a i) : ∀ i,0≤a i*t+b i := by
      intro i
      rcases lt_trichotomy (a i) 0 with hi|hi|hi
      · have := (le_div_iff_of_neg hi).mp (hup i hi)
        nlinarith
      · simpa [hi] using hz i hi
      · have := (div_le_iff₀ hi).mp (hlo i hi)
        nlinarith
    by_cases hL : L.Nonempty
    · obtain ⟨i,hi,hmax⟩ := L.exists_max_image (fun i => -b i/a i) hL
      have hi0 : 0<a i := (Finset.mem_filter.mp hi).2
      refine ⟨-b i/a i,hrow _ ?_ ?_⟩
      · intro j hj
        exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩)
      · intro j hj
        exact hpair i j hi0 hj
    · by_cases hU : U.Nonempty
      · obtain ⟨j,hj,hmin⟩ := U.exists_min_image (fun i => -b i/a i) hU
        refine ⟨-b j/a j,hrow _ ?_ ?_⟩
        · intro i hi
          exact (hL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim
        · intro i hi
          exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
      · refine ⟨0,hrow _ ?_ ?_⟩
        · intro i hi
          exact (hL ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim
        · intro i hi
          exact (hU ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩).elim

structure RationalAffineRow (n : ℕ) where
  constant : ℚ
  coefficient : Fin n → ℚ

namespace RationalAffineRow

variable {n : ℕ}

def eval {K : Type*} [Field K] [CharZero K] (r : RationalAffineRow n)
    (x : Fin n → K) : K :=
  (r.constant : K)+∑ i,(r.coefficient i : K)*x i

def zeroRow : RationalAffineRow n := ⟨0,fun _=>0⟩

def linearCombination (c d : ℚ) (r s : RationalAffineRow n) : RationalAffineRow n :=
  ⟨c*r.constant+d*s.constant,fun i=>c*r.coefficient i+d*s.coefficient i⟩

@[simp] theorem eval_zero {K : Type*} [Field K] [CharZero K] (x : Fin n → K) :
    (zeroRow : RationalAffineRow n).eval x=0 := by simp [eval,zeroRow]

@[simp] theorem eval_linearCombination {K : Type*} [Field K] [CharZero K]
    (c d : ℚ) (r s : RationalAffineRow n) (x : Fin n → K) :
    (linearCombination c d r s).eval x=(c : K)*r.eval x+(d : K)*s.eval x := by
  simp only [eval,linearCombination,Rat.cast_add,Rat.cast_mul,add_mul,
    Finset.sum_add_distrib,mul_add,mul_assoc,← Finset.mul_sum]
  ring

def zeroFirst (r : RationalAffineRow (n+1)) : RationalAffineRow n :=
  ⟨r.constant,fun i=>r.coefficient i.succ⟩

theorem eval_cons {K : Type*} [Field K] [CharZero K]
    (r : RationalAffineRow (n+1)) (t : K) (x : Fin n → K) :
    r.eval (Fin.cons t x)=(r.coefficient 0 : K)*t+r.zeroFirst.eval x := by
  simp [eval,zeroFirst,Fin.sum_univ_succ,add_assoc,add_comm,add_left_comm]

def eliminate {ι : Type*} (r : ι → RationalAffineRow (n+1)) :
    (ι ⊕ (ι × ι)) → RationalAffineRow n
  | Sum.inl i => if (r i).coefficient 0=0 then (r i).zeroFirst else zeroRow
  | Sum.inr (i,j) =>
      if 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0 then
        linearCombination ((r i).coefficient 0)⁻¹ (-((r j).coefficient 0)⁻¹)
          (r i).zeroFirst (r j).zeroFirst
      else zeroRow

theorem eliminate_feasible_iff {K ι : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]
    (r : ι → RationalAffineRow (n+1)) (x : Fin n → K) :
    (∀ j,0≤(eliminate r j).eval x) ↔
      ∃ t : K,∀ i,0≤(r i).eval (Fin.cons t x) := by
  simp only [eval_cons]
  rw [exists_linear_inequality_variable_iff]
  constructor
  · intro hx
    refine ⟨?_,?_⟩
    · intro i hi
      have hiQ : (r i).coefficient 0=0 := by exact_mod_cast hi
      simpa [eliminate,hiQ] using hx (Sum.inl i)
    · intro i j hi hj
      have hiQ : 0<(r i).coefficient 0 := by exact_mod_cast hi
      have hjQ : (r j).coefficient 0<0 := by exact_mod_cast hj
      have h := hx (Sum.inr (i,j))
      have hijQ : 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0 := ⟨hiQ,hjQ⟩
      simp only [eliminate,if_pos hijQ,eval_linearCombination,
        Rat.cast_inv,Rat.cast_neg] at h
      simpa [div_eq_mul_inv,mul_comm] using (neg_le_neg (sub_nonneg.mp
        (show 0≤((r i).coefficient 0 : K)⁻¹*(r i).zeroFirst.eval x-
          ((r j).coefficient 0 : K)⁻¹*(r j).zeroFirst.eval x by nlinarith)))
  · rintro ⟨hz,hpairs⟩ row
    rcases row with i|⟨i,j⟩
    · by_cases hi : (r i).coefficient 0=0
      · simpa [eliminate,hi] using hz i (by exact_mod_cast hi)
      · simp [eliminate,hi]
    · by_cases hij : 0<(r i).coefficient 0 ∧ (r j).coefficient 0<0
      · have h := hpairs i j (by exact_mod_cast hij.1) (by exact_mod_cast hij.2)
        simp only [eliminate,if_pos hij,eval_linearCombination,
          Rat.cast_inv,Rat.cast_neg]
        have h' : ((r j).coefficient 0 : K)⁻¹*(r j).zeroFirst.eval x≤
            ((r i).coefficient 0 : K)⁻¹*(r i).zeroFirst.eval x := by
          simpa [div_eq_mul_inv,mul_comm] using (neg_le_neg h)
        nlinarith
      · simp [eliminate,hij]

end RationalAffineRow

open RationalAffineRow

/-- Every real solution of finitely many rational weak affine
inequalities can be replaced by a rational solution. -/
theorem rational_feasible_of_real_feasible (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] (r : ι → RationalAffineRow n),
      (∃ x : Fin n → ℝ,∀ i,0≤(r i).eval x) →
        ∃ y : Fin n → ℚ,∀ i,0≤(r i).eval y := by
  induction n with
  | zero =>
      intro ι hι r h
      obtain ⟨x,hx⟩ := h
      refine ⟨fun i=>Fin.elim0 i,?_⟩
      intro i
      have hi : 0≤((r i).constant : ℝ) := by simpa [eval] using hx i
      simpa [eval] using (Rat.cast_nonneg (K := ℝ)).mp hi
  | succ n ih =>
      intro ι hι r h
      obtain ⟨x,hx⟩ := h
      have hreal : ∃ x' : Fin n → ℝ,∀ j,0≤(eliminate r j).eval x' := by
        refine ⟨Fin.tail x,(eliminate_feasible_iff r (Fin.tail x)).mpr ⟨x 0,?_⟩⟩
        simpa using hx
      obtain ⟨y,hy⟩ := ih (eliminate r) hreal
      obtain ⟨t,ht⟩ := (eliminate_feasible_iff r y).mp hy
      exact ⟨Fin.cons t y,ht⟩

/-- The same statement with an arbitrary finite variable index. -/
theorem rational_matrix_feasible_of_real_feasible {ι κ : Type*}
    [Fintype ι] [Fintype κ] (A : ι → κ → ℚ) (b : ι → ℚ)
    (h : ∃ x : κ → ℝ,∀ i,0≤(b i : ℝ)+∑ j,(A i j : ℝ)*x j) :
    ∃ y : κ → ℚ,∀ i,0≤b i+∑ j,A i j*y j := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : ι → RationalAffineRow (Fintype.card κ) :=
    fun i=>⟨b i,fun j=>A i (e j)⟩
  obtain ⟨x,hx⟩ := h
  have hreal : ∃ z : Fin (Fintype.card κ) → ℝ,∀ i,0≤(r i).eval z := by
    refine ⟨fun j=>x (e j),?_⟩
    intro i
    simpa [r,eval,← e.sum_comp] using hx i
  obtain ⟨y,hy⟩ := rational_feasible_of_real_feasible _ r hreal
  refine ⟨fun j=>y (e.symm j),?_⟩
  intro i
  simpa [r,eval,← e.sum_comp] using hy i

end PaperVerification.ToricRationalGeometry

#print axioms PaperVerification.ToricRationalGeometry.rational_matrix_feasible_of_real_feasible
