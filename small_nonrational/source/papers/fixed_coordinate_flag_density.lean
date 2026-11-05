module
public import Papers.ConstantRankVectorCharts
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Rational points are dense in the kernel of a fixed rational matrix.
The projector is the already verified constant-rank kernel chart. -/
theorem rational_kernel_density {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : RationalCoordinates A)
    (x : Fin n → ℝ) (hx : A.mulVec x = 0) :
    x ∈ closure {y : Fin n → ℝ | (∀ i, RatScalar (y i)) ∧ A.mulVec y = 0} := by
  classical
  obtain ⟨C⟩ := exists_rowKernelChart A
  let F : (Fin n → ℝ) → (Fin n → ℝ) := C.eval A
  have hF : ContinuousAt F x := by
    exact (C.continuousAt x).comp_of_eq
      ((continuous_const.prodMk continuous_id).continuousAt (x := x)) rfl
  have hFx : F x = x := C.self x hx
  have hcl := mem_closure_image hF (scalarCoordinates_dense n x)
  rw [hFx] at hcl
  apply closure_mono (s := F '' {w : Fin n → ℝ | ∀ i, RatScalar (w i)}) ?_ hcl
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨C.rational hA hw, C.mem A rfl C.independent w⟩

/-- Two normal rows, represented by their coordinate columns. -/
def pair {n : ℕ} (a b : Fin n → ℝ) : Fin n → Fin 2 → ℝ :=
  fun i => ![a i, b i]

theorem minor_pair {n : ℕ} (a b : Fin n → ℝ) (s : Fin 2 → Fin n) :
    minor (pair a b) s = a (s 0) * b (s 1) - a (s 1) * b (s 0) := by
  simp [minor, pair, Matrix.det_fin_two, mul_comm]

/-- The coefficients of a two-by-two minor are linear in the second row. -/
def minorCoefficients {n : ℕ} (a : Fin n → ℝ) (s : Fin 2 → Fin n)
    (i : Fin n) : ℝ :=
  (if i = s 1 then a (s 0) else 0) - (if i = s 0 then a (s 1) else 0)

theorem minorCoefficients_dot {n : ℕ} (a b : Fin n → ℝ) (s : Fin 2 → Fin n) :
    minorCoefficients a s ⬝ᵥ b = minor (pair a b) s := by
  classical
  simp [minorCoefficients, dotProduct, sub_mul, Finset.sum_sub_distrib,
    ite_mul, minor_pair]

theorem minorCoefficients_rational {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, RatScalar (a i)) (s : Fin 2 → Fin n) (i : Fin n) :
    RatScalar (minorCoefficients a s i) := by
  classical
  unfold minorCoefficients
  apply RatScalar.sub
  · split_ifs
    · exact ha _
    · exact RatScalar.zero
  · split_ifs
    · exact ha _
    · exact RatScalar.zero

/-- Holding the first normal fixed and rational, all zero two-by-two minors
are rational linear constraints on the second normal. -/
theorem fixed_first_zero_minor_density {n : ℕ}
    (a b : Fin n → ℝ) (ha : ∀ i, RatScalar (a i)) :
    b ∈ closure {b' : Fin n → ℝ |
      (∀ i, RatScalar (b' i)) ∧ PreservesZeroMinors (pair a b) (pair a b')} := by
  classical
  let e : Fin (Fintype.card (Fin 2 → Fin n)) ≃ (Fin 2 → Fin n) :=
    (Fintype.equivFin (Fin 2 → Fin n)).symm
  let A : Matrix (Fin (Fintype.card (Fin 2 → Fin n))) (Fin n) ℝ :=
    fun k i => if minor (pair a b) (e k) = 0 then minorCoefficients a (e k) i else 0
  have hA : RationalCoordinates A := by
    intro k i
    dsimp only [A]
    split_ifs
    · exact minorCoefficients_rational a ha _ _
    · exact RatScalar.zero
  have hAb : A.mulVec b = 0 := by
    ext k
    by_cases hk : minor (pair a b) (e k) = 0
    · simpa only [A, Matrix.mulVec, if_pos hk, Pi.zero_apply,
        minorCoefficients_dot] using hk
    · simp [A, Matrix.mulVec, hk, dotProduct]
  have hcl := rational_kernel_density A hA b hAb
  apply closure_mono (s := {b' : Fin n → ℝ |
    (∀ i, RatScalar (b' i)) ∧ A.mulVec b' = 0}) ?_ hcl
  intro b' hb'
  refine ⟨hb'.1, ?_⟩
  intro s hs
  have h := congrFun hb'.2 (e.symm s)
  simpa only [A, Matrix.mulVec, Equiv.apply_symm_apply, if_pos hs,
    minorCoefficients_dot, Pi.zero_apply] using h

theorem pair_continuous {n : ℕ} (a : Fin n → ℝ) :
    Continuous (fun b : Fin n → ℝ => pair a b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_const
  · exact continuous_apply i

/-- The full relative density statement for a fixed rational normal.
The first row is literally unchanged, and every labelled maximal-minor sign
is preserved. This is the nontrivial plane-in-three-space flag step. -/
theorem fixed_first_chirotope_density {n : ℕ}
    (a b : Fin n → ℝ) (ha : ∀ i, RatScalar (a i)) :
    b ∈ closure {b' : Fin n → ℝ |
      (∀ i, RatScalar (b' i)) ∧ SameChirotope (pair a b) (pair a b')} := by
  have hcl := fixed_first_zero_minor_density a b ha
  have hopen := (pair_continuous a).continuousAt.tendsto.eventually
    (eventually_nonzero_minor_signs (pair a b))
  have hi := mem_closure_inter_of_eventually hcl hopen
  apply closure_mono (s :=
    {b' : Fin n → ℝ | (∀ i, RatScalar (b' i)) ∧
      PreservesZeroMinors (pair a b) (pair a b')} ∩
    {b' | ∀ s, minor (pair a b) s ≠ 0 →
      SignType.sign (minor (pair a b') s) = SignType.sign (minor (pair a b) s)}) ?_ hi
  intro b' hb'
  refine ⟨hb'.1.1, ?_⟩
  intro s
  by_cases hs : minor (pair a b) s = 0
  · rw [hb'.1.2 s hs, hs]
  · exact hb'.2 s hs

#print axioms rational_kernel_density
#print axioms fixed_first_chirotope_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
