module
public import Papers.AlgebraicChartDensity
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section
noncomputable section

/-!
# Sound rational elimination certificates

An elimination certificate consists of polynomial identities. Its producer
does not decide truth in Lean: the identities are ordinary proof fields,
and the theorem below proves their consequences for every real point.

The distinguished coordinate is `none`; retained coordinates are `some i`.
Elimination uses `a * x_none + b = 0`, with the nonzero coefficient justified
by an explicit divisor of a product of required nonzero minors.
-/

namespace Papers.RationalityTen.RationalElimination

open Set Filter Topology MvPolynomial
open MultiaffineDensity AlgebraicChartDensity
open scoped BigOperators

def EquationsHold {ι : Type*} {m : ℕ}
    (E : Fin m → MvPolynomial ι ℚ) (x : ι → ℝ) : Prop :=
  ∀ j, evalRat (E j) x = 0

def UnitsHold {ι : Type*} {u : ℕ}
    (U : Fin u → MvPolynomial ι ℚ) (x : ι → ℝ) : Prop :=
  ∀ j, evalRat (U j) x ≠ 0

def SolutionSet {ι : Type*} {m u : ℕ}
    (E : Fin m → MvPolynomial ι ℚ) (U : Fin u → MvPolynomial ι ℚ) :
    Set (ι → ℝ) := {x | EquationsHold E x ∧ UnitsHold U x}

def RationallyDenseSystem {ι : Type*} {m u : ℕ}
    (E : Fin m → MvPolynomial ι ℚ) (U : Fin u → MvPolynomial ι ℚ) : Prop :=
  ∀ x ∈ SolutionSet E U,
    x ∈ closure {q | RationalVector q ∧ q ∈ SolutionSet E U}

theorem isOpen_unitsHold {ι : Type*} {u : ℕ}
    (U : Fin u → MvPolynomial ι ℚ) : IsOpen {x | UnitsHold U x} := by
  have h : {x | UnitsHold U x} = ⋂ j, {x | evalRat (U j) x ≠ 0} := by
    ext x
    simp only [UnitsHold, mem_setOf_eq, mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_ne.preimage (evalRat_continuous (U j))

/-- A denominator factor is certified by a polynomial divisibility
identity in the original required nonzero minors. -/
structure UnitWitness {ι : Type*} {u : ℕ}
    (U : Fin u → MvPolynomial ι ℚ) (p : MvPolynomial ι ℚ) where
  count : ℕ
  selected : Fin count → Fin u
  quotient : MvPolynomial ι ℚ
  identity : (∏ j, U (selected j)) = p * quotient

theorem UnitWitness.nonzero {ι : Type*} {u : ℕ}
    {U : Fin u → MvPolynomial ι ℚ} {p : MvPolynomial ι ℚ}
    (W : UnitWitness U p) (x : ι → ℝ) (hx : UnitsHold U x) :
    evalRat p x ≠ 0 := by
  have hid := congrArg (fun q => evalRat q x) W.identity
  simp only [evalRat, eval₂_prod, eval₂_mul] at hid
  have hprod : (∏ j : Fin W.count, evalRat (U (W.selected j)) x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hx (W.selected j))
  intro hzero
  change (∏ j : Fin W.count, evalRat (U (W.selected j)) x) =
    evalRat p x * evalRat W.quotient x at hid
  rw [hzero, zero_mul] at hid
  exact hprod hid

@[simp] theorem evalRat_rename_some {ι : Type*}
    (p : MvPolynomial ι ℚ) (x : Option ι → ℝ) :
    evalRat (rename some p) x = evalRat p (fun i => x (some i)) := by
  simp only [evalRat, eval₂_rename, Function.comp_def]

/-- All polynomial identities necessary for one exact elimination. -/
structure LinearStep (ι : Type*) (m u : ℕ) where
  sourceE : Fin m → MvPolynomial (Option ι) ℚ
  sourceU : Fin u → MvPolynomial (Option ι) ℚ
  targetE : Fin m → MvPolynomial ι ℚ
  targetU : Fin u → MvPolynomial ι ℚ
  a : MvPolynomial ι ℚ
  b : MvPolynomial ι ℚ
  pivot : Fin m
  pivot_identity : sourceE pivot = rename some a * X none + rename some b
  coefficient_or_constant_unit :
    UnitWitness sourceU (rename some a) ⊕ UnitWitness sourceU (rename some b)
  equation_power : Fin m → ℕ
  equation_quotient : Fin m → MvPolynomial (Option ι) ℚ
  equation_identity : ∀ j,
    rename some (targetE j) +
      (rename some a * X none + rename some b) * equation_quotient j =
        (rename some a) ^ equation_power j * sourceE j
  unit_power : Fin u → ℕ
  unit_quotient : Fin u → MvPolynomial (Option ι) ℚ
  unit_identity : ∀ j,
    rename some (targetU j) +
      (rename some a * X none + rename some b) * unit_quotient j =
        (rename some a) ^ unit_power j * sourceU j

def LinearStep.lift {ι : Type*} {m u : ℕ} (C : LinearStep ι m u)
    (y : ι → ℝ) : Option ι → ℝ :=
  Option.elim' (-evalRat C.b y / evalRat C.a y) y

theorem LinearStep.pivot_zero {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (x : Option ι → ℝ)
    (hx : EquationsHold C.sourceE x) :
    evalRat C.a (fun i => x (some i)) * x none +
      evalRat C.b (fun i => x (some i)) = 0 := by
  have h := hx C.pivot
  rw [C.pivot_identity] at h
  simpa only [evalRat, eval₂_add, eval₂_mul, eval₂_X, eval₂_rename,
    Function.comp_def] using h

theorem LinearStep.coefficient_ne_zero {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (x : Option ι → ℝ)
    (hx : x ∈ SolutionSet C.sourceE C.sourceU) :
    evalRat C.a (fun i => x (some i)) ≠ 0 := by
  rcases C.coefficient_or_constant_unit with ha | hb
  · simpa only [evalRat_rename_some] using ha.nonzero x hx.2
  · have hb' : evalRat C.b (fun i => x (some i)) ≠ 0 := by
      simpa only [evalRat_rename_some] using hb.nonzero x hx.2
    intro ha
    have hp := C.pivot_zero x hx.1
    rw [ha, zero_mul, zero_add] at hp
    exact hb' hp

theorem LinearStep.lift_restrict {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (x : Option ι → ℝ)
    (hx : x ∈ SolutionSet C.sourceE C.sourceU) :
    C.lift (fun i => x (some i)) = x := by
  have ha := C.coefficient_ne_zero x hx
  have he := C.pivot_zero x hx.1
  funext i
  cases i with
  | none =>
    change -evalRat C.b (fun i => x (some i)) /
      evalRat C.a (fun i => x (some i)) = x none
    apply (div_eq_iff ha).mpr
    linarith
  | some i => rfl

theorem LinearStep.restrict_solution {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (x : Option ι → ℝ)
    (hx : x ∈ SolutionSet C.sourceE C.sourceU) :
    (fun i => x (some i)) ∈ SolutionSet C.targetE C.targetU := by
  have hp := C.pivot_zero x hx.1
  have ha := C.coefficient_ne_zero x hx
  constructor
  · intro j
    have h := congrArg (fun p => evalRat p x) (C.equation_identity j)
    simp only [evalRat, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_rename, Function.comp_def] at h
    change evalRat (C.targetE j) (fun i => x (some i)) +
      (evalRat C.a (fun i => x (some i)) * x none +
        evalRat C.b (fun i => x (some i))) *
          evalRat (C.equation_quotient j) x =
        evalRat C.a (fun i => x (some i)) ^ C.equation_power j *
          evalRat (C.sourceE j) x at h
    simpa only [hp, hx.1 j, zero_mul, mul_zero, add_zero] using h
  · intro j
    have h := congrArg (fun p => evalRat p x) (C.unit_identity j)
    simp only [evalRat, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_rename, Function.comp_def] at h
    change evalRat (C.targetU j) (fun i => x (some i)) +
      (evalRat C.a (fun i => x (some i)) * x none +
        evalRat C.b (fun i => x (some i))) *
          evalRat (C.unit_quotient j) x =
        evalRat C.a (fun i => x (some i)) ^ C.unit_power j *
          evalRat (C.sourceU j) x at h
    rw [hp, zero_mul, add_zero] at h
    rw [h]
    exact mul_ne_zero (pow_ne_zero _ ha) (hx.2 j)

theorem LinearStep.lift_pivot_zero {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (y : ι → ℝ) (ha : evalRat C.a y ≠ 0) :
    evalRat C.a y * C.lift y none + evalRat C.b y = 0 := by
  dsimp [LinearStep.lift]
  field_simp [ha] <;> ring

theorem LinearStep.lift_solution {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (y : ι → ℝ)
    (hy : y ∈ SolutionSet C.targetE C.targetU) (ha : evalRat C.a y ≠ 0) :
    C.lift y ∈ SolutionSet C.sourceE C.sourceU := by
  have hp := C.lift_pivot_zero y ha
  have hrestrict : (fun i => C.lift y (some i)) = y := rfl
  constructor
  · intro j
    have h := congrArg (fun p => evalRat p (C.lift y)) (C.equation_identity j)
    simp only [evalRat, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_rename, Function.comp_def] at h
    change evalRat (C.targetE j) y +
      (evalRat C.a y * C.lift y none + evalRat C.b y) *
        evalRat (C.equation_quotient j) (C.lift y) =
      evalRat C.a y ^ C.equation_power j * evalRat (C.sourceE j) (C.lift y) at h
    rw [hy.1 j, hp, zero_mul, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ ha)
  · intro j hz
    have h := congrArg (fun p => evalRat p (C.lift y)) (C.unit_identity j)
    simp only [evalRat, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_rename, Function.comp_def] at h
    change evalRat (C.targetU j) y +
      (evalRat C.a y * C.lift y none + evalRat C.b y) *
        evalRat (C.unit_quotient j) (C.lift y) =
      evalRat C.a y ^ C.unit_power j * evalRat (C.sourceU j) (C.lift y) at h
    rw [hp, zero_mul, add_zero, hz, mul_zero] at h
    exact hy.2 j h

theorem LinearStep.continuousAt_lift {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) (y : ι → ℝ) (ha : evalRat C.a y ≠ 0) :
    ContinuousAt C.lift y := by
  apply continuousAt_pi.mpr
  intro i
  cases i with
  | none =>
    exact (evalRat_continuous C.b).continuousAt.neg.div
      (evalRat_continuous C.a).continuousAt ha
  | some i => exact (continuous_apply i).continuousAt

theorem LinearStep.rational_lift {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u) {y : ι → ℝ} (hy : RationalVector y) :
    RationalVector (C.lift y) := by
  intro i
  cases i with
  | none =>
    obtain ⟨a, ha⟩ := evalRat_rational C.a y hy
    obtain ⟨b, hb⟩ := evalRat_rational C.b y hy
    exact ⟨-b / a, by simp only [Rat.cast_div, Rat.cast_neg, ha, hb]; rfl⟩
  | some i => exact hy i

/-- The complete semantic consequence of an exact elimination certificate.
No density assertion is accepted without a proof for the transformed system. -/
theorem LinearStep.preserves_density {ι : Type*} {m u : ℕ}
    (C : LinearStep ι m u)
    (h : RationallyDenseSystem C.targetE C.targetU) :
    RationallyDenseSystem C.sourceE C.sourceU := by
  intro x hx
  let y := fun i => x (some i)
  have hy := C.restrict_solution x hx
  have ha := C.coefficient_ne_zero x hx
  have hbase := h y hy
  have hopen : IsOpen {q | evalRat C.a q ≠ 0} :=
    isOpen_ne.preimage (evalRat_continuous C.a)
  have hh := density_from_local_chart C.lift y
    (SolutionSet C.targetE C.targetU) (SolutionSet C.sourceE C.sourceU)
    {q | evalRat C.a q ≠ 0} hbase hopen ha
    (C.continuousAt_lift y ha)
    (fun _ _ hq => C.rational_lift hq)
    (fun q hq => C.lift_solution q hq.1 hq.2)
  rwa [C.lift_restrict x hx] at hh

theorem empty_equation_system_dense {ι : Type*} {u : ℕ}
    (E : Fin 0 → MvPolynomial ι ℚ) (U : Fin u → MvPolynomial ι ℚ) :
    RationallyDenseSystem E U := by
  intro x hx
  have h := restrict_closure_to_open (rationalVector_dense x)
    (isOpen_unitsHold U) hx.2
  apply closure_mono ?_ h
  rintro q ⟨hr, hu⟩
  exact ⟨hr, ⟨fun j => Fin.elim0 j, hu⟩⟩

theorem zero_equations_system_dense {ι : Type*} {m u : ℕ}
    (E : Fin m → MvPolynomial ι ℚ) (U : Fin u → MvPolynomial ι ℚ)
    (hE : ∀ j, E j = 0) : RationallyDenseSystem E U := by
  intro x hx
  have h := restrict_closure_to_open (rationalVector_dense x)
    (isOpen_unitsHold U) hx.2
  apply closure_mono ?_ h
  rintro q ⟨hr, hu⟩
  refine ⟨hr, ⟨?_, hu⟩⟩
  intro j
  simp only [hE j, evalRat, eval₂_zero]

/-- A literal common equation suffices when every equation is a multiple
of it and the common equation itself occurs in the system. -/
theorem system_dense_of_single_equation {ι : Type*} {m u : ℕ}
    (E : Fin m → MvPolynomial ι ℚ) (U : Fin u → MvPolynomial ι ℚ)
    (p : MvPolynomial ι ℚ) (pivot : Fin m) (hpivot : E pivot = p)
    (quotients : Fin m → MvPolynomial ι ℚ)
    (hidentity : ∀ j, E j = p * quotients j)
    (hdense : ∀ x : ι → ℝ, evalRat p x = 0 →
      x ∈ closure {q | RationalVector q ∧ evalRat p q = 0}) :
    RationallyDenseSystem E U := by
  intro x hx
  have hz : evalRat p x = 0 := by
    rw [← hpivot]
    exact hx.1 pivot
  have h := restrict_closure_to_open (hdense x hz) (isOpen_unitsHold U) hx.2
  apply closure_mono ?_ h
  rintro q ⟨⟨hr, he⟩, hu⟩
  refine ⟨hr, ⟨?_, hu⟩⟩
  intro j
  rw [hidentity j]
  change eval₂ (Rat.castHom ℝ) q p = 0 at he
  simp only [evalRat, eval₂_mul, he, zero_mul]

/-- Removing powers and factors is valid only with explicit identities
and a proof that every removed factor is a unit on the allowed locus. -/
structure FactorReduction {ι : Type*} {u : ℕ}
    (U : Fin u → MvPolynomial ι ℚ) (P Q : MvPolynomial ι ℚ) where
  power : ℕ
  power_pos : 0 < power
  multiplier : MvPolynomial ι ℚ
  unit : MvPolynomial ι ℚ
  unit_witness : UnitWitness U unit
  forward_identity : P * multiplier = unit * Q ^ power
  reverse_quotient : MvPolynomial ι ℚ
  reverse_identity : P = Q * reverse_quotient

theorem FactorReduction.zero_iff {ι : Type*} {u : ℕ}
    {U : Fin u → MvPolynomial ι ℚ} {P Q : MvPolynomial ι ℚ}
    (C : FactorReduction U P Q) (x : ι → ℝ) (hx : UnitsHold U x) :
    evalRat P x = 0 ↔ evalRat Q x = 0 := by
  constructor
  · intro hp
    have h := congrArg (fun p => evalRat p x) C.forward_identity
    simp only [evalRat, eval₂_mul, eval₂_pow] at h
    change evalRat P x * evalRat C.multiplier x =
      evalRat C.unit x * evalRat Q x ^ C.power at h
    rw [hp, zero_mul] at h
    have hpow := (mul_eq_zero.mp h.symm).resolve_left (C.unit_witness.nonzero x hx)
    exact eq_zero_of_pow_eq_zero hpow
  · intro hq
    have h := congrArg (fun p => evalRat p x) C.reverse_identity
    change eval₂ (Rat.castHom ℝ) x Q = 0 at hq
    simpa only [evalRat, eval₂_mul, hq, zero_mul] using h

theorem dense_system_of_factor_reductions {ι : Type*} {m u : ℕ}
    (E E' : Fin m → MvPolynomial ι ℚ) (U : Fin u → MvPolynomial ι ℚ)
    (C : ∀ j, FactorReduction U (E j) (E' j))
    (hdense : RationallyDenseSystem E' U) : RationallyDenseSystem E U := by
  have hsets : SolutionSet E U = SolutionSet E' U := by
    ext x
    constructor
    · rintro ⟨he, hu⟩
      exact ⟨fun j => ((C j).zero_iff x hu).mp (he j), hu⟩
    · rintro ⟨he, hu⟩
      exact ⟨fun j => ((C j).zero_iff x hu).mpr (he j), hu⟩
  intro x hx
  rw [hsets] at hx ⊢
  exact hdense x hx

end Papers.RationalityTen.RationalElimination
