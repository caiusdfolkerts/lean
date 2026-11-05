module

public import VolumePolynomials.Definitions
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section

/-!
# A finite rational shape-forcing system

This is an evaluation form of the coefficient conditions in Section 7.  Its
unknowns are the two parameters and all ordinary cubic coefficients in nine
variables.  The polynomial `volumeSymbol w` is the ordinary coefficient
polynomial evaluated at the symbolic weight vector `w`.

The system has 39 equations and eight strict inequalities.  No mixed-volume
coefficient, geometric equality case, or realization condition is built into
its definition.  Membership in the actual volume locus is imposed separately.
-/

open scoped BigOperators

namespace VolumePolynomials.ShapeConditions

abbrev Label := Fin 9
abbrev Variable := Fin 2 ⊕ MultiIndex 9 3
abbrev RationalPolynomial := MvPolynomial Variable ℚ

def e₁ : Label := 0
def e₂ : Label := 1
def e₃ : Label := 2
def sᵥ : Label := 3
def s𝓌 : Label := 4
def s𝓏 : Label := 5
def bodyA : Label := 6
def bodyB : Label := 7
def bodyC : Label := 8

def segmentIndex (i : Fin 6) : Label := i.castLE (by decide)
def frameIndex (i : Fin 3) : Label := i.castLE (by decide)

def parameter : RationalPolynomial := MvPolynomial.X (Sum.inl 0)
def areaParameter : RationalPolynomial := MvPolynomial.X (Sum.inl 1)

def unitWeight {R : Type*} [Zero R] [One R] (i : Label) : Label → R :=
  fun j => if j = i then 1 else 0

def volumeSymbol (w : Label → RationalPolynomial) : RationalPolynomial :=
  ∑ α : MultiIndex 9 3,
    MvPolynomial.X (Sum.inr α) * ∏ i, w i ^ (α.1 i : ℕ)

def extrusionSymbol (w : Label → RationalPolynomial) (h : Label) : RationalPolynomial :=
  volumeSymbol (w + unitWeight h) - volumeSymbol w

def lastWeight : Label → RationalPolynomial :=
  fun i => parameter * unitWeight bodyC i + unitWeight e₁ i

/-- The eighteen zero-volume tests force all six calibrated labels to have
affine dimension at most one, once the frame has positive total volume. -/
def segmentEquations : List RationalPolynomial :=
  (List.finRange 6).flatMap fun h =>
    (List.finRange 3).map fun j =>
      volumeSymbol (unitWeight (segmentIndex h) + unitWeight (frameIndex j))

/-- Explicit equations, with the unspecified cubic coefficients left free. -/
def equations : List RationalPolynomial := segmentEquations ++
  [ volumeSymbol (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight sᵥ + unitWeight e₂ + unitWeight e₃),
    volumeSymbol (unitWeight sᵥ + unitWeight e₁ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight sᵥ + unitWeight e₁ + unitWeight e₂) - 1,
    volumeSymbol (unitWeight s𝓌 + unitWeight e₂ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₂),
    volumeSymbol (unitWeight s𝓏 + unitWeight e₂ + unitWeight e₃) - 1,
    volumeSymbol (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₃) -
      MvPolynomial.C (2 / 3 : ℚ),
    volumeSymbol (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₂) - 1,
    volumeSymbol (unitWeight sᵥ + unitWeight s𝓌 + unitWeight s𝓏) -
      MvPolynomial.C (4 / 3 : ℚ),
    volumeSymbol (unitWeight bodyA + unitWeight e₁ + unitWeight e₂),
    volumeSymbol (unitWeight bodyB + unitWeight e₁ + unitWeight e₃),
    volumeSymbol (unitWeight bodyC + unitWeight e₂ + unitWeight e₃),
    extrusionSymbol (unitWeight bodyA) sᵥ - extrusionSymbol (unitWeight bodyB) sᵥ,
    extrusionSymbol (unitWeight bodyA + unitWeight bodyB) sᵥ -
      4 * extrusionSymbol (unitWeight bodyA) sᵥ,
    extrusionSymbol (unitWeight bodyB) s𝓌 - extrusionSymbol (unitWeight bodyC) s𝓌,
    extrusionSymbol (unitWeight bodyB + unitWeight bodyC) s𝓌 -
      4 * extrusionSymbol (unitWeight bodyB) s𝓌,
    extrusionSymbol (unitWeight bodyA) s𝓏 - extrusionSymbol lastWeight s𝓏,
    extrusionSymbol (unitWeight bodyA + lastWeight) s𝓏 -
      4 * extrusionSymbol (unitWeight bodyA) s𝓏,
    areaParameter - extrusionSymbol (unitWeight bodyA) e₃ ]

def inequalities : List RationalPolynomial :=
  [ parameter, 1 - parameter,
    extrusionSymbol (unitWeight bodyA) e₃,
    extrusionSymbol (unitWeight bodyB) e₂,
    extrusionSymbol (unitWeight bodyC) e₁,
    extrusionSymbol (unitWeight bodyA) sᵥ,
    extrusionSymbol (unitWeight bodyB) s𝓌,
    extrusionSymbol (unitWeight bodyA) s𝓏 ]

def assignment (lam a : ℝ) (c : Coefficients 9 3) : Variable → ℝ :=
  Sum.elim (fun i => if i = 0 then lam else a) c

def polynomialValue (lam a : ℝ) (c : Coefficients 9 3) : RationalPolynomial →+* ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (assignment lam a c)

def Holds (lam a : ℝ) (c : Coefficients 9 3) : Prop :=
  (∀ p ∈ equations, polynomialValue lam a c p = 0) ∧
  (∀ p ∈ inequalities, 0 < polynomialValue lam a c p)

/-- The actual geometric locus is not absorbed into the polynomial tests. -/
def Feasible (lam a : ℝ) : Prop :=
  ∃ c ∈ VolumeLocus 9 3, Holds lam a c

def extrusionValue (V : (Label → ℝ) → ℝ) (w : Label → ℝ) (h : Label) : ℝ :=
  V (w + unitWeight h) - V w

def lastNumericalWeight (lam : ℝ) : Label → ℝ :=
  fun i => lam * unitWeight bodyC i + unitWeight e₁ i

/-- The exact ordinary-volume meaning of the finite rational system. -/
def OrdinaryConditions (lam a : ℝ) (V : (Label → ℝ) → ℝ) : Prop :=
  (∀ h : Fin 6, ∀ j : Fin 3,
    V (unitWeight (segmentIndex h) + unitWeight (frameIndex j)) = 0) ∧
  (V (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) = 1 ∧
    V (unitWeight sᵥ + unitWeight e₂ + unitWeight e₃) = 0 ∧
    V (unitWeight sᵥ + unitWeight e₁ + unitWeight e₃) = 1 ∧
    V (unitWeight sᵥ + unitWeight e₁ + unitWeight e₂) = 1 ∧
    V (unitWeight s𝓌 + unitWeight e₂ + unitWeight e₃) = 1 ∧
    V (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₃) = 1 ∧
    V (unitWeight s𝓌 + unitWeight e₁ + unitWeight e₂) = 0 ∧
    V (unitWeight s𝓏 + unitWeight e₂ + unitWeight e₃) = 1 ∧
    V (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₃) = (2 / 3 : ℝ) ∧
    V (unitWeight s𝓏 + unitWeight e₁ + unitWeight e₂) = 1 ∧
    V (unitWeight sᵥ + unitWeight s𝓌 + unitWeight s𝓏) = (4 / 3 : ℝ) ∧
    V (unitWeight bodyA + unitWeight e₁ + unitWeight e₂) = 0 ∧
    V (unitWeight bodyB + unitWeight e₁ + unitWeight e₃) = 0 ∧
    V (unitWeight bodyC + unitWeight e₂ + unitWeight e₃) = 0 ∧
    extrusionValue V (unitWeight bodyA) sᵥ = extrusionValue V (unitWeight bodyB) sᵥ ∧
    extrusionValue V (unitWeight bodyA + unitWeight bodyB) sᵥ =
      4 * extrusionValue V (unitWeight bodyA) sᵥ ∧
    extrusionValue V (unitWeight bodyB) s𝓌 = extrusionValue V (unitWeight bodyC) s𝓌 ∧
    extrusionValue V (unitWeight bodyB + unitWeight bodyC) s𝓌 =
      4 * extrusionValue V (unitWeight bodyB) s𝓌 ∧
    extrusionValue V (unitWeight bodyA) s𝓏 = extrusionValue V (lastNumericalWeight lam) s𝓏 ∧
    extrusionValue V (unitWeight bodyA + lastNumericalWeight lam) s𝓏 =
      4 * extrusionValue V (unitWeight bodyA) s𝓏 ∧
    a = extrusionValue V (unitWeight bodyA) e₃) ∧
  (0 < lam ∧ lam < 1 ∧
    0 < extrusionValue V (unitWeight bodyA) e₃ ∧
    0 < extrusionValue V (unitWeight bodyB) e₂ ∧
    0 < extrusionValue V (unitWeight bodyC) e₁ ∧
    0 < extrusionValue V (unitWeight bodyA) sᵥ ∧
    0 < extrusionValue V (unitWeight bodyB) s𝓌 ∧
    0 < extrusionValue V (unitWeight bodyA) s𝓏)

@[simp] theorem equations_length : equations.length = 39 := by
  first
  | simp [equations, segmentEquations, List.length_flatMap, List.map_const]

@[simp] theorem inequalities_length : inequalities.length = 8 := rfl

@[simp] theorem polynomialValue_parameter (lam a : ℝ) (c : Coefficients 9 3) :
    polynomialValue lam a c parameter = lam := by
  first
  | simp [polynomialValue, parameter, assignment]

@[simp] theorem polynomialValue_areaParameter (lam a : ℝ) (c : Coefficients 9 3) :
    polynomialValue lam a c areaParameter = a := by
  first
  | simp [polynomialValue, areaParameter, assignment]

@[simp] theorem polynomialValue_coefficient (lam a : ℝ) (c : Coefficients 9 3)
    (α : MultiIndex 9 3) :
    polynomialValue lam a c (MvPolynomial.X (Sum.inr α)) = c α := by
  first
  | simp [polynomialValue, assignment]

@[simp] theorem polynomialValue_C (lam a : ℝ) (c : Coefficients 9 3) (r : ℚ) :
    polynomialValue lam a c (MvPolynomial.C r) = (r : ℝ) := by
  first
  | simp [polynomialValue]

@[simp] theorem polynomialValue_unitWeight (lam a : ℝ) (c : Coefficients 9 3)
    (i j : Label) :
    polynomialValue lam a c (unitWeight i j) = unitWeight i j := by
  first
  | simp [unitWeight]

/-- Symbolic evaluation is exactly ordinary polynomial evaluation, with no
factorial rescaling of the ordinary coefficients. -/
@[simp] theorem polynomialValue_volumeSymbol (lam a : ℝ) (c : Coefficients 9 3)
    (w : Label → RationalPolynomial) :
    polynomialValue lam a c (volumeSymbol w) =
      evaluate c (fun i => polynomialValue lam a c (w i)) := by
  first
  | classical
    simp [volumeSymbol, evaluate]

@[simp] theorem polynomialValue_extrusionSymbol (lam a : ℝ) (c : Coefficients 9 3)
    (w : Label → RationalPolynomial) (h : Label) :
    polynomialValue lam a c (extrusionSymbol w h) =
      evaluate c ((fun i => polynomialValue lam a c (w i)) + unitWeight h) -
      evaluate c (fun i => polynomialValue lam a c (w i)) := by
  first
  | simp [extrusionSymbol, Pi.add_def]

@[simp] theorem polynomialValue_lastWeight (lam a : ℝ) (c : Coefficients 9 3)
    (i : Label) :
    polynomialValue lam a c (lastWeight i) =
      lam * unitWeight bodyC i + unitWeight e₁ i := by
  first
  | simp [lastWeight]

theorem holds_iff_ordinary (lam a : ℝ) (c : Coefficients 9 3) :
    Holds lam a c ↔ OrdinaryConditions lam a (evaluate c) := by
  first
  | simp only [Holds, equations, List.forall_mem_append, segmentEquations,
      List.forall_mem_flatMap, List.forall_mem_map]
    simp [inequalities, OrdinaryConditions, extrusionValue, lastNumericalWeight,
      Pi.add_def, map_ofNat, sub_eq_zero, sub_pos, and_assoc]
    all_goals
      intros
      rfl

theorem Holds.parameter_range {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) : 0 < lam ∧ lam < 1 := by
  first
  | have h₀ := h.2 parameter (by simp [inequalities])
    have h₁ := h.2 (1 - parameter) (by simp [inequalities])
    simp only [polynomialValue_parameter, map_sub, map_one] at h₀ h₁
    exact ⟨h₀, sub_pos.mp h₁⟩

theorem Holds.segment_zero {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) (i : Fin 6) (j : Fin 3) :
    evaluate c (unitWeight (segmentIndex i) + unitWeight (frameIndex j)) = 0 := by
  first
  | have hm : volumeSymbol (unitWeight (segmentIndex i) + unitWeight (frameIndex j)) ∈
        equations := by
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_finRange i, ?_⟩
      exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
    simpa [Pi.add_def] using h.1 _ hm

theorem Holds.frame_volume {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) :
    evaluate c (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) = 1 := by
  first
  | have hm := h.1 (volumeSymbol (unitWeight e₁ + unitWeight e₂ + unitWeight e₃) - 1)
      (by simp [equations])
    simpa [Pi.add_def, sub_eq_zero] using hm

theorem Holds.area_value {lam a : ℝ} {c : Coefficients 9 3}
    (h : Holds lam a c) :
    a = evaluate c (unitWeight bodyA + unitWeight e₃) - evaluate c (unitWeight bodyA) := by
  first
  | have hm := h.1 (areaParameter - extrusionSymbol (unitWeight bodyA) e₃)
      (by simp [equations])
    simpa [Pi.add_def, sub_eq_zero] using hm

end VolumePolynomials.ShapeConditions
