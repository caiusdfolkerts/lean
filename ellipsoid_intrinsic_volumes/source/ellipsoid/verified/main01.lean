module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.LinearAlgebra.Lagrange
public import tau_ceti.ring_theory.polynomial.roots
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import tau_ceti.topology.algebra.polynomial.basic
public import tau_ceti.measure_theory.constructions.haar_to_sphere

/- Generated ordinary proof stage. See audit/staged_ellipsoid_main/Main01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Ellipsoid/Definitions.lean -/



/-!
# Geometric quantities in the ellipsoid manuscript

Intrinsic volumes in this file are defined from the *actual Lebesgue volumes*
of parallel bodies. The polynomial is recovered by interpolation at the
nonnegative integers. Thus an integral formula for these quantities requires
a proof of the Steiner polynomial identity; it is not part of the definition.

An ellipsoid is represented by its centre, an orthogonal frame, and positive
semiaxes. Repeated semiaxes are allowed. This is the usual full-dimensional
ellipsoid parameterization, not a regular-spectrum restriction.
-/

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators Pointwise

namespace EllipsoidVerification

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : Space n) 1)).toReal

def parallelBody {n : ℕ} (K : Set (Space n)) (r : ℝ) : Set (Space n) :=
  K + Metric.closedBall 0 r

def parallelVolume {n : ℕ} (K : Set (Space n)) (r : ℝ) : ℝ :=
  (volume (parallelBody K r)).toReal

def steinerInterpolant {n : ℕ} (K : Set (Space n)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun i : Fin (n + 1) => (i.val : ℝ))
    (fun i => parallelVolume K i.val)

def intrinsicVolume {n : ℕ} (K : Set (Space n)) (k : ℕ) : ℝ :=
  if k ≤ n then (steinerInterpolant K).coeff (n - k) / unitBallVolume (n - k) else 0

/-- The literal geometric correspondence that must be proved before using
the interpolated coefficients as the coefficients of every parallel body. -/
def HasSteinerFormula {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ r : ℝ, 0 ≤ r → parallelVolume K r = (steinerInterpolant K).eval r

def axisMap {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun i => a i * x i)

structure FullEllipsoid (n : ℕ) where
  center : Space n
  frame : Space n ≃ₗᵢ[ℝ] Space n
  semiaxis : Fin n → ℝ
  semiaxis_pos : ∀ i, 0 < semiaxis i

namespace FullEllipsoid

def body {n : ℕ} (E : FullEllipsoid n) : Set (Space n) :=
  (fun x => E.center + E.frame (axisMap E.semiaxis x)) '' Metric.closedBall 0 1

def volume {n : ℕ} (E : FullEllipsoid n) (k : ℕ) : ℝ :=
  intrinsicVolume E.body k

def sphere (n : ℕ) (r : ℝ) (hr : 0 < r) : FullEllipsoid n where
  center := 0
  frame := LinearIsometryEquiv.refl ℝ (Space n)
  semiaxis := fun _ => r
  semiaxis_pos := fun _ => hr

def axesIn {n : ℕ} (E : FullEllipsoid n) (a b : ℝ) : Prop :=
  ∀ i, a ≤ E.semiaxis i ∧ E.semiaxis i ≤ b

def congruent {n : ℕ} (E F : FullEllipsoid n) : Prop :=
  ∃ T : Space n ≃ᵢ Space n, T '' E.body = F.body

def axisDistance {n : ℕ} (E F : FullEllipsoid n) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ⨆ i : Fin n, |E.semiaxis i - F.semiaxis (σ i)|

def volumeDistance {n : ℕ} (E F : FullEllipsoid n) : ℝ :=
  ⨆ k : Fin n, |E.volume (k.val + 1) - F.volume (k.val + 1)|

end FullEllipsoid

/-- Theorem 1.1, with literal sets and Euclidean congruence. -/
def IntrinsicReconstruction : Prop :=
  ∀ (n : ℕ) (E F : FullEllipsoid n),
    (∀ k : ℕ, 1 ≤ k → k ≤ n → E.volume k = F.volume k) → E.congruent F

/-- The quantitative estimate of Theorem 1.2. The positive dimension
condition gives the intended meaning of the exponent `1 / n`. -/
def UniformHolderRecovery : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∃ C : ℝ, 0 < C ∧ ∀ E F : FullEllipsoid n,
      E.axesIn a b → F.axesIn a b →
      E.axisDistance F ≤ C * Real.rpow (E.volumeDistance F) (1 / (n : ℝ))

/-- No exponent larger than `1/n` works in any semiaxis neighborhood of
a sphere. The inequality is explicitly violated for every proposed constant. -/
def SharpHolderRecovery : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        E.axesIn a b ∧ F.axesIn a b ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧
        C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F

/-- The additional equal-volume sharpness clause of Theorem 1.2. -/
def SharpHolderRecoveryAtFixedVolume : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        E.axesIn a b ∧ F.axesIn a b ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧ E.volume n = F.volume n ∧
        C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F

theorem steinerInterpolant_eval_node {n : ℕ} (K : Set (Space n)) (i : Fin (n + 1)) :
    (steinerInterpolant K).eval (i.val : ℝ) = parallelVolume K i.val := by
  classical
  unfold steinerInterpolant
  apply Lagrange.eval_interpolate_at_node
    (v := fun j : Fin (n + 1) => (j.val : ℝ))
    (fun j : Fin (n + 1) => parallelVolume K j.val)
  · intro i hi j hj h
    exact Fin.ext (Nat.cast_injective h)
  · exact Finset.mem_univ i

@[fun_prop] theorem continuous_axisMap {n : ℕ} (a : Fin n → ℝ) :
    Continuous (axisMap a) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i => continuous_const.mul (PiLp.continuous_apply 2 _ i)

theorem FullEllipsoid.isCompact_body {n : ℕ} (E : FullEllipsoid n) :
    IsCompact E.body := by
  apply (isCompact_closedBall (0 : Space n) 1).image
  exact continuous_const.add (E.frame.continuous.comp (continuous_axisMap E.semiaxis))

theorem FullEllipsoid.nonempty_body {n : ℕ} (E : FullEllipsoid n) :
    E.body.Nonempty := by
  exact Set.Nonempty.image _ ⟨0, by simp⟩

end EllipsoidVerification
end
end CanonicalSource0

section CanonicalSource1
/- Source: Ellipsoid/CoefficientDefinitions.lean -/



noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace EllipsoidVerification

/-- Coefficients of a degree-`n` polynomial in the squared variable. -/
abbrev Coefficients (n : ℕ) := Fin (n + 1) → ℝ

def coefficientPolynomial {n : ℕ} (e : Coefficients n) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), e j * t ^ (2 * j.val)

def coefficientHead {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then e j * t ^ (2 * j.val) else 0

def coefficientDerivative {n : ℕ} (e : Coefficients n) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), (2 * j.val : ℝ) * e j * t ^ (2 * j.val - 1)

def coefficientHeadDerivative {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then
    (2 * j.val : ℝ) * e j * t ^ (2 * j.val - 1) else 0

/-- The integral in equation (3), without any real-rootedness assumption. -/
def coefficientTransform {n : ℕ} (e : Coefficients n) (k : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (1 / 2 : ℝ) * Real.rpow t (-(k : ℝ)) *
    (coefficientHead e k t * coefficientDerivative e t -
      coefficientHeadDerivative e k t * coefficientPolynomial e t) *
    Real.rpow (coefficientPolynomial e t) (-(3 / 2 : ℝ))

def mellinMoment {n : ℕ} (e : Coefficients n) (r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.rpow t (r - 1) *
    Real.rpow (coefficientPolynomial e t) (-(3 / 2 : ℝ))

def coefficientAdmissible {n : ℕ} (e : Coefficients n) : Prop :=
  (∀ j, 0 ≤ e j) ∧ 0 < e 0 ∧ 0 < e (Fin.last n)

/-- There are `m` free internal coefficients and degree `m+1`. -/
def fixedEndpoints (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) : Coefficients (m + 1) :=
  fun j => if h0 : j.val = 0 then e0 else
    if hn : j.val = m + 1 then en else x ⟨j.val - 1, by omega⟩

def coefficientMap (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun k => coefficientTransform (fixedEndpoints m e0 en x) (k.val + 1)

def principalJacobianPositive {m : ℕ} (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ s : Finset (Fin m), 0 < (J.submatrix (fun i : s => i.val) (fun i : s => i.val)).det

def coefficientJacobian {n : ℕ} (e : Coefficients n)
    (k j : Fin (n - 1)) : ℝ :=
  let kk := k.val + 1
  let jj := j.val + 1
  (1 / 2 : ℝ) * if k ≤ j then
    ∑ l : Fin (n + 1), if l.val < kk then
      ((kk : ℝ) - l.val) * e l *
        mellinMoment e (2 * (jj : ℝ) - (kk : ℝ) + 2 * (l.val : ℝ)) else 0
  else
    ∑ l : Fin (n + 1), if kk < l.val then
      ((l.val : ℝ) - kk) * e l *
        mellinMoment e (2 * (jj : ℝ) - (kk : ℝ) + 2 * (l.val : ℝ)) else 0

theorem coefficientPolynomial_nonneg {n : ℕ} {e : Coefficients n}
    (he : ∀ j, 0 ≤ e j) (t : ℝ) : 0 ≤ coefficientPolynomial e t := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (he j) (even_two_mul j.val |>.pow_nonneg t)

theorem coefficientPolynomial_ge_constant {n : ℕ} {e : Coefficients n}
    (he : ∀ j, 0 ≤ e j) (t : ℝ) : e 0 ≤ coefficientPolynomial e t := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      mul_nonneg (he j) (even_two_mul j.val |>.pow_nonneg t)) (Finset.mem_univ 0)
  simpa [coefficientPolynomial] using h

theorem coefficientPolynomial_pos {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (t : ℝ) : 0 < coefficientPolynomial e t :=
  he.2.1.trans_le (coefficientPolynomial_ge_constant he.1 t)

theorem coefficientPolynomial_ge_leading {n : ℕ} {e : Coefficients n}
    (he : ∀ j, 0 ≤ e j) (t : ℝ) :
    e (Fin.last n) * t ^ (2 * n) ≤ coefficientPolynomial e t := by
  exact Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      mul_nonneg (he j) (even_two_mul j.val |>.pow_nonneg t)) (Finset.mem_univ (Fin.last n))

theorem fixedEndpoints_zero (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    fixedEndpoints m e0 en x 0 = e0 := by simp [fixedEndpoints]

theorem fixedEndpoints_last (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    fixedEndpoints m e0 en x (Fin.last (m + 1)) = en := by simp [fixedEndpoints]

theorem fixedEndpoints_internal (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) (i : Fin m) :
    fixedEndpoints m e0 en x ⟨i.val + 1, by omega⟩ = x i := by
  simp [fixedEndpoints, show i.val ≠ m by omega]

theorem fixedEndpoints_admissible {m : ℕ} {e0 en : ℝ} {x : Fin m → ℝ}
    (h0 : 0 < e0) (hn : 0 < en) (hx : 0 ≤ x) :
    coefficientAdmissible (fixedEndpoints m e0 en x) := by
  refine ⟨?_, by simpa [fixedEndpoints_zero] using h0,
    by simpa [fixedEndpoints_last] using hn⟩
  intro j
  unfold fixedEndpoints
  split_ifs <;> first | exact h0.le | exact hn.le | exact hx _

@[fun_prop] theorem continuous_coefficientPolynomial {n : ℕ} (e : Coefficients n) :
    Continuous (coefficientPolynomial e) := by
  unfold coefficientPolynomial
  fun_prop

@[fun_prop] theorem continuous_coefficientPolynomial_coefficients {n : ℕ} (t : ℝ) :
    Continuous (fun e : Coefficients n => coefficientPolynomial e t) := by
  unfold coefficientPolynomial
  fun_prop

end EllipsoidVerification
end
end CanonicalSource1

section CanonicalSource2
/- Source: Ellipsoid/Semiaxes.lean -/



noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators Pointwise

namespace EllipsoidVerification

def axisCoefficientPolynomial {n : ℕ} (a : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (1 + C (a i ^ 2) * X)

def axisCoefficients {n : ℕ} (a : Fin n → ℝ) : Coefficients n :=
  fun j => (axisCoefficientPolynomial a).coeff j.val

def inverseSquareRoot {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  -(a i ^ 2)⁻¹

theorem axisCoefficientPolynomial_factorization {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    axisCoefficientPolynomial a = C (∏ i, a i ^ 2) *
      ∏ i, (X - C (inverseSquareRoot a i)) := by
  unfold axisCoefficientPolynomial
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  unfold inverseSquareRoot
  have hai : a i ^ 2 ≠ 0 := pow_ne_zero _ (ha i).ne'
  rw [mul_sub, ← C_mul, mul_neg, mul_inv_cancel₀ hai]
  simp only [C_neg, map_one, sub_neg_eq_add]
  ring

theorem axisCoefficientPolynomial_roots {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) :
    (axisCoefficientPolynomial a).roots = Finset.univ.val.map (inverseSquareRoot a) := by
  rw [axisCoefficientPolynomial_factorization a ha]
  exact roots_C_mul_prod_X_sub_C _ _
    (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (ha i).ne')

/-- Equality of finite value multisets gives an actual permutation matching
every occurrence, including repeated values. -/
theorem exists_perm_of_multiset_map_eq {n : ℕ} {f g : Fin n → ℝ}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, f i = g (σ i) := by
  classical
  have hc (x : ℝ) : Fintype.card {i : Fin n // f i = x} =
      Fintype.card {i : Fin n // g i = x} := by
    have hh := congrArg (Multiset.count x) h
    simpa only [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def,
      Fintype.card_subtype, eq_comm] using hh
  let σ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv fun x => Fintype.equivOfCardEq (hc x)
  exact ⟨σ, fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

theorem semiaxes_perm_of_axisPolynomial_eq {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : axisCoefficientPolynomial a = axisCoefficientPolynomial b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a i = b (σ i) := by
  have hr := congrArg Polynomial.roots h
  rw [axisCoefficientPolynomial_roots a ha, axisCoefficientPolynomial_roots b hb] at hr
  obtain ⟨σ, hσ⟩ := exists_perm_of_multiset_map_eq hr
  refine ⟨σ, fun i => ?_⟩
  have hi := hσ i
  dsimp [inverseSquareRoot] at hi
  have hs : a i ^ 2 = b (σ i) ^ 2 := inv_injective (neg_injective hi)
  nlinarith [ha i, hb (σ i)]

def permuteAxes {n : ℕ} (σ : Equiv.Perm (Fin n)) : Space n ≃ₗᵢ[ℝ] Space n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

theorem permuteAxes_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Space n) (i : Fin n) :
    permuteAxes σ x i = x (σ.symm i) := rfl

theorem permuteAxes_axisMap {n : ℕ} {a b : Fin n → ℝ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, a i = b (σ i)) (x : Space n) :
    permuteAxes σ (axisMap a x) = axisMap b (permuteAxes σ x) := by
  ext i
  simpa [permuteAxes_apply, axisMap] using
    congrArg (fun r : ℝ => r * x (σ.symm i)) (hσ (σ.symm i))

def FullEllipsoid.placement {n : ℕ} (E : FullEllipsoid n) : Space n ≃ᵢ Space n :=
  E.frame.toIsometryEquiv.trans (IsometryEquiv.vaddConst E.center)

@[simp] theorem FullEllipsoid.placement_apply {n : ℕ} (E : FullEllipsoid n) (x : Space n) :
    E.placement x = E.center + E.frame x := by
  simp [FullEllipsoid.placement, IsometryEquiv.vaddConst, add_comm]

/-- A permutation of positive semiaxes gives an isometry between the actual
ellipsoid bodies. No simple-spectrum hypothesis is used. -/
theorem FullEllipsoid.congruent_of_semiaxes_perm {n : ℕ} (E F : FullEllipsoid n)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, E.semiaxis i = F.semiaxis (σ i)) :
    E.congruent F := by
  let P := permuteAxes σ
  let T := E.placement.symm.trans (P.toIsometryEquiv.trans F.placement)
  refine ⟨T, ?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨P x, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, P.norm_map] using hx
    · change F.center + F.frame (axisMap F.semiaxis (P x)) =
        T (E.center + E.frame (axisMap E.semiaxis x))
      rw [← F.placement_apply, ← E.placement_apply]
      simp only [T, IsometryEquiv.trans_apply, IsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.coe_toIsometryEquiv]
      exact congrArg F.placement (permuteAxes_axisMap σ hσ x).symm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨E.placement (axisMap E.semiaxis (P.symm x)), ?_, ?_⟩
    · refine ⟨P.symm x, ?_, by simp⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, P.symm.norm_map] using hx
    · change T (E.placement (axisMap E.semiaxis (P.symm x))) =
        F.center + F.frame (axisMap F.semiaxis x)
      rw [← F.placement_apply]
      simp only [T, IsometryEquiv.trans_apply, IsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.coe_toIsometryEquiv]
      rw [permuteAxes_axisMap σ hσ, P.apply_symm_apply]

theorem FullEllipsoid.congruent_of_axisPolynomial_eq {n : ℕ} (E F : FullEllipsoid n)
    (h : axisCoefficientPolynomial E.semiaxis = axisCoefficientPolynomial F.semiaxis) :
    E.congruent F := by
  obtain ⟨σ, hσ⟩ := semiaxes_perm_of_axisPolynomial_eq E.semiaxis_pos F.semiaxis_pos h
  exact E.congruent_of_semiaxes_perm F σ hσ

end EllipsoidVerification
end
end CanonicalSource2

section CanonicalSource3
/- Source: Ellipsoid/SupportGeometry.lean -/



noncomputable section

open MeasureTheory Set
open scoped BigOperators Pointwise InnerProductSpace RealInnerProductSpace

namespace EllipsoidVerification

def axisLinear {n : ℕ} (a : Fin n → ℝ) : Space n →ₗ[ℝ] Space n where
  toFun := axisMap a
  map_add' x y := by ext i; simp [axisMap]; ring
  map_smul' r x := by ext i; simp [axisMap]; ring

def axisCLM {n : ℕ} (a : Fin n → ℝ) : Space n →L[ℝ] Space n :=
  (axisLinear a).toContinuousLinearMap

@[simp] theorem axisCLM_apply {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    axisCLM a x = axisMap a x := rfl

@[simp] theorem axisMap_zero {n : ℕ} (a : Fin n → ℝ) : axisMap a 0 = 0 := by
  exact (axisLinear a).map_zero

@[simp] theorem axisMap_smul {n : ℕ} (a : Fin n → ℝ) (r : ℝ) (x : Space n) :
    axisMap a (r • x) = r • axisMap a x := (axisLinear a).map_smul r x

theorem axisMap_injective {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, a i ≠ 0) :
    Function.Injective (axisMap a) := by
  intro x y h
  ext i
  exact mul_left_cancel₀ (ha i) (congrArg (fun z : Space n => z i) h)

theorem axisMap_ne_zero {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, a i ≠ 0)
    {x : Space n} (hx : x ≠ 0) : axisMap a x ≠ 0 := by
  intro h
  apply hx
  apply axisMap_injective ha
  simpa using h

theorem axisMap_inner {n : ℕ} (a : Fin n → ℝ) (x y : Space n) :
    ⟪x, axisMap a y⟫_ℝ = ⟪axisMap a x, y⟫_ℝ := by
  simp only [PiLp.inner_apply, Real.inner_apply, axisMap, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def axisBody {n : ℕ} (a : Fin n → ℝ) : Set (Space n) :=
  axisMap a '' Metric.closedBall 0 1

def axisSupport {n : ℕ} (a : Fin n → ℝ) (x : Space n) : ℝ := ‖axisMap a x‖

def supportPoint {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n :=
  axisMap a ((axisSupport a x)⁻¹ • axisMap a x)

theorem axisSupport_pos {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {x : Space n} (hx : x ≠ 0) : 0 < axisSupport a x :=
  norm_pos_iff.mpr (axisMap_ne_zero (fun i => (ha i).ne') hx)

@[simp] theorem axisSupport_zero {n : ℕ} (a : Fin n → ℝ) : axisSupport a 0 = 0 := by
  simp [axisSupport]

@[simp] theorem supportPoint_zero {n : ℕ} (a : Fin n → ℝ) : supportPoint a 0 = 0 := by
  simp [supportPoint]

@[fun_prop] theorem continuous_axisSupport {n : ℕ} (a : Fin n → ℝ) :
    Continuous (axisSupport a) := (continuous_axisMap a).norm

theorem axisSupport_smul {n : ℕ} (a : Fin n → ℝ) (r : ℝ) (x : Space n) :
    axisSupport a (r • x) = |r| * axisSupport a x := by
  simp [axisSupport, norm_smul, Real.norm_eq_abs]

theorem supportPoint_mem_axisBody {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    supportPoint a x ∈ axisBody a := by
  refine ⟨(axisSupport a x)⁻¹ • axisMap a x, ?_, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg (axisMap a x)), axisSupport]
  by_cases h : ‖axisMap a x‖ = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem inner_le_axisSupport {n : ℕ} (a : Fin n → ℝ) (x : Space n)
    {y : Space n} (hy : y ∈ axisBody a) : ⟪x, y⟫_ℝ ≤ axisSupport a x := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [axisMap_inner]
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  exact (real_inner_le_norm _ _).trans (by
    simpa [axisSupport] using mul_le_mul_of_nonneg_left hz' (norm_nonneg (axisMap a x)))

theorem inner_supportPoint {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    ⟪x, supportPoint a x⟫_ℝ = axisSupport a x := by
  rw [supportPoint, axisMap_inner, inner_smul_right, real_inner_self_eq_norm_sq]
  dsimp [axisSupport]
  by_cases h : ‖axisMap a x‖ = 0
  · simp [h]
  · field_simp

theorem convex_axisBody {n : ℕ} (a : Fin n → ℝ) : Convex ℝ (axisBody a) :=
  (convex_closedBall (0 : Space n) 1).linear_image (axisLinear a)

theorem zero_mem_axisBody {n : ℕ} (a : Fin n → ℝ) : (0 : Space n) ∈ axisBody a := by
  exact ⟨0, by simp, axisMap_zero a⟩

def normalOffset {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) : Space n :=
  ‖x‖ • supportPoint a x + t • x

@[simp] theorem normalOffset_zero {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    normalOffset a t 0 = 0 := by simp [normalOffset]

theorem inner_normalOffset_self {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    ⟪x, normalOffset a t x⟫_ℝ =
      ‖x‖ * (axisSupport a x + t * ‖x‖) := by
  rw [normalOffset, inner_add_right, inner_smul_right, inner_smul_right,
    inner_supportPoint, real_inner_self_eq_norm_sq]
  ring

theorem inner_normalOffset_le {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (x y : Space n) :
    ⟪x, normalOffset a t y⟫_ℝ ≤ ‖y‖ * (axisSupport a x + t * ‖x‖) := by
  have hsup := inner_le_axisSupport a x (supportPoint_mem_axisBody a y)
  have hinner := real_inner_le_norm x y
  rw [normalOffset, inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hsup (norm_nonneg y),
    mul_le_mul_of_nonneg_left hinner ht]

theorem normalOffset_ne_zero {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) {x : Space n} (hx : x ≠ 0) : normalOffset a t x ≠ 0 := by
  intro h
  have hp : 0 < ‖x‖ * (axisSupport a x + t * ‖x‖) :=
    mul_pos (norm_pos_iff.mpr hx)
      (add_pos_of_pos_of_nonneg (axisSupport_pos ha hx) (mul_nonneg ht (norm_nonneg x)))
  rw [← inner_normalOffset_self, h, inner_zero_right] at hp
  exact lt_irrefl _ hp

theorem normalOffset_norm_eq_of_eq {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) {x y : Space n}
    (h : normalOffset a t x = normalOffset a t y) : ‖x‖ = ‖y‖ := by
  suffices hle : ∀ x y : Space n, normalOffset a t x = normalOffset a t y → ‖x‖ ≤ ‖y‖ from
    le_antisymm (hle x y h) (hle y x h.symm)
  intro x y hxy
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : 0 < axisSupport a x + t * ‖x‖ :=
      add_pos_of_pos_of_nonneg (axisSupport_pos ha hx) (mul_nonneg ht (norm_nonneg x))
    have hh := inner_normalOffset_le a ht x y
    rw [← hxy, inner_normalOffset_self] at hh
    exact le_of_mul_le_mul_right hh hpos

theorem normalOffset_injective {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) : Function.Injective (normalOffset a t) := by
  intro x y h
  have hnorm := normalOffset_norm_eq_of_eq ha ht h
  by_cases hx : x = 0
  · rw [hx]
    symm
    apply norm_eq_zero.mp
    simpa [hx] using hnorm.symm
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : y ≠ 0 := by
    intro hy
    exact hr.ne' (by simpa [hy] using hnorm)
  have hxS := axisSupport_pos ha hx
  have hyS := axisSupport_pos ha hy
  have hsup := inner_le_axisSupport a x (supportPoint_mem_axisBody a y)
  have hxy := real_inner_le_norm x y
  rw [← hnorm] at hxy
  have heq := congrArg (fun z : Space n => ⟪x, z⟫_ℝ) h
  rw [inner_normalOffset_self, normalOffset, inner_add_right, inner_smul_right,
    inner_smul_right, ← hnorm] at heq
  have hs : ⟪x, supportPoint a y⟫_ℝ = axisSupport a x := by
    have hn := mul_nonneg ht (sub_nonneg.mpr hxy)
    nlinarith
  have hcs : ⟪axisMap a x, axisMap a y⟫_ℝ = axisSupport a x * axisSupport a y := by
    rw [supportPoint, axisMap_inner, inner_smul_right] at hs
    field_simp [hyS.ne'] at hs
    nlinarith
  have hcol := (inner_eq_norm_mul_iff_real).1 hcs
  have hcol' : axisSupport a y • x = axisSupport a x • y := by
    apply axisMap_injective (fun i => (ha i).ne')
    simpa only [axisMap_smul, axisSupport] using hcol
  have hnormcol := congrArg norm hcol'
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hyS.le,
    Real.norm_of_nonneg hxS.le, ← hnorm] at hnormcol
  have hS : axisSupport a y = axisSupport a x := mul_right_cancel₀ hr.ne' hnormcol
  rw [hS] at hcol'
  ext i
  exact mul_left_cancel₀ hxS.ne' (congrArg (fun z : Space n => z i) hcol')

theorem normalOffset_mem_parallelBody {n : ℕ} (a : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t)
    {x : Space n} (hx : x ∈ Metric.closedBall 0 1) :
    normalOffset a t x ∈ parallelBody (axisBody a) t := by
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  have hfirst : ‖x‖ • supportPoint a x ∈ axisBody a :=
    (convex_axisBody a).smul_mem_of_zero_mem (zero_mem_axisBody a)
      (supportPoint_mem_axisBody a x) ⟨norm_nonneg x, hx'⟩
  have hsecond : t • x ∈ Metric.closedBall (0 : Space n) t := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht]
    exact mul_le_of_le_one_right ht hx'
  exact ⟨_, hfirst, _, hsecond, rfl⟩

end EllipsoidVerification
end
end CanonicalSource3

section CanonicalSource4
/- Source: Ellipsoid/NormalOffsetSurjectivity.lean -/



noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Pointwise Topology InnerProductSpace RealInnerProductSpace

namespace EllipsoidVerification

theorem hasFDerivAt_euclideanNorm {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (fun z : Space n => ‖z‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have h' : HasFDerivAt (fun z : Space n => ‖z‖)
      ((1 / (2 * ‖x‖)) • 2 • innerSL ℝ x) x := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using h
  apply h'.congr_fderiv
  ext y
  simp only [two_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hx] <;> ring

theorem hasFDerivAt_axisSupport {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (axisSupport a) (innerSL ℝ (supportPoint a x)) x := by
  have h := (hasFDerivAt_euclideanNorm (axisMap_ne_zero (fun i => (ha i).ne') hx)).comp x
    (axisCLM a).hasFDerivAt
  have h' : HasFDerivAt (axisSupport a)
      ((‖axisMap a x‖⁻¹ • innerSL ℝ (axisMap a x)).comp (axisCLM a)) x := h
  apply h'.congr_fderiv
  ext y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, axisCLM_apply, smul_eq_mul, supportPoint,
    ← axisMap_inner, real_inner_smul_left, axisSupport]

theorem supportPoint_smul_pos {n : ℕ} (a : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (x : Space n) : supportPoint a (r • x) = supportPoint a x := by
  simp only [supportPoint, axisSupport_smul, abs_of_pos hr, axisMap_smul, _root_.mul_inv_rev,
    smul_smul]
  congr 1
  congr 1
  field_simp [hr.ne']

theorem normalOffset_smul_nonneg {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    {r : ℝ} (hr : 0 ≤ r) (x : Space n) :
    normalOffset a t (r • x) = r • normalOffset a t x := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp
  · rw [normalOffset, norm_smul, Real.norm_of_nonneg hr.le,
      supportPoint_smul_pos a hr, normalOffset, smul_add, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring

theorem normalized_mem_unitSphere {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Space n) 1 := by
  simp [Metric.mem_sphere, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    norm_ne_zero_iff.mpr hx]

/-- The homogeneous normal-offset parametrization is onto the whole ambient
space. The proof maximizes the dual support ratio on the actual unit sphere
and applies Fermat's theorem; it does not presume a boundary parametrization. -/
theorem normalOffset_surjective {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) : Function.Surjective (normalOffset a t) := by
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  let g : Space n → ℝ := fun u => ⟪z, u⟫_ℝ / (axisSupport a u + t)
  have hu0 (u : Space n) (hu : u ∈ Metric.sphere (0 : Space n) 1) : u ≠ 0 := by
    intro h
    simpa [h] using hu
  have hden (u : Space n) (hu : u ∈ Metric.sphere (0 : Space n) 1) :
      0 < axisSupport a u + t := add_pos_of_pos_of_nonneg (axisSupport_pos ha (hu0 u hu)) ht
  have hg : ContinuousOn g (Metric.sphere (0 : Space n) 1) := by
    apply ((innerSL ℝ z).continuous.continuousOn).div
      ((continuous_axisSupport a).add continuous_const).continuousOn
    exact fun u hu => (hden u hu).ne'
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMaxOn
    ⟨‖z‖⁻¹ • z, normalized_mem_unitSphere hz⟩ hg
  have hun : ‖u‖ = 1 := by simpa using hu
  let c := g u
  have hc : 0 < c := by
    have hv := hmax (normalized_mem_unitSphere hz)
    have hip : 0 < ⟪z, ‖z‖⁻¹ • z⟫_ℝ := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      positivity
    exact (div_pos hip (hden _ (normalized_mem_unitSphere hz))).trans_le hv
  have hsupport (x : Space n) : ⟪z, x⟫_ℝ ≤ c * (axisSupport a x + t * ‖x‖) := by
    by_cases hx : x = 0
    · simp [hx]
    have hnx := norm_pos_iff.mpr hx
    have hm := (div_le_iff₀ (hden _ (normalized_mem_unitSphere hx))).mp
      (hmax (normalized_mem_unitSphere hx))
    have hmul := mul_le_mul_of_nonneg_left hm hnx.le
    simp only [inner_smul_right, axisSupport_smul,
      abs_of_pos (inv_pos.mpr hnx)] at hmul
    convert hmul using 1 <;> field_simp [hnx.ne'] <;> ring
  let f : Space n → ℝ := fun x => c * (axisSupport a x + t * ‖x‖) - ⟪z, x⟫_ℝ
  have hfu : f u = 0 := by
    dsimp [f, c, g]
    rw [hun, mul_one, div_mul_cancel₀ _ (hden u hu).ne', sub_self]
  have hmin : IsLocalMin f u := by
    apply (show IsMinOn f Set.univ u from fun x hx => ?_).isLocalMin (by simp)
    rw [hfu]
    exact sub_nonneg.mpr (hsupport x)
  have hderiv := (((hasFDerivAt_axisSupport ha (hu0 u hu)).add
    ((hasFDerivAt_euclideanNorm (hu0 u hu)).const_mul t)).const_mul c).sub
      (innerSL ℝ z).hasFDerivAt
  have hzero := hmin.hasFDerivAt_eq_zero hderiv
  have hgrad : c • (supportPoint a u + t • u) = z := by
    let w := c • (supportPoint a u + t • u) - z
    have hw := congrArg (fun L : Space n →L[ℝ] ℝ => L w) hzero
    have hnorm : ‖w‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      change ⟪c • (supportPoint a u + t • u) - z, w⟫_ℝ = 0
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
        innerSL_apply_apply, smul_eq_mul, hun, inv_one, one_mul,
        inner_sub_left, real_inner_smul_left, inner_add_left] using hw
    have hnorm0 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  refine ⟨c • u, ?_⟩
  rw [normalOffset_smul_nonneg a t hc.le, normalOffset, hun, one_smul]
  exact hgrad

/-- The image is the literal Minkowski parallel body, including radius zero. -/
theorem normalOffset_image_unitBall {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) :
    normalOffset a t '' Metric.closedBall (0 : Space n) 1 = parallelBody (axisBody a) t := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact normalOffset_mem_parallelBody a ht hx
  · intro z hz
    obtain ⟨x, rfl⟩ := normalOffset_surjective ha ht z
    refine ⟨x, ?_, rfl⟩
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨v, hv, w, hw, heq⟩ := hz
    have hh : ⟪x, normalOffset a t x⟫_ℝ ≤ axisSupport a x + t * ‖x‖ := by
      rw [← heq, inner_add_right]
      have hs := inner_le_axisSupport a x hv
      have hn : ‖w‖ ≤ t := by simpa using hw
      have hi := (real_inner_le_norm x w).trans
        (mul_le_mul_of_nonneg_left hn (norm_nonneg x))
      nlinarith
    rw [inner_normalOffset_self] at hh
    have hp := add_pos_of_pos_of_nonneg (axisSupport_pos ha hx)
      (mul_nonneg ht (norm_nonneg x))
    have hn : ‖x‖ ≤ 1 := le_of_mul_le_mul_right (by simpa using hh) hp
    simpa using hn

end EllipsoidVerification
end
end CanonicalSource4

section CanonicalSource5
/- Source: Ellipsoid/NormalOffsetCalculus.lean -/



noncomputable section

open Set Matrix
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace EllipsoidVerification

theorem axisMap_axisMap {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    axisMap a (axisMap a x) = axisMap (fun i => a i ^ 2) x := by
  ext i
  simp [axisMap]
  ring

theorem supportPoint_eq {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    supportPoint a x = (axisSupport a x)⁻¹ • axisMap (fun i => a i ^ 2) x := by
  rw [supportPoint, axisMap_smul, axisMap_axisMap]

theorem axisSupport_sq {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    axisSupport a x ^ 2 = ∑ i, a i ^ 2 * (x i) ^ 2 := by
  rw [axisSupport, ← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, Real.inner_apply, axisMap, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def supportDerivative {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n →L[ℝ] Space n :=
  (axisSupport a x)⁻¹ • axisCLM (fun i => a i ^ 2) -
    ((axisSupport a x)⁻¹ • innerSL ℝ (supportPoint a x)).smulRight (supportPoint a x)

theorem hasFDerivAt_supportPoint {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (supportPoint a) (supportDerivative a x) x := by
  have hp := axisSupport_pos ha hx
  have hi := (hasDerivAt_inv hp.ne').comp_hasFDerivAt x (hasFDerivAt_axisSupport ha hx)
  have hd := hi.smul (axisCLM (fun i => a i ^ 2)).hasFDerivAt
  convert hd using 1
  · funext z
    exact supportPoint_eq a z
  · ext y i
    simp only [supportDerivative, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, axisCLM_apply,
      supportPoint_eq, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply, smul_eq_mul,
      inner_smul_left, Function.comp_apply]
    field_simp [hp.ne'] <;> ring

def normalOffsetDerivative {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    Space n →L[ℝ] Space n :=
  ‖x‖ • supportDerivative a x +
    (‖x‖⁻¹ • innerSL ℝ x).smulRight (supportPoint a x) +
      t • ContinuousLinearMap.id ℝ (Space n)

theorem hasFDerivAt_normalOffset {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    (t : ℝ) {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (normalOffset a t) (normalOffsetDerivative a t x) x := by
  exact ((hasFDerivAt_euclideanNorm hx).smul (hasFDerivAt_supportPoint ha hx)).add
    ((hasFDerivAt_id x).const_smul t)

def normalOffsetMatrix {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => ‖x‖ / axisSupport a x * a i ^ 2 + t) +
    Matrix.vecMulVec (fun i => supportPoint a x i)
      (fun j => ‖x‖⁻¹ * x j - ‖x‖ / axisSupport a x * supportPoint a x j)

theorem normalOffsetDerivative_eq_matrix {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    normalOffsetDerivative a t x = (normalOffsetMatrix a t x).toEuclideanLin.toContinuousLinearMap := by
  ext y i
  simp only [normalOffsetDerivative, supportDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, axisCLM_apply, PiLp.smul_apply, PiLp.sub_apply,
    PiLp.add_apply, axisMap, PiLp.toLp_apply, smul_eq_mul,
    LinearMap.coe_toContinuousLinearMap',
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, normalOffsetMatrix,
    Matrix.add_mulVec, Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec,
    Pi.add_apply, Pi.smul_apply, op_smul_eq_smul, dotProduct, PiLp.inner_apply, Real.inner_apply,
    sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  ring_nf
  simp only [Finset.mul_sum]
  simp only [← mul_assoc]
  have hsum :
      (∑ j, ‖x‖ * (axisSupport a x)⁻¹ * supportPoint a x j * y j *
        supportPoint a x i) =
      ∑ j, ‖x‖ * (axisSupport a x)⁻¹ * supportPoint a x i *
        supportPoint a x j * y j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

theorem det_normalOffsetDerivative {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (x : Space n) :
    LinearMap.det (normalOffsetDerivative a t x).toLinearMap = (normalOffsetMatrix a t x).det := by
  rw [normalOffsetDerivative_eq_matrix]
  exact LinearMap.det_toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis _

theorem normalOffsetMatrix_smul_pos {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    normalOffsetMatrix a t (r • x) = normalOffsetMatrix a t x := by
  ext i j
  simp only [normalOffsetMatrix, norm_smul, Real.norm_of_nonneg hr.le,
    axisSupport_smul, abs_of_pos hr, supportPoint_smul_pos a hr,
    Matrix.add_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [mul_div_mul_left _ _ hr.ne', _root_.mul_inv_rev]
  split_ifs <;> field_simp [hr.ne'] <;> ring

end EllipsoidVerification
end
end CanonicalSource5

section CanonicalSource6
/- Source: Ellipsoid/NormalOffsetJacobian.lean -/



noncomputable section

open Matrix Polynomial Set
open scoped BigOperators RealInnerProductSpace

namespace EllipsoidVerification

theorem det_diagonal_add_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b v w : ι → ℝ) (hb : ∀ i, b i ≠ 0) :
    (Matrix.diagonal b + Matrix.vecMulVec v w).det =
      (∏ i, b i) * (1 + ∑ i, w i * (b i)⁻¹ * v i) := by
  have hfactor : Matrix.diagonal b + Matrix.vecMulVec v w =
      Matrix.diagonal b * (1 + Matrix.vecMulVec (fun i => (b i)⁻¹ * v i) w) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.vecMulVec_apply]
    split_ifs <;> field_simp [hb i] <;> ring
  rw [hfactor, Matrix.det_mul, Matrix.det_diagonal, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem det_diagonal_add_vecMulVec_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b v w : ι → ℝ) (hb : ∀ i, b i ≠ 0) :
    (Matrix.diagonal b + Matrix.vecMulVec v w).det =
      (∏ i, b i) + ∑ i, v i * w i * ∏ j ∈ Finset.univ.erase i, b j := by
  rw [det_diagonal_add_vecMulVec b v w hb, mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_prod_erase Finset.univ b (Finset.mem_univ i)]
  field_simp [hb i]

def normalOffsetJacobianPolynomial {n : ℕ} (a : Fin n → ℝ) (x : Space n) : ℝ[X] :=
  (∏ i, (X + C (‖x‖ / axisSupport a x * a i ^ 2))) +
    ∑ i, C (supportPoint a x i *
      (‖x‖⁻¹ * x i - ‖x‖ / axisSupport a x * supportPoint a x i)) *
      ∏ j ∈ Finset.univ.erase i, (X + C (‖x‖ / axisSupport a x * a j ^ 2))

theorem normalOffsetJacobianPolynomial_eval {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : x ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (normalOffsetJacobianPolynomial a x).eval t = (normalOffsetMatrix a t x).det := by
  rw [normalOffsetMatrix, det_diagonal_add_vecMulVec_expansion]
  · simp only [normalOffsetJacobianPolynomial, Polynomial.eval_add,
      Polynomial.eval_prod, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, add_comm]
  · intro i
    exact (add_pos_of_pos_of_nonneg
      (mul_pos (div_pos (norm_pos_iff.mpr hx) (axisSupport_pos ha hx)) (sq_pos_of_pos (ha i))) ht).ne'

theorem normalOffsetJacobianPolynomial_natDegree {n : ℕ} (a : Fin n → ℝ) (x : Space n) :
    (normalOffsetJacobianPolynomial a x).natDegree ≤ n := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_prod_le _ _).trans
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    exact le_rfl
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_prod_le _ _).trans
    simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by simp)

theorem normalOffsetMatrix_det_pos_unit {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    0 < (normalOffsetMatrix a t x).det := by
  have hx0 : x ≠ 0 := by intro h; simpa [h] using hx
  let h := axisSupport a x
  have hh : 0 < h := axisSupport_pos ha hx0
  let b : Fin n → ℝ := fun i => a i ^ 2 / h + t
  have hb (i : Fin n) : 0 < b i := add_pos_of_pos_of_nonneg
    (div_pos (sq_pos_of_pos (ha i)) hh) ht
  have hv (i : Fin n) : supportPoint a x i = a i ^ 2 * x i / h := by
    simp only [supportPoint_eq, PiLp.smul_apply, axisMap, PiLp.toLp_apply, smul_eq_mul]
    dsimp [h]
    ring
  have hsum : ∑ i, a i ^ 2 * (x i) ^ 2 / h ^ 2 = 1 := by
    rw [← Finset.sum_div, ← axisSupport_sq]
    exact div_self (pow_ne_zero 2 hh.ne')
  have hbracket :
      1 + ∑ i, (x i - h⁻¹ * supportPoint a x i) * (b i)⁻¹ * supportPoint a x i =
        ((h + t) / h) * ∑ i, (a i ^ 2 / h / b i) * (x i) ^ 2 := by
    have heach (i : Fin n) :
        (x i - h⁻¹ * supportPoint a x i) * (b i)⁻¹ * supportPoint a x i =
          ((h + t) / h) * ((a i ^ 2 / h / b i) * (x i) ^ 2) -
            a i ^ 2 * (x i) ^ 2 / h ^ 2 := by
      rw [hv]
      have hden : a i ^ 2 + h * t ≠ 0 :=
        (add_pos_of_pos_of_nonneg (sq_pos_of_pos (ha i)) (mul_nonneg hh.le ht)).ne'
      dsimp [b]
      field_simp [hh.ne', hden] <;> ring
    simp_rw [heach]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx0
    ext i
    exact not_not.mp (not_exists.mp h i)
  have hS : 0 < ∑ i, (a i ^ 2 / h / b i) * (x i) ^ 2 := by
    apply Finset.sum_pos'
    · intro i hi
      positivity
    · exact ⟨i, Finset.mem_univ i, mul_pos
        (div_pos (div_pos (sq_pos_of_pos (ha i)) hh) (hb i)) (sq_pos_of_ne_zero hi)⟩
  rw [normalOffsetMatrix, det_diagonal_add_vecMulVec]
  · have hpos : 0 < (∏ i, b i) *
        (1 + ∑ i, (x i - h⁻¹ * supportPoint a x i) * (b i)⁻¹ * supportPoint a x i) := by
      rw [hbracket]
      exact mul_pos (Finset.prod_pos fun i _ => hb i)
        (mul_pos (div_pos (add_pos_of_pos_of_nonneg hh ht) hh) hS)
    simpa only [hx, one_div, inv_one, one_mul, mul_one, b, h, div_eq_mul_inv,
      mul_comm] using hpos
  · intro i
    simpa [hx, b, h, div_eq_mul_inv, mul_comm] using (hb i).ne'

theorem normalOffsetMatrix_det_pos {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : x ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < (normalOffsetMatrix a t x).det := by
  have hunit := normalized_mem_unitSphere hx
  have h := normalOffsetMatrix_det_pos_unit ha (by simpa using hunit) ht
  simpa only [normalOffsetMatrix_smul_pos a t (inv_pos.mpr (norm_pos_iff.mpr hx))] using h

theorem normalOffsetJacobianPolynomial_smul_pos {n : ℕ} (a : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) (x : Space n) :
    normalOffsetJacobianPolynomial a (r • x) = normalOffsetJacobianPolynomial a x := by
  simp only [normalOffsetJacobianPolynomial, norm_smul, Real.norm_of_nonneg hr.le,
    axisSupport_smul, abs_of_pos hr, supportPoint_smul_pos a hr,
    PiLp.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hr.ne', _root_.mul_inv_rev]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  field_simp [hr.ne']

end EllipsoidVerification
end
end CanonicalSource6

section CanonicalSource7
/- Source: Ellipsoid/SteinerVolume.lean -/



noncomputable section

open MeasureTheory Polynomial Set Filter
open scoped BigOperators Pointwise Topology RealInnerProductSpace

namespace EllipsoidVerification

theorem continuousAt_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {x : Space n} (hx : x ≠ 0) (k : ℕ) :
    ContinuousAt (fun z => (normalOffsetJacobianPolynomial a z).coeff k) x := by
  have hs := (hasFDerivAt_axisSupport ha hx).continuousAt
  have hv := (hasFDerivAt_supportPoint ha hx).continuousAt
  have hr := continuous_norm.continuousAt.div hs (axisSupport_pos ha hx).ne'
  have hInv := continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)
  have hc (i : Fin n) : ContinuousAt (fun z : Space n => ‖z‖ / axisSupport a z * a i ^ 2) x :=
    hr.mul continuousAt_const
  have hp (s : Finset (Fin n)) (j : ℕ) : ContinuousAt
      (fun z : Space n => (∏ i ∈ s, (X + C (‖z‖ / axisSupport a z * a i ^ 2))).coeff j) x := by
    apply Polynomial.continuousAt_coeff_prod
    intro i hi l hl
    simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> fun_prop
  simp only [normalOffsetJacobianPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul]
  apply (hp Finset.univ k).add
  apply tendsto_finsetSum
  intro i hi
  apply ContinuousAt.mul
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.comp hv).mul
      ((hInv.mul (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt).sub
        (hr.mul ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).continuousAt.comp hv)))
  · exact hp _ _

theorem measurable_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (k : ℕ) :
    Measurable (fun z : Space n => (normalOffsetJacobianPolynomial a z).coeff k) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (continuousAt_normalOffsetJacobianPolynomial_coeff ha hx k).continuousWithinAt

theorem bounded_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (k : ℕ) :
    ∃ C : ℝ, ∀ x : Space n, ‖(normalOffsetJacobianPolynomial a x).coeff k‖ ≤ C := by
  have hc : ContinuousOn (fun x : Space n => (normalOffsetJacobianPolynomial a x).coeff k)
      (Metric.sphere 0 1) := by
    intro x hx
    apply (continuousAt_normalOffsetJacobianPolynomial_coeff ha _ k).continuousWithinAt
    intro h
    simpa [h] using hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Space n) 1).exists_bound_of_continuousOn hc
  refine ⟨max C ‖(normalOffsetJacobianPolynomial a 0).coeff k‖, fun x => ?_⟩
  by_cases hx : x = 0
  · simpa [hx] using le_max_right C ‖(normalOffsetJacobianPolynomial a 0).coeff k‖
  · have hb := hC _ (normalized_mem_unitSphere hx)
    rw [normalOffsetJacobianPolynomial_smul_pos a (inv_pos.mpr (norm_pos_iff.mpr hx))] at hb
    exact hb.trans (le_max_left _ _)

theorem integrableOn_normalOffsetJacobianPolynomial_coeff {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (k : ℕ) :
    IntegrableOn (fun z : Space n => (normalOffsetJacobianPolynomial a z).coeff k)
      (Metric.closedBall 0 1) := by
  obtain ⟨C, hC⟩ := bounded_normalOffsetJacobianPolynomial_coeff ha k
  exact Measure.integrableOn_of_bounded
    (isCompact_closedBall (0 : Space n) 1).measure_lt_top.ne
    (measurable_normalOffsetJacobianPolynomial_coeff ha k).aestronglyMeasurable
    (ae_of_all _ hC)

def normalOffsetVolumePolynomial {n : ℕ} (a : Fin n → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (∫ x in Metric.closedBall (0 : Space n) 1,
    (normalOffsetJacobianPolynomial a x).coeff k.val) * X ^ k.val

theorem normalOffsetVolumePolynomial_natDegree {n : ℕ} (a : Fin n → ℝ) :
    (normalOffsetVolumePolynomial a).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa using Nat.le_of_lt_succ k.isLt)

theorem normalOffsetVolumePolynomial_eval {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) (t : ℝ) :
    (normalOffsetVolumePolynomial a).eval t =
      ∫ x in Metric.closedBall (0 : Space n) 1, (normalOffsetJacobianPolynomial a x).eval t := by
  simp only [normalOffsetVolumePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  simp only [← integral_mul_const]
  rw [← integral_finsetSum _ (fun k _ =>
    (integrableOn_normalOffsetJacobianPolynomial_coeff ha k.val).mul_const (t ^ k.val))]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro x hx
  calc
    (∑ k : Fin (n + 1), (normalOffsetJacobianPolynomial a x).coeff k.val * t ^ k.val) =
        ∑ k ∈ Finset.range (n + 1), (normalOffsetJacobianPolynomial a x).coeff k * t ^ k :=
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (normalOffsetJacobianPolynomial a x).coeff k * t ^ k) (n + 1)
    _ = (normalOffsetJacobianPolynomial a x).eval t :=
      (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le
        (normalOffsetJacobianPolynomial_natDegree a x)) t).symm

theorem normalOffset_image_punctured_unitBall {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 ≤ t) :
    normalOffset a t '' (Metric.closedBall (0 : Space n) 1 \ {0}) =
      parallelBody (axisBody a) t \ {0} := by
  rw [← normalOffset_image_unitBall ha ht]
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simpa only [Set.mem_singleton_iff] using normalOffset_ne_zero ha ht hx0
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hx0
    apply hne
    simpa only [Set.mem_singleton_iff, normalOffset_zero] using congrArg (normalOffset a t) hx0

/-- An ellipsoid-specific Steiner formula derived from the actual geometric
normal map and the finite-dimensional change-of-variables theorem. -/
theorem parallelVolume_axisBody_eq_polynomial {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) {t : ℝ} (ht : 0 ≤ t) :
    parallelVolume (axisBody a) t = (normalOffsetVolumePolynomial a).eval t := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hrestrict (s : Set (Space n)) : volume.restrict (s \ {0}) = volume.restrict s := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    simp [hx]
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    (s := Metric.closedBall (0 : Space n) 1 \ {0})
    (measurableSet_closedBall.diff (measurableSet_singleton 0))
    (fun x hx => (hasFDerivAt_normalOffset ha t hx.2).hasFDerivWithinAt)
    (normalOffset_injective ha ht).injOn (fun _ : Space n => (1 : ℝ))
  rw [normalOffset_image_punctured_unitBall ha ht] at hcv
  simp only [MeasureTheory.IntegrableOn, hrestrict, smul_eq_mul, mul_one] at hcv
  have hl : (∫ _ in parallelBody (axisBody a) t, (1 : ℝ)) = parallelVolume (axisBody a) t := by
    simp [integral_const, parallelVolume, Measure.real]
  rw [hl] at hcv
  rw [normalOffsetVolumePolynomial_eval ha]
  refine hcv.trans (integral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Space n))] with x hx
  change |LinearMap.det (normalOffsetDerivative a t x).toLinearMap| =
    (normalOffsetJacobianPolynomial a x).eval t
  rw [det_normalOffsetDerivative, abs_of_pos (normalOffsetMatrix_det_pos ha hx ht),
    normalOffsetJacobianPolynomial_eval ha hx ht]

theorem steinerInterpolant_axisBody {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    steinerInterpolant (axisBody a) = normalOffsetVolumePolynomial a := by
  symm
  unfold steinerInterpolant
  apply Lagrange.eq_interpolate_of_eval_eq
    (v := fun i : Fin (n + 1) => (i.val : ℝ))
    (fun i : Fin (n + 1) => parallelVolume (axisBody a) i.val)
  · intro i hi j hj hij
    exact Fin.ext (Nat.cast_injective hij)
  · apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (Nat.lt_succ_of_le (normalOffsetVolumePolynomial_natDegree a))
  · intro i hi
    exact (parallelVolume_axisBody_eq_polynomial hn ha (Nat.cast_nonneg i.val)).symm

theorem axisBody_hasSteinerFormula {n : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) : HasSteinerFormula (axisBody a) := by
  intro t ht
  rw [steinerInterpolant_axisBody hn ha]
  exact parallelVolume_axisBody_eq_polynomial hn ha ht

theorem intrinsicVolume_axisBody_eq_jacobianIntegral {n k : ℕ} (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hk : k ≤ n) :
    intrinsicVolume (axisBody a) k =
      (∫ x in Metric.closedBall (0 : Space n) 1,
        (normalOffsetJacobianPolynomial a x).coeff (n - k)) / unitBallVolume (n - k) := by
  rw [intrinsicVolume, if_pos hk, steinerInterpolant_axisBody hn ha]
  congr 1
  simp only [normalOffsetVolumePolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (⟨n - k, by omega⟩ : Fin (n + 1))]
  · simp
  · intro j hj hne
    have hval : n - k ≠ j.val := fun h => hne (Fin.ext h.symm)
    simp [hval]
  · simp

end EllipsoidVerification
end
end CanonicalSource7

section CanonicalSource8
/- Source: Ellipsoid/HomogeneousIntegration.lean -/



noncomputable section

open MeasureTheory Set Metric Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def PositivelyHomogeneous {n : ℕ} (f : Space n → ℝ) (γ : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = r ^ γ * f x

theorem integrable_sphere_of_continuousOn_compl_zero {n : ℕ} {f : Space n → ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) :
    Integrable (fun u : sphere (0 : Space n) 1 => f u) volume.toSphere := by
  have hc : Continuous (fun u : sphere (0 : Space n) 1 => f u) := by
    apply hf.comp_continuous continuous_subtype_val
    intro u
    intro hu
    have hn := u.property
    simpa [show (u : Space n) = 0 from hu] using hn
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem homogeneous_bound {n : ℕ} {f : Space n → ℝ} {γ : ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) (hh : PositivelyHomogeneous f γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, x ≠ 0 → ‖f x‖ ≤ C * ‖x‖ ^ γ := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Space n) 1).exists_bound_of_continuousOn
    (hf.mono (by intro x hx hx0; simpa [show x = 0 from hx0] using hx))
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have hxpos := norm_pos_iff.mpr hx
  have heq : f x = ‖x‖ ^ γ * f (‖x‖⁻¹ • x) := by
    simpa only [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul] using
      hh ‖x‖ hxpos (‖x‖⁻¹ • x)
  rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos γ)]
  exact (mul_le_mul_of_nonneg_left
    ((hB _ (normalized_mem_unitSphere hx)).trans (le_max_left B 0))
    (Real.rpow_nonneg hxpos.le γ)).trans_eq (mul_comm _ _)

theorem integrable_norm_rpow_gaussian {n : ℕ} (hn : 0 < n) {γ : ℝ} (hγ : -(n : ℝ) < γ) :
    Integrable (fun x : Space n => ‖x‖ ^ γ * Real.exp (-‖x‖ ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply (integrable_fun_norm_addHaar (volume : Measure (Space n))
    (f := fun r : ℝ => r ^ γ * Real.exp (-r ^ 2))).mpr
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) (by norm_num)
    (s := (n : ℝ) + γ - 1) (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, neg_mul, one_mul]
  have hpow : r ^ ((n : ℝ) + γ - 1) = r ^ (n - 1) * r ^ γ := by
    rw [← Real.rpow_natCast r (n - 1), ← Real.rpow_add hr]
    congr 1
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  rw [hpow]
  ring

theorem integrable_homogeneous_gaussian {n : ℕ} (hn : 0 < n) {f : Space n → ℝ} {γ : ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) (hh : PositivelyHomogeneous f γ)
    (hγ : -(n : ℝ) < γ) : Integrable (fun x => f x * Real.exp (-‖x‖ ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨C, hC, hb⟩ := homogeneous_bound hf hh
  apply ((integrable_norm_rpow_gaussian hn hγ).const_mul C).mono'
  · exact ((measurable_of_continuousOn_compl_singleton 0 hf).mul
      (measurable_norm.pow_const 2 |>.neg.exp)).aestronglyMeasurable
  · filter_upwards [volume.ae_ne (0 : Space n)] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right (hb x hx) (Real.exp_pos _).le).trans_eq (by ring)

/-- Polar coordinates for a homogeneous integrand times a Gaussian weight,
with the exact radial Gamma factor and the full locally integrable range. -/
theorem integral_homogeneous_gaussian {n : ℕ} (hn : 0 < n) {f : Space n → ℝ} {γ : ℝ}
    (hf : ContinuousOn f ({0}ᶜ : Set (Space n))) (hh : PositivelyHomogeneous f γ)
    (hγ : -(n : ℝ) < γ) :
    (∫ x : Space n, f x * Real.exp (-‖x‖ ^ 2)) =
      (1 / 2 : ℝ) * Real.Gamma (((n : ℝ) + γ) / 2) *
        ∫ u : sphere (0 : Space n) 1, f u ∂volume.toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [TauCeti.integral_eq_integral_toSphere_integral_Ioi _
    (integrable_homogeneous_gaussian hn hf hh hγ)]
  have hr (u : sphere (0 : Space n) 1) :
      (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (Space n) - 1) •
        (f (r • (u : Space n)) * Real.exp (-‖r • (u : Space n)‖ ^ 2))) =
      ((1 / 2 : ℝ) * Real.Gamma (((n : ℝ) + γ) / 2)) * f u := by
    have heq : (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (Space n) - 1) •
        (f (r • (u : Space n)) * Real.exp (-‖r • (u : Space n)‖ ^ 2))) =
        ∫ r in Ioi (0 : ℝ), (r ^ ((n : ℝ) + γ - 1) * Real.exp (-r ^ (2 : ℝ))) * f u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [hh r hr, norm_smul, Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere u, mul_one]
      simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
      rw [← Real.rpow_natCast r (n - 1), Nat.cast_sub hn, Nat.cast_one, Real.rpow_two]
      have hp : r ^ ((n : ℝ) - 1) * r ^ γ = r ^ ((n : ℝ) + γ - 1) := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      calc
        _ = (r ^ ((n : ℝ) - 1) * r ^ γ) *
            (f (u : Space n) * Real.exp (-r ^ 2)) := by ring
        _ = _ := by rw [hp]; ring
    rw [heq, integral_mul_const, integral_rpow_mul_exp_neg_rpow (by norm_num) (by linarith)]
    congr 3
    ring
  simp_rw [hr]
  exact integral_const_mul _ _

theorem closedBall_ae_eq_ball_one {n : ℕ} :
    Metric.closedBall (0 : Space n) 1 =ᵐ[volume] Metric.ball 0 1 := by
  have hs := MeasureTheory.Measure.addHaar_sphere_of_ne_zero (volume : Measure (Space n))
    (0 : Space n) (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hs] with x hx
  have hx' : ‖x‖ ≠ 1 := by simpa only [Metric.mem_sphere, dist_zero_right, Set.mem_compl_iff] using hx
  simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right]
  exact propext (le_iff_lt_or_eq.trans (or_iff_left hx'))

theorem integral_homogeneous_zero_unitBall {n : ℕ} (hn : 0 < n) {f : Space n → ℝ}
    (hf : IntegrableOn f (Metric.closedBall 0 1)) (hh : PositivelyHomogeneous f 0) :
    (∫ x in Metric.closedBall (0 : Space n) 1, f x) =
      (n : ℝ)⁻¹ * ∫ u : sphere (0 : Space n) 1, f u ∂volume.toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [setIntegral_congr_set closedBall_ae_eq_ball_one,
    TauCeti.setIntegral_ball_zero_eq_integral_Ioo (hf.mono_set ball_subset_closedBall)]
  have heq : (∫ r in Ioo (0 : ℝ) 1, r ^ (Module.finrank ℝ (Space n) - 1) •
      ∫ u : sphere (0 : Space n) 1, f (r • (u : Space n)) ∂volume.toSphere) =
      (∫ r in Ioo (0 : ℝ) 1, r ^ (n - 1)) *
        ∫ u : sphere (0 : Space n) 1, f u ∂volume.toSphere := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
      hh r hr.1, Real.rpow_zero, one_mul]
  rw [heq]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  simp [Nat.sub_add_cancel hn, hcast, hn.ne']

end EllipsoidVerification
end
end CanonicalSource8

section CanonicalSource9
/- Source: Ellipsoid/GaussianIntegrals.lean -/



noncomputable section

open MeasureTheory Set Real
open scoped BigOperators

namespace EllipsoidVerification

theorem integral_gaussian_rpow {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2)) = Real.sqrt Real.pi * b ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  simp_rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hb.le]
  ring

theorem integral_sq_gaussian_rpow {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2)) =
      Real.sqrt Real.pi / 2 * b ^ (-(3 / 2 : ℝ)) := by
  let f : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-b * x ^ 2)
  have hi : Integrable f := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : -1 < (2 : ℝ))
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    rw [show (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f (-x) by
      simpa using (integral_comp_neg_Ioi 0 f).symm]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [f]
  have hhalf : (∫ x in Ioi (0 : ℝ), f x) =
      b ^ (-(3 / 2 : ℝ)) * (1 / 2 : ℝ) * Real.Gamma (3 / 2) := by
    convert integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2)
      (by norm_num) (by norm_num) hb using 1 <;> norm_num [f, Real.rpow_two]
  have hGamma : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_nat_add_one_add_half 0 using 1 <;> norm_num
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hi, compl_Ioi, hneg, hhalf, hGamma]
  ring

theorem gaussian_second_factor {b : ℝ} (hb : 0 < b) :
    Real.sqrt Real.pi / 2 * b ^ (-(3 / 2 : ℝ)) =
      ((2 * b)⁻¹) * (Real.sqrt Real.pi * b ^ (-(1 / 2 : ℝ))) := by
  have hp : b ^ (-(3 / 2 : ℝ)) = b⁻¹ * b ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
    congr 1
    ring
  rw [hp]
  field_simp

theorem integral_diagonal_gaussian_coordinate_sq {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ j, 0 < b j) (i : Fin n) :
    (∫ x : Space n, (x i) ^ 2 * Real.exp (-(∑ j, b j * (x j) ^ 2))) =
      ((Real.sqrt Real.pi) ^ n / 2) * (b i)⁻¹ * ∏ j, (b j) ^ (-(1 / 2 : ℝ)) := by
  let f : (j : Fin n) → ℝ → ℝ := fun j x =>
    (if j = i then x ^ 2 else 1) * Real.exp (-b j * x ^ 2)
  have hpoint (x : Fin n → ℝ) :
      (x i) ^ 2 * Real.exp (-(∑ j, b j * (x j) ^ 2)) = ∏ j, f j (x j) := by
    simp only [f, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [Function.comp_def, PiLp.toLp_apply, hpoint,
    integral_fintype_prod_volume_eq_prod]
  have hf (j : Fin n) : (∫ x, f j x) =
      (if j = i then (2 * b i)⁻¹ else 1) *
        (Real.sqrt Real.pi * (b j) ^ (-(1 / 2 : ℝ))) := by
    by_cases hji : j = i
    · subst j
      simp only [f, if_true]
      rw [integral_sq_gaussian_rpow (hb i), gaussian_second_factor (hb i)]
    · simp only [f, hji, if_false, one_mul]
      exact integral_gaussian_rpow (hb j)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp

theorem finite_product_rpow {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (s : ℝ) :
    (∏ i, b i) ^ s = ∏ i, (b i) ^ s := by
  classical
  have h (S : Finset ι) : (∏ i ∈ S, b i) ^ s = ∏ i ∈ S, (b i) ^ s := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi,
          Real.mul_rpow (hb i) (Finset.prod_nonneg fun j hj => hb j), ih]
  exact h Finset.univ

end EllipsoidVerification
end
end CanonicalSource9
