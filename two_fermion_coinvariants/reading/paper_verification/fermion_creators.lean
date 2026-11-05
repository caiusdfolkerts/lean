module

public import PaperVerification.FermionExterior
public import PaperVerification.FermionSupport
public import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.Tactic.Abel

/-!
# Actual creation operators preserve the moment harmonics

All coefficients lie in a commutative ring. The exterior operations are the
literal creations and contractions, and the ordinary relations are literal
weighted moments in the coefficient ring. Polynomial indexing makes the
commutators apply to the suffix Newton polynomials as well as to powers.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Exterior

open scoped BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)

local notation "E" => ExteriorAlgebra R V

/-- The commutator of a paired contraction with arbitrary exterior creation. -/
theorem pairLower_creation (i : Fin n) (v : V) :
    pairLower b i * creation v = creation v * pairLower b i +
      (b.coord (.inl i) v) • annihilation (b.coord (.inr i)) -
      (b.coord (.inr i) v) • annihilation (b.coord (.inl i)) := by
  have hθ : annihilation (b.coord (.inl i)) * creation v =
      (b.coord (.inl i) v) • 1 - creation v * annihilation (b.coord (.inl i)) :=
    eq_sub_of_add_eq (annihilation_creation _ _)
  have hξ : annihilation (b.coord (.inr i)) * creation v =
      (b.coord (.inr i) v) • 1 - creation v * annihilation (b.coord (.inr i)) :=
    eq_sub_of_add_eq (annihilation_creation _ _)
  unfold pairLower
  rw [mul_assoc, hθ, mul_sub, mul_smul_comm, mul_one,
    ← mul_assoc, hξ, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
  abel

variable (φ β a c : Fin n → R)

/-- Polynomial-indexed theta contraction. -/
def thetaFunctional (p : Polynomial R) : Module.Dual R V :=
  ∑ i, (c i * p.eval (φ i)) • b.coord (.inl i)

/-- Polynomial-indexed xi contraction. -/
def xiFunctional (p : Polynomial R) : Module.Dual R V :=
  ∑ i, (β i * a i * p.eval (φ i)) • b.coord (.inr i)

def thetaCurrent (p : Polynomial R) : Module.End R E :=
  annihilation (thetaFunctional b φ c p)

def xiCurrent (p : Polynomial R) : Module.End R E :=
  annihilation (xiFunctional b φ β a p)

def mixedCurrent (p : Polynomial R) : Module.End R E :=
  ∑ i, p.eval (φ i) • pairLower b i

/-- The vectors whose wedge products are the two creation operators. -/
def thetaCreatorVector (p : Polynomial R) : V :=
  ∑ i, (β i * a i * p.eval (φ i)) • b (.inl i)

def xiCreatorVector (p : Polynomial R) : V :=
  ∑ i, (c i * p.eval (φ i)) • b (.inr i)

def thetaCreator (p : Polynomial R) : Module.End R E :=
  creation (thetaCreatorVector b φ β a p)

def xiCreator (p : Polynomial R) : Module.End R E :=
  creation (xiCreatorVector b φ c p)

@[simp]
theorem coord_thetaCreatorVector_left (p : Polynomial R) (i : Fin n) :
    b.coord (.inl i) (thetaCreatorVector b φ β a p) = β i * a i * p.eval (φ i) := by
  simp [thetaCreatorVector, Module.Basis.coord_apply, Finsupp.single_apply]

@[simp]
theorem coord_thetaCreatorVector_right (p : Polynomial R) (i : Fin n) :
    b.coord (.inr i) (thetaCreatorVector b φ β a p) = 0 := by
  simp [thetaCreatorVector, Module.Basis.coord_apply, Finsupp.single_apply]

@[simp]
theorem coord_xiCreatorVector_left (p : Polynomial R) (i : Fin n) :
    b.coord (.inl i) (xiCreatorVector b φ c p) = 0 := by
  simp [xiCreatorVector, Module.Basis.coord_apply, Finsupp.single_apply]

@[simp]
theorem coord_xiCreatorVector_right (p : Polynomial R) (i : Fin n) :
    b.coord (.inr i) (xiCreatorVector b φ c p) = c i * p.eval (φ i) := by
  simp [xiCreatorVector, Module.Basis.coord_apply, Finsupp.single_apply]

theorem thetaCurrent_eq_sum (p : Polynomial R) :
    thetaCurrent b φ c p =
      ∑ i, (c i * p.eval (φ i)) • annihilation (b.coord (.inl i)) := by
  simp only [thetaCurrent, thetaFunctional, annihilation, map_sum, map_smul]

theorem xiCurrent_eq_sum (p : Polynomial R) :
    xiCurrent b φ β a p =
      ∑ i, (β i * a i * p.eval (φ i)) • annihilation (b.coord (.inr i)) := by
  simp only [xiCurrent, xiFunctional, annihilation, map_sum, map_smul]

def ordinaryPolynomialMoment (p : Polynomial R) : R :=
  ∑ i, β i * a i * c i * p.eval (φ i)

theorem thetaCurrent_thetaCreator (p q : Polynomial R) :
    thetaCurrent b φ c q * thetaCreator b φ β a p +
      thetaCreator b φ β a p * thetaCurrent b φ c q =
        ordinaryPolynomialMoment φ β a c (q * p) • 1 := by
  rw [thetaCurrent, thetaCreator, annihilation_creation]
  congr 1
  simp only [thetaFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    coord_thetaCreatorVector_left, ordinaryPolynomialMoment, Polynomial.eval_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem xiCurrent_xiCreator (p q : Polynomial R) :
    xiCurrent b φ β a q * xiCreator b φ c p +
      xiCreator b φ c p * xiCurrent b φ β a q =
        ordinaryPolynomialMoment φ β a c (q * p) • 1 := by
  rw [xiCurrent, xiCreator, annihilation_creation]
  congr 1
  simp only [xiFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    coord_xiCreatorVector_right, ordinaryPolynomialMoment, Polynomial.eval_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem thetaCurrent_xiCreator (p q : Polynomial R) :
    thetaCurrent b φ c q * xiCreator b φ c p +
      xiCreator b φ c p * thetaCurrent b φ c q = 0 := by
  rw [thetaCurrent, xiCreator, annihilation_creation]
  simp only [thetaFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    coord_xiCreatorVector_left, smul_zero, Finset.sum_const_zero, zero_smul]

theorem xiCurrent_thetaCreator (p q : Polynomial R) :
    xiCurrent b φ β a q * thetaCreator b φ β a p +
      thetaCreator b φ β a p * xiCurrent b φ β a q = 0 := by
  rw [xiCurrent, thetaCreator, annihilation_creation]
  simp only [xiFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    coord_thetaCreatorVector_right, smul_zero, Finset.sum_const_zero, zero_smul]

theorem mixedCurrent_thetaCreator (p q : Polynomial R) :
    mixedCurrent b φ q * thetaCreator b φ β a p =
      thetaCreator b φ β a p * mixedCurrent b φ q + xiCurrent b φ β a (q * p) := by
  rw [mixedCurrent, Finset.sum_mul]
  simp_rw [thetaCreator, smul_mul_assoc,
    pairLower_creation, coord_thetaCreatorVector_left, coord_thetaCreatorVector_right,
    zero_smul, sub_zero, smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp only [mixedCurrent, Finset.mul_sum, mul_smul_comm]
  · rw [xiCurrent_eq_sum]
    simp only [Polynomial.eval_mul, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring

theorem mixedCurrent_xiCreator (p q : Polynomial R) :
    mixedCurrent b φ q * xiCreator b φ c p =
      xiCreator b φ c p * mixedCurrent b φ q - thetaCurrent b φ c (q * p) := by
  rw [mixedCurrent, Finset.sum_mul]
  simp_rw [xiCreator, smul_mul_assoc,
    pairLower_creation, coord_xiCreatorVector_left, coord_xiCreatorVector_right,
    zero_smul, add_zero, smul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [mixedCurrent, Finset.mul_sum, mul_smul_comm]
  · rw [thetaCurrent_eq_sum]
    simp only [Polynomial.eval_mul, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring

/-- The simultaneous kernel of the literal odd and mixed contractions. -/
def IsHarmonic (w : E) : Prop :=
  (∀ p : Polynomial R, thetaCurrent b φ c p w = 0) ∧
  (∀ p : Polynomial R, xiCurrent b φ β a p w = 0) ∧
  ∀ p : Polynomial R, mixedCurrent b φ p w = 0

/-- Polynomial moments vanish whenever all ordinary power moments vanish. -/
theorem ordinaryPolynomialMoment_zero
    (h : ∀ k, moment φ (fun i ↦ β i * a i * c i) k = 0) (p : Polynomial R) :
    ordinaryPolynomialMoment φ β a c p = 0 := by
  simpa only [ordinaryPolynomialMoment, smul_eq_mul, mul_comm] using
    polynomial_moment_zero φ (fun i ↦ β i * a i * c i) h p

/-- A creator preserves harmonics whenever its ordinary anticommutators vanish. -/
theorem thetaCreator_preserves_harmonics_of_moments
    (p : Polynomial R) (h : ∀ q, ordinaryPolynomialMoment φ β a c (q * p) = 0) (w : E) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (thetaCreator b φ β a p w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    have heq := congrArg (fun T : Module.End R E ↦ T w)
      (thetaCurrent_thetaCreator b φ β a c p q)
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, hw.1 q, map_zero, add_zero,
      h q, zero_smul, LinearMap.zero_apply] using heq
  · intro q
    have heq := congrArg (fun T : Module.End R E ↦ T w)
      (xiCurrent_thetaCreator b φ β a p q)
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply,
      hw.2.1 q, map_zero, add_zero] using heq
  · intro q
    have heq := congrArg (fun T : Module.End R E ↦ T w)
      (mixedCurrent_thetaCreator b φ β a p q)
    simpa only [Module.End.mul_apply, LinearMap.add_apply,
      hw.2.2 q, map_zero, hw.2.1 (q * p), add_zero] using heq

/-- The xi analogue with only the necessary polynomial moments assumed. -/
theorem xiCreator_preserves_harmonics_of_moments
    (p : Polynomial R) (h : ∀ q, ordinaryPolynomialMoment φ β a c (q * p) = 0) (w : E) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (xiCreator b φ c p w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    have heq := congrArg (fun T : Module.End R E ↦ T w)
      (thetaCurrent_xiCreator b φ c p q)
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.zero_apply,
      hw.1 q, map_zero, add_zero] using heq
  · intro q
    have heq := congrArg (fun T : Module.End R E ↦ T w)
      (xiCurrent_xiCreator b φ β a c p q)
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, hw.2.1 q, map_zero, add_zero,
      h q, zero_smul, LinearMap.zero_apply] using heq
  · intro q
    have heq := congrArg (fun T : Module.End R E ↦ T w)
      (mixedCurrent_xiCreator b φ c p q)
    simpa only [Module.End.mul_apply, LinearMap.sub_apply,
      hw.2.2 q, map_zero, hw.1 (q * p), sub_zero] using heq

/-- Every polynomial theta creator preserves harmonics when all ordinary
power moments vanish. -/
theorem thetaCreator_preserves_harmonics
    (h : ∀ k, moment φ (fun i ↦ β i * a i * c i) k = 0)
    (p : Polynomial R) (w : E) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (thetaCreator b φ β a p w) :=
  thetaCreator_preserves_harmonics_of_moments b φ β a c p
    (fun q ↦ ordinaryPolynomialMoment_zero φ β a c h (q * p)) w hw

/-- Every polynomial xi creator preserves harmonics under the same hypothesis. -/
theorem xiCreator_preserves_harmonics
    (h : ∀ k, moment φ (fun i ↦ β i * a i * c i) k = 0)
    (p : Polynomial R) (w : E) (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (xiCreator b φ c p w) :=
  xiCreator_preserves_harmonics_of_moments b φ β a c p
    (fun q ↦ ordinaryPolynomialMoment_zero φ β a c h (q * p)) w hw

/-- The scalar vacuum is harmonic. -/
theorem isHarmonic_one : IsHarmonic b φ β a c (1 : E) := by
  refine ⟨fun p ↦ annihilation_one _, fun p ↦ annihilation_one _, ?_⟩
  intro p
  simp only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply, pairLower,
    Module.End.mul_apply, annihilation_one, map_zero, smul_zero, Finset.sum_const_zero]

theorem mixedCurrent_annihilation (p : Polynomial R) (l : Module.Dual R V) :
    mixedCurrent b φ p * annihilation l = annihilation l * mixedCurrent b φ p := by
  have hpair (i : Fin n) : pairLower b i * annihilation l =
      annihilation l * pairLower b i := by
    unfold pairLower
    rw [mul_assoc, annihilation_anticomm_eq (b.coord (.inl i)) l]
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
    have h := congrArg (fun T : Module.End R E ↦ T (annihilation (b.coord (.inl i)) w))
      (annihilation_anticomm_eq (b.coord (.inr i)) l)
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [h, neg_neg]
  simp only [mixedCurrent, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, hpair]

/-- The harmonic equations are stable under every ordinary contraction. -/
theorem IsHarmonic.annihilation {w : E} (hw : IsHarmonic b φ β a c w)
    (l : Module.Dual R V) : IsHarmonic b φ β a c (annihilation l w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    have h := congrArg (fun T : Module.End R E ↦ T w)
      (annihilation_anticomm_eq (thetaFunctional b φ c p) l)
    have hp : Exterior.annihilation (thetaFunctional b φ c p) w = 0 := hw.1 p
    simpa only [thetaCurrent, Module.End.mul_apply, LinearMap.neg_apply,
      hp, map_zero, neg_zero] using h
  · intro p
    have h := congrArg (fun T : Module.End R E ↦ T w)
      (annihilation_anticomm_eq (xiFunctional b φ β a p) l)
    have hp : Exterior.annihilation (xiFunctional b φ β a p) w = 0 := hw.2.1 p
    simpa only [xiCurrent, Module.End.mul_apply, LinearMap.neg_apply,
      hp, map_zero, neg_zero] using h
  · intro p
    have h := congrArg (fun T : Module.End R E ↦ T w)
      (mixedCurrent_annihilation b φ p l)
    simpa only [Module.End.mul_apply, hw.2.2 p, map_zero] using h

theorem annihilation_involute (l : Module.Dual R V) (w : E) :
    annihilation l (CliffordAlgebra.involute w) =
      -CliffordAlgebra.involute (annihilation l w) := by
  have h := congrArg Neg.neg (CliffordAlgebra.involute_contractLeft
    (Q := (0 : QuadraticForm R V)) l w)
  simpa only [annihilation, neg_neg] using h.symm

theorem mixedCurrent_involute (p : Polynomial R) (w : E) :
    mixedCurrent b φ p (CliffordAlgebra.involute w) =
      CliffordAlgebra.involute (mixedCurrent b φ p w) := by
  simp only [mixedCurrent, LinearMap.sum_apply, LinearMap.smul_apply, pairLower,
    Module.End.mul_apply, annihilation_involute, map_neg, neg_neg, map_sum, map_smul]

/-- The harmonic equations respect the even/odd grading involution. -/
theorem IsHarmonic.involute {w : E} (hw : IsHarmonic b φ β a c w) :
    IsHarmonic b φ β a c (CliffordAlgebra.involute w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    change Exterior.annihilation _ (CliffordAlgebra.involute w) = 0
    rw [annihilation_involute]
    change -CliffordAlgebra.involute (thetaCurrent b φ c p w) = 0
    rw [hw.1 p, map_zero, neg_zero]
  · intro p
    change Exterior.annihilation _ (CliffordAlgebra.involute w) = 0
    rw [annihilation_involute]
    change -CliffordAlgebra.involute (xiCurrent b φ β a p w) = 0
    rw [hw.2.1 p, map_zero, neg_zero]
  · intro p
    rw [mixedCurrent_involute, hw.2.2 p, map_zero]

/-- The suffix polynomial used to create a mark at a prescribed index. -/
def suffixPolynomial (j : Fin n) : Polynomial R :=
  ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (Polynomial.X - Polynomial.C (φ i))

theorem suffixPolynomial_eval_above (j i : Fin n) (hji : j < i) :
    (suffixPolynomial φ j).eval (φ i) = 0 := by
  rw [suffixPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hji)
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

theorem suffixPolynomial_eval_at (j : Fin n) :
    (suffixPolynomial φ j).eval (φ j) =
      ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (φ j - φ i) := by
  simp only [suffixPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]

end PaperVerification.Fermion.Exterior
