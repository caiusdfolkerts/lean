module

public import sunlet.normalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The localized algebra of the normalized coordinates

Only the two unit coordinates at each non-base position are inverted.  In
particular, the diagonal coordinates and the two coordinates at each
non-identity color remain arbitrary affine variables.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Sunlet.Normalization

inductive Variable (ι Ω : Type*) (e : ι) (o : Ω) where
  | z : Ω → Variable ι Ω e o
  | k : {b : Ω // b ≠ o} → Variable ι Ω e o
  | l : {b : Ω // b ≠ o} → Variable ι Ω e o
  | u : {a : ι // a ≠ e} → Variable ι Ω e o
  | v : {a : ι // a ≠ e} → Variable ι Ω e o
  deriving DecidableEq

variable {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω] [Fintype Ω]

/-- A disjoint-sum presentation makes the exact number of normalized variables explicit. -/
def variableEquivSum :
    Variable ι Ω e o ≃
      Ω ⊕ ({b : Ω // b ≠ o} ⊕ ({b : Ω // b ≠ o} ⊕
        ({a : ι // a ≠ e} ⊕ {a : ι // a ≠ e}))) where
  toFun
    | .z b => .inl b
    | .k b => .inr (.inl b)
    | .l b => .inr (.inr (.inl b))
    | .u a => .inr (.inr (.inr (.inl a)))
    | .v a => .inr (.inr (.inr (.inr a)))
  invFun
    | .inl b => .z b
    | .inr (.inl b) => .k b
    | .inr (.inr (.inl b)) => .l b
    | .inr (.inr (.inr (.inl a))) => .u a
    | .inr (.inr (.inr (.inr a))) => .v a
  left_inv i := by cases i <;> rfl
  right_inv i := by rcases i with b | b | b | a | a <;> rfl


instance variableFintype [Fintype ι] (e : ι) (o : Ω) : Fintype (Variable ι Ω e o) :=
  Fintype.ofEquiv _ (variableEquivSum (e := e) (o := o)).symm

abbrev PolynomialRing (K : Type*) [CommRing K] (e : ι) (o : Ω) :=
  MvPolynomial (Variable ι Ω e o) K

def denominator (K : Type*) [CommRing K] (e : ι) (o : Ω) : PolynomialRing K e o :=
  ∏ b : {b : Ω // b ≠ o}, MvPolynomial.X (.k b) * MvPolynomial.X (.l b)

abbrev LocalizedRing (K : Type*) [CommRing K] (e : ι) (o : Ω) :=
  Localization.Away (denominator K e o)

variable {K : Type*} [Field K] {e : ι} {o : Ω}

def parameterVariable (i : Variable ι Ω e o) : LocalizedRing K e o :=
  algebraMap (PolynomialRing K e o) (LocalizedRing K e o) (MvPolynomial.X i)

theorem variable_k_isUnit (b : {b : Ω // b ≠ o}) :
    IsUnit (parameterVariable (K := K) (.k b) : LocalizedRing K e o) := by
  apply IsLocalization.Away.isUnit_of_dvd (denominator K e o)
  exact dvd_trans (dvd_mul_right _ _) (Finset.dvd_prod_of_mem _ (Finset.mem_univ b))

theorem variable_l_isUnit (b : {b : Ω // b ≠ o}) :
    IsUnit (parameterVariable (K := K) (.l b) : LocalizedRing K e o) := by
  apply IsLocalization.Away.isUnit_of_dvd (denominator K e o)
  exact dvd_trans (dvd_mul_left _ _) (Finset.dvd_prod_of_mem _ (Finset.mem_univ b))

/-- The universal normalized point over the localized polynomial ring. -/
def universalParameters : Parameters (LocalizedRing K e o) ι Ω e o where
  z b := parameterVariable (.z b)
  k b := if hb : b = o then 1 else (variable_k_isUnit (K := K) (e := e) ⟨b, hb⟩).unit
  l b := if hb : b = o then 1 else (variable_l_isUnit (K := K) (e := e) ⟨b, hb⟩).unit
  u a := parameterVariable (.u a)
  v a := parameterVariable (.v a)
  k_base := by simp
  l_base := by simp

def normalizedComorphism (π : ι → Equiv.Perm Ω) :
    MvPolynomial (ι × Ω) K →ₐ[K] LocalizedRing K e o :=
  MvPolynomial.aeval (parameterMap π universalParameters)

def specialization : MvPolynomial (Sunlet.ParamVar ι Ω) K →ₐ[K] LocalizedRing K e o :=
  MvPolynomial.aeval (expand universalParameters).toCoordinates

theorem specialization_coordinate (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) (ab : ι × Ω) :
    specialization (Sunlet.coordinatePolynomial (K := K) π ab) =
      parameterMap π (universalParameters (K := K) (e := e) (o := o)) ab := by
  rw [specialization, Sunlet.aeval_coordinatePolynomial_algebra]
  exact congrFun (expand_parameterMap π he universalParameters) ab

theorem specialization_comp (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω) :
    (specialization (K := K) (e := e) (o := o)).comp
        (PolynomialImage.comorphism (Sunlet.coordinatePolynomial (K := K) π)) =
      normalizedComorphism (K := K) (e := e) (o := o) π := by
  ext ab
  simp only [AlgHom.comp_apply, PolynomialImage.comorphism, normalizedComorphism,
    MvPolynomial.aeval_X]
  exact specialization_coordinate π he ab

theorem definingIdeal_le_normalizedKernel (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) :
    PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π) ≤
      RingHom.ker (normalizedComorphism (K := K) (e := e) (o := o) π) := by
  intro f hf
  change PolynomialImage.comorphism (Sunlet.coordinatePolynomial π) f = 0 at hf
  change normalizedComorphism π f = 0
  calc
    _ = specialization (PolynomialImage.comorphism (Sunlet.coordinatePolynomial π) f) :=
      (AlgHom.congr_fun (specialization_comp (o := o) π he) f).symm
    _ = 0 := by rw [hf, map_zero]

section Evaluation

variable {L : Type*} [Field L] [Algebra K L]

def variableValues (p : Parameters L ι Ω e o) : Variable ι Ω e o → L
  | .z b => p.z b
  | .k b => p.k b
  | .l b => p.l b
  | .u a => p.u a
  | .v a => p.v a

theorem evaluated_denominator_isUnit (p : Parameters L ι Ω e o) :
    IsUnit (MvPolynomial.aeval (variableValues p) (denominator K e o)) := by
  apply isUnit_iff_ne_zero.mpr
  simp only [denominator, map_prod, map_mul, MvPolynomial.aeval_X, variableValues]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)

/-- Any normalized field-valued point evaluates the localized algebra. -/
def evaluate (p : Parameters L ι Ω e o) : LocalizedRing K e o →ₐ[K] L :=
  IsLocalization.Away.liftAlgHom (denominator K e o) (evaluated_denominator_isUnit p)

@[simp] theorem evaluate_variable (p : Parameters L ι Ω e o) (i : Variable ι Ω e o) :
    evaluate (K := K) p (parameterVariable i) = variableValues p i := by
  simp [evaluate, parameterVariable, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem evaluate_universal_z (p : Parameters L ι Ω e o) (b : Ω) :
    evaluate (K := K) p ((universalParameters (K := K) (e := e) (o := o)).z b) = p.z b := by
  simp [universalParameters, variableValues]

@[simp] theorem evaluate_universal_k (p : Parameters L ι Ω e o) (b : Ω) :
    evaluate (K := K) p ((universalParameters (K := K) (e := e) (o := o)).k b :
      LocalizedRing K e o) = (p.k b : L) := by
  by_cases hb : b = o
  · subst b
    simp [universalParameters, p.k_base]
  · simp [universalParameters, hb, variableValues]

@[simp] theorem evaluate_universal_l (p : Parameters L ι Ω e o) (b : Ω) :
    evaluate (K := K) p ((universalParameters (K := K) (e := e) (o := o)).l b :
      LocalizedRing K e o) = (p.l b : L) := by
  by_cases hb : b = o
  · subst b
    simp [universalParameters, p.l_base]
  · simp [universalParameters, hb, variableValues]

@[simp] theorem evaluate_universal_u (p : Parameters L ι Ω e o) (a : {a : ι // a ≠ e}) :
    evaluate (K := K) p ((universalParameters (K := K) (e := e) (o := o)).u a) = p.u a := by
  simp [universalParameters, variableValues]

@[simp] theorem evaluate_universal_v (p : Parameters L ι Ω e o) (a : {a : ι // a ≠ e}) :
    evaluate (K := K) p ((universalParameters (K := K) (e := e) (o := o)).v a) = p.v a := by
  simp [universalParameters, variableValues]

theorem evaluate_coordinate (p : Parameters L ι Ω e o)
    (π : ι → Equiv.Perm Ω) (a : ι) (b : Ω) :
    evaluate (K := K) p (coordinate π (universalParameters (K := K) (e := e) (o := o)) a b) =
      coordinate π p a b := by
  by_cases ha : a = e
  · simp [coordinate, ha]
  · simp [coordinate, ha, map_units_inv, Units.val_inv_eq_inv_val]

end Evaluation

abbrev OriginalRing (K ι Ω : Type*) [CommRing K] :=
  MvPolynomial (Sunlet.ParamVar ι Ω) K

abbrev OriginalField (K ι Ω : Type*) [CommRing K] :=
  FractionRing (OriginalRing K ι Ω)

def genericCoordinates (i : Sunlet.ParamVar ι Ω) : OriginalField K ι Ω :=
  algebraMap (OriginalRing K ι Ω) (OriginalField K ι Ω) (MvPolynomial.X i)

def genericParameters : Sunlet.Parameters (OriginalField K ι Ω) ι Ω :=
  Sunlet.Parameters.ofCoordinates genericCoordinates

theorem genericCoordinates_ne_zero (i : Sunlet.ParamVar ι Ω) :
    genericCoordinates (K := K) i ≠ 0 := by
  intro hi
  apply MvPolynomial.X_ne_zero (R := K) i
  apply IsFractionRing.injective (OriginalRing K ι Ω) (OriginalField K ι Ω)
  simpa [genericCoordinates] using hi

theorem generic_s_ne_zero (b : Ω) : (genericParameters (K := K) (ι := ι)).s b ≠ 0 :=
  genericCoordinates_ne_zero (.s b)

theorem generic_h_ne_zero (b : Ω) : (genericParameters (K := K) (ι := ι)).h b ≠ 0 :=
  genericCoordinates_ne_zero (.h b)

/-- The two identity-color variables are independent, in every characteristic. -/
theorem generic_gamma_ne_zero (e : ι) :
    (genericParameters (K := K) (Ω := Ω)).u e + genericParameters.v e ≠ 0 := by
  intro h
  have hp : (MvPolynomial.X (.u e) : OriginalRing K ι Ω) + MvPolynomial.X (.v e) = 0 := by
    apply IsFractionRing.injective (OriginalRing K ι Ω) (OriginalField K ι Ω)
    simpa [genericParameters, Sunlet.Parameters.ofCoordinates, genericCoordinates] using h
  let x : Sunlet.ParamVar ι Ω → K := fun i => match i with
    | .u _ => 1
    | _ => 0
  have hx := congrArg (MvPolynomial.aeval x) hp
  simpa [x] using hx

/-- Evaluation at the normalized generic point of the original affine space. -/
def normalizingHom : LocalizedRing K e o →ₐ[K] OriginalField K ι Ω :=
  evaluate (normalize genericParameters generic_s_ne_zero generic_h_ne_zero
    (generic_gamma_ne_zero e))

theorem normalizingHom_coordinate (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) (a : ι) (b : Ω) :
    normalizingHom (coordinate π (universalParameters (K := K) (e := e) (o := o)) a b) =
      Sunlet.coordinate π (genericParameters (K := K)) a b := by
  rw [normalizingHom, evaluate_coordinate]
  exact normalize_coordinate π he genericParameters generic_s_ne_zero generic_h_ne_zero
    (generic_gamma_ne_zero e) a b

theorem generic_coordinate (π : ι → Equiv.Perm Ω) (ab : ι × Ω) :
    Sunlet.parameterMap π (genericParameters (K := K)) ab =
      algebraMap (OriginalRing K ι Ω) (OriginalField K ι Ω)
        (Sunlet.coordinatePolynomial (K := K) π ab) := by
  simp [Sunlet.parameterMap, Sunlet.coordinate, genericParameters,
    Sunlet.Parameters.ofCoordinates, genericCoordinates, Sunlet.coordinatePolynomial]

theorem normalizingHom_comp (π : ι → Equiv.Perm Ω) (he : π e = Equiv.refl Ω) :
    (normalizingHom (K := K) (e := e) (o := o)).comp (normalizedComorphism π) =
      (IsScalarTower.toAlgHom K (OriginalRing K ι Ω) (OriginalField K ι Ω)).comp
        (PolynomialImage.comorphism (Sunlet.coordinatePolynomial (K := K) π)) := by
  ext ab
  simp only [AlgHom.comp_apply, normalizedComorphism, PolynomialImage.comorphism,
    MvPolynomial.aeval_X, IsScalarTower.toAlgHom_apply]
  change normalizingHom (coordinate π universalParameters ab.1 ab.2) = _
  rw [normalizingHom_coordinate π he]
  exact generic_coordinate π ab

/-- The normalized relations imply the original relations by evaluating in the
fraction field of the actual original parameter polynomial ring. -/
theorem normalizedKernel_le_definingIdeal (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) :
    RingHom.ker (normalizedComorphism (K := K) (e := e) (o := o) π) ≤
      PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π) := by
  intro f hf
  change normalizedComorphism π f = 0 at hf
  change PolynomialImage.comorphism (Sunlet.coordinatePolynomial π) f = 0
  apply IsFractionRing.injective (OriginalRing K ι Ω) (OriginalField K ι Ω)
  rw [map_zero]
  calc
    _ = normalizingHom (normalizedComorphism (K := K) (e := e) (o := o) π f) :=
      (AlgHom.congr_fun (normalizingHom_comp (o := o) π he) f).symm
    _ = 0 := by rw [hf, map_zero]

/-- Gauge normalization preserves the complete defining ideal, with no
assumption of characteristic zero or algebraic closedness. -/
theorem definingIdeal_eq_normalizedKernel (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) :
    PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π) =
      RingHom.ker (normalizedComorphism (K := K) (e := e) (o := o) π) :=
  le_antisymm (definingIdeal_le_normalizedKernel π he) (normalizedKernel_le_definingIdeal π he)

/-- The original coordinate algebra is the subalgebra generated by the
normalized coordinates in the localized ring with fewer independent variables. -/
def coordinateRingEquivNormalizedImage (π : ι → Equiv.Perm Ω)
    (he : π e = Equiv.refl Ω) :
    (MvPolynomial (ι × Ω) K ⧸
      PolynomialImage.definingIdeal (Sunlet.coordinatePolynomial (K := K) π)) ≃ₐ[K]
        (normalizedComorphism (K := K) (e := e) (o := o) π).range :=
  (Ideal.quotientEquivAlgOfEq K (definingIdeal_eq_normalizedKernel π he)).trans
    (Ideal.quotientKerEquivRange (normalizedComorphism π))

end Sunlet.Normalization
