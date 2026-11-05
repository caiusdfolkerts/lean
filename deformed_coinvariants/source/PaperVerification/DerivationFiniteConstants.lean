module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.Derivation.Localization

/-!
# Derivations over a finite subalgebra of constants

In characteristic zero, a derivation of a domain that vanishes on a subalgebra
over which the domain is finite vanishes everywhere. The proof extends the
derivation to the fraction field, forms its actual constant subfield, and
applies the derivative of a separable minimal polynomial. This is the
Jacobian-kernel input needed for the zero-dimensional case of Proposition 6.5.

This supporting theorem does not assume algebraic independence, a nonzero
Jacobian determinant, or vanishing of the derivation on the ambient ring.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.DerivationFiniteConstants

section Field

variable {K L : Type*} [CommRing K] [Field L] [Algebra K L]

/-- The actual kernel of a field-valued derivation is a subfield. -/
def constantField (D : Derivation K L L) : Subfield L where
  carrier := {x | D x = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change D x = 0 at hx
    change D (-x) = 0
    rw [map_neg, hx, neg_zero]
  mul_mem' := by
    intro x y hx hy
    change D x = 0 at hx
    change D y = 0 at hy
    change D (x * y) = 0
    rw [D.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  inv_mem' := by
    intro x hx
    change D x = 0 at hx
    change D x⁻¹ = 0
    rw [D.leibniz_inv, hx, smul_zero]

@[simp] theorem mem_constantField (D : Derivation K L L) (x : L) :
    x ∈ constantField D ↔ D x = 0 := Iff.rfl

/-- The same derivation is linear over its full field of constants. -/
def overConstants (D : Derivation K L L) : Derivation (constantField D) L L where
  toFun := D
  map_add' := map_add D
  map_smul' c x := by
    change D ((c : L) * x) = (c : L) * D x
    rw [D.leibniz, show D (c : L) = 0 from c.property]
    simp only [smul_eq_mul, mul_zero, add_zero]
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz

@[simp] theorem overConstants_apply (D : Derivation K L L) (x : L) :
    overConstants D x = D x := rfl

/-- Algebraic elements over the actual constants have zero derivative in
characteristic zero; separability is proved by the perfect-field instance. -/
theorem apply_eq_zero_of_integral_constants [CharZero L]
    (D : Derivation K L L) (x : L) (hx : IsIntegral (constantField D) x) : D x = 0 := by
  letI : CharZero (constantField D) :=
    { cast_injective := by
        intro m n h
        apply Nat.cast_injective (R := L)
        exact congrArg (fun z : constantField D => (z : L)) h }
  have hsep : (minpoly (constantField D) x).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hx)
  have hcoeff : Polynomial.aeval x (minpoly (constantField D) x).derivative ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero hsep (minpoly.aeval (constantField D) x)
  have hder := (overConstants D).map_aeval (minpoly (constantField D) x) x
  rw [minpoly.aeval, map_zero] at hder
  exact (smul_eq_zero.mp hder.symm).resolve_left hcoeff

end Field

section Domain

variable {K A : Type*} [CommRing K] [CommRing A] [IsDomain A] [CharZero A]
  [Algebra K A]

local notation "Q" => FractionRing A

/-- The standard extension to the fraction field, with the original values
embedded through the injective fraction-ring map. -/
def fractionDerivation (D : Derivation K A A) : Derivation K Q Q :=
  ((Algebra.linearMap A Q).compDer D).extendOfIsLocalization (nonZeroDivisors A)

@[simp] theorem fractionDerivation_algebraMap (D : Derivation K A A) (x : A) :
    fractionDerivation D (algebraMap A Q x) = algebraMap A Q (D x) := by
  rw [fractionDerivation, Derivation.extendOfIsLocalization_algebraMap]
  rfl

/-- A finite extension of a subalgebra of constants has no nonzero derivations
in characteristic zero. The subalgebra is the literal subalgebra of `A`. -/
theorem eq_zero_of_finite_subalgebra (S : Subalgebra K A)
    [Module.Finite S A] (D : Derivation K A A)
    (hS : ∀ s : S, D (s : A) = 0) : D = 0 := by
  letI : CharZero Q :=
    { cast_injective := by
        intro m n h
        apply Nat.cast_injective (R := A)
        apply IsFractionRing.injective A Q
        simpa only [map_natCast] using h }
  let DQ := fractionDerivation D
  let E := constantField DQ
  let inclusion : S →+* E :=
    { toFun := fun s => ⟨algebraMap A Q (s : A), by
        change fractionDerivation D (algebraMap A Q (s : A)) = 0
        rw [fractionDerivation_algebraMap, hS s, map_zero]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun s t => Subtype.ext (map_add _ _ _)
      map_mul' := fun s t => Subtype.ext (map_mul _ _ _) }
  have hcomm : (algebraMap E Q).comp inclusion =
      (algebraMap A Q).comp (algebraMap S A) := by
    apply RingHom.ext
    intro s
    rfl
  have hpoly (x : A) : IsIntegral E (algebraMap A Q x) :=
    (IsIntegral.of_finite S x).map_of_comp_eq inclusion (algebraMap A Q) hcomm
  have hall (x : Q) : IsIntegral E x := by
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
    rw [div_eq_mul_inv]
    exact (hpoly a).mul (hpoly b).inv
  have hDQ (x : Q) : DQ x = 0 := apply_eq_zero_of_integral_constants DQ x (hall x)
  apply Derivation.ext
  intro x
  change D x = 0
  apply IsFractionRing.injective A Q
  have hz := hDQ (algebraMap A Q x)
  change fractionDerivation D (algebraMap A Q x) = 0 at hz
  simpa only [fractionDerivation_algebraMap, map_zero] using
    hz

/-- It suffices to kill the displayed generators of the finite subalgebra;
the proof discharges vanishing on every algebra expression by induction. -/
theorem eq_zero_of_finite_adjoin {ι : Type*} (F : ι → A)
    [Module.Finite (Algebra.adjoin K (Set.range F)) A]
    (D : Derivation K A A) (hF : ∀ i, D (F i) = 0) : D = 0 := by
  apply eq_zero_of_finite_subalgebra (Algebra.adjoin K (Set.range F)) D
  rintro ⟨s, hs⟩
  change D s = 0
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hF i
  | algebraMap c => exact D.map_algebraMap c
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => simp only [D.leibniz, hx, hy, smul_zero, add_zero]

end Domain

end PaperVerification.DerivationFiniteConstants
