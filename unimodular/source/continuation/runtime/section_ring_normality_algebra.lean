module

public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Integral closedness of coefficientwise section rings

An integral element over a polynomial ring has integral coefficients. After
rescaling the polynomial variable by a Cartier generator, this elementary
fact proves normality of a section ring described by local regularity.

The final theorem applies to an arbitrary subring of `K[T]` characterized
by scaled coefficients in integrally closed subrings of `K`. The geometric
application supplies those subrings as the actual local rings of a scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Polynomial
attribute [local instance] Polynomial.algebra

namespace Unimodular.SectionRingNormality

section Range

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- Replacing an injectively embedded integrally closed ring by its actual
image preserves integral closedness in the same ambient ring. -/
theorem range_isIntegrallyClosedIn [IsIntegrallyClosedIn R A] :
    IsIntegrallyClosedIn (algebraMap R A).range A := by
  let f := algebraMap R A
  have hf : Function.Injective f := (isIntegrallyClosedIn_iff.mp
    (inferInstance : IsIntegrallyClosedIn R A)).1
  let e : R ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  apply Subring.isIntegrallyClosedIn_iff.mpr
  intro x hx
  have hc : (algebraMap R A).comp e.symm.toRingHom =
      (RingHom.id A).comp (algebraMap f.range A) := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply a)
  have hi : IsIntegral R x := hx.map_of_comp_eq e.symm.toRingHom (RingHom.id A) hc
  exact IsIntegrallyClosedIn.isIntegral_iff.mp hi

/-- Polynomial extension preserves integral closedness inside a fixed
ambient polynomial ring. No fraction-field identification is assumed. -/
theorem polynomial_isIntegrallyClosedIn [IsIntegrallyClosedIn R A] :
    IsIntegrallyClosedIn R[X] A[X] := by
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, ?_⟩
  · exact Polynomial.map_injective _
      ((isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn R A)).1)
  · intro p hp
    exact (Polynomial.lifts_iff_coeff_lifts p).mpr fun n =>
      IsIntegrallyClosedIn.isIntegral_iff.mp (hp.coeff n)

end Range

section Coefficients

variable {K : Type*} [Field K]

/-- Polynomials whose coefficients lie in the given subring. -/
abbrev coefficientSubring (S : Subring K) : Subring K[X] :=
  Polynomial.liftsRing S.subtype

theorem mem_coefficientSubring_iff (S : Subring K) (p : K[X]) :
    p ∈ coefficientSubring S ↔ ∀ n, p.coeff n ∈ S := by
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]
  constructor
  · intro h n
    obtain ⟨a, ha⟩ := h n
    exact ha ▸ a.property
  · intro h n
    exact ⟨⟨p.coeff n, h n⟩, rfl⟩

theorem coefficientSubring_isIntegrallyClosedIn (S : Subring K)
    [IsIntegrallyClosedIn S K] :
    IsIntegrallyClosedIn (coefficientSubring S) K[X] := by
  letI : IsIntegrallyClosedIn S[X] K[X] := polynomial_isIntegrallyClosedIn S K
  exact range_isIntegrallyClosedIn S[X] K[X]

/-- The literal change of polynomial variable `T ↦ g⁻¹ T`, starting from
the finite graded-sum model of `K[T]`. -/
def normalizePolynomial (g : K) : AddMonoidAlgebra K ℕ →+* K[X] :=
  (Polynomial.aeval (Polynomial.C g⁻¹ * Polynomial.X)).toRingHom.comp
    (Polynomial.toFinsuppIso K).symm.toRingHom

@[simp] theorem normalizePolynomial_coeff (g : K)
    (p : AddMonoidAlgebra K ℕ) (n : ℕ) :
    (normalizePolynomial g p).coeff n = p.coeff n / g ^ n := by
  change (((Polynomial.toFinsuppIso K).symm p).comp
    (Polynomial.C g⁻¹ * Polynomial.X)).coeff n = _
  rw [Polynomial.comp_C_mul_X_coeff]
  simp only [div_eq_mul_inv, inv_pow, Polynomial.toFinsuppIso_symm_apply,
    Polynomial.coeff_ofFinsupp]

/-- Integral closedness of a subring defined by all local scaled-coefficient
conditions. Every condition is checked; neither finite generation nor
generation in degree one is used. -/
theorem scaledCoefficients_isIntegrallyClosedIn
    {ι : Type*} (A : Subring (AddMonoidAlgebra K ℕ))
    (S : ι → Subring K) (g : ι → K)
    (hS : ∀ i, IsIntegrallyClosedIn (S i) K)
    (hA : ∀ p, p ∈ A ↔ ∀ i n, p.coeff n / g i ^ n ∈ S i) :
    IsIntegrallyClosedIn A (AddMonoidAlgebra K ℕ) := by
  apply Subring.isIntegrallyClosedIn_iff.mpr
  intro p hp
  apply (hA p).mpr
  intro i n
  letI : IsIntegrallyClosedIn (S i) K := hS i
  let B := coefficientSubring (S i)
  let f := normalizePolynomial (g i)
  have hf : ∀ q ∈ A, f q ∈ B := by
    intro q hq
    apply (mem_coefficientSubring_iff (S i) (f q)).mpr
    intro d
    rw [normalizePolynomial_coeff]
    exact (hA q).mp hq i d
  have hi : IsIntegral B (f p) :=
    hp.map_of_comp_eq (f.restrict A B hf) f rfl
  have hm : f p ∈ B := Subring.isIntegrallyClosedIn_iff.mp
    (coefficientSubring_isIntegrallyClosedIn (S i)) hi
  simpa only [f, normalizePolynomial_coeff] using
    (mem_coefficientSubring_iff (S i) (f p)).mp hm n

/-- The ordinary normal-domain conclusion, obtained inside the already
normal polynomial ring over the field. -/
theorem scaledCoefficients_isIntegrallyClosed
    {ι : Type*} (A : Subring (AddMonoidAlgebra K ℕ))
    (S : ι → Subring K) (g : ι → K)
    (hS : ∀ i, IsIntegrallyClosedIn (S i) K)
    (hA : ∀ p, p ∈ A ↔ ∀ i n, p.coeff n / g i ^ n ∈ S i) :
    IsIntegrallyClosed A := by
  letI : IsIntegrallyClosed (AddMonoidAlgebra K ℕ) :=
    IsIntegrallyClosed.of_equiv (Polynomial.toFinsuppIso K)
  letI : IsIntegrallyClosedIn A (AddMonoidAlgebra K ℕ) :=
    scaledCoefficients_isIntegrallyClosedIn A S g hS hA
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn A
    (AddMonoidAlgebra K ℕ)

end Coefficients

end Unimodular.SectionRingNormality

#print axioms Unimodular.SectionRingNormality.scaledCoefficients_isIntegrallyClosed

end
