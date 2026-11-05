module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.RingTheory.RingHom.Basis

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.Fermion

open MvPolynomial

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The residue exponents for the covering `Yᵢ = Xᵢ ^ rᵢ`. -/
abbrev PowerResidues (r : Fin n → ℕ) := ∀ i, Fin (r i)

noncomputable def scalePowerExponent (r : Fin n → ℕ) (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ r i * d i

noncomputable def residuePowerExponent {r : Fin n → ℕ} (b : PowerResidues r) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (b i : ℕ)

@[simp] theorem scalePowerExponent_apply (r : Fin n → ℕ) (d : Fin n →₀ ℕ) (i : Fin n) :
    scalePowerExponent r d i = r i * d i := by
  classical
  simp [scalePowerExponent]

@[simp] theorem residuePowerExponent_apply {r : Fin n → ℕ} (b : PowerResidues r) (i : Fin n) :
    residuePowerExponent b i = (b i : ℕ) := by
  classical
  simp [residuePowerExponent]

/-- Coordinatewise Euclidean division, allowing a different positive degree at every index. -/
noncomputable def powerDivModEquiv (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) :
    (Fin n →₀ ℕ) ≃ (PowerResidues r × (Fin n →₀ ℕ)) where
  toFun d := (fun i ↦ ⟨d i % r i, Nat.mod_lt _ (hr i)⟩,
    Finsupp.equivFunOnFinite.symm fun i ↦ d i / r i)
  invFun p := scalePowerExponent r p.2 + residuePowerExponent p.1
  left_inv d := by
    ext i
    simp [Nat.div_add_mod]
  right_inv p := by
    apply Prod.ext
    · funext i
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (p.1 i).isLt]
    · ext i
      simp [Nat.mul_add_div (hr i), Nat.div_eq_of_lt (p.1 i).isLt]

 theorem powerDivModEquiv_scale_add (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (a d : Fin n →₀ ℕ) :
    powerDivModEquiv r hr (scalePowerExponent r a + d) =
      ((powerDivModEquiv r hr d).1, a + (powerDivModEquiv r hr d).2) := by
  apply Prod.ext
  · funext i
    apply Fin.ext
    simp [powerDivModEquiv]
  · ext i
    simp [powerDivModEquiv, Nat.mul_add_div (hr i)]

/-- The literal heterogeneous power substitution. -/
noncomputable def powerSubstitution (r : Fin n → ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval fun i ↦ X i ^ r i

@[simp] theorem powerSubstitution_X (r : Fin n → ℕ) (i : Fin n) :
    powerSubstitution (R := R) r (X i) = X i ^ r i := by
  simp [powerSubstitution]

 theorem powerSubstitution_monomial (r : Fin n → ℕ) (d : Fin n →₀ ℕ) (a : R) :
    powerSubstitution r (monomial d a) = monomial (scalePowerExponent r d) a := by
  classical
  rw [powerSubstitution, aeval_monomial, monomial_eq]
  rw [d.prod_fintype _ (fun _ ↦ pow_zero _),
    (scalePowerExponent r d).prod_fintype _ (fun _ ↦ pow_zero _)]
  simp [pow_mul]

/-- The actual additive coordinate isomorphism on polynomial coefficients. -/
noncomputable def powerCoverRepr (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) :
    MvPolynomial (Fin n) R ≃+ (PowerResidues r →₀ MvPolynomial (Fin n) R) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <|
    (Finsupp.domCongr (powerDivModEquiv r hr)).trans <|
    Finsupp.curryAddEquiv.trans <|
      Finsupp.mapRange.addEquiv AddMonoidAlgebra.coeffAddEquiv.symm

 theorem powerCoverRepr_monomial (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (d : Fin n →₀ ℕ) (a : R) :
    powerCoverRepr r hr (monomial d a) =
      Finsupp.single (powerDivModEquiv r hr d).1
        (monomial (powerDivModEquiv r hr d).2 a) := by
  simp [powerCoverRepr, ← single_eq_monomial]

 theorem powerCoverRepr_substitution_mul (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (a b : MvPolynomial (Fin n) R) :
    powerCoverRepr r hr (powerSubstitution r a * b) = a • powerCoverRepr r hr b := by
  classical
  induction a using MvPolynomial.induction_on' with
  | monomial γ a =>
    induction b using MvPolynomial.induction_on' with
    | monomial d b =>
      rw [powerSubstitution_monomial, monomial_mul_monomial, powerCoverRepr_monomial,
        powerDivModEquiv_scale_add, powerCoverRepr_monomial, Finsupp.smul_single,
        smul_eq_mul, monomial_mul_monomial]
    | add b₁ b₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, smul_add]
  | add a₁ a₂ h₁ h₂ => rw [map_add, add_mul, map_add, h₁, h₂, add_smul]

/-- The monomials `∏ Xᵢ ^ bᵢ`, `bᵢ < rᵢ`, are an explicit basis over the power subring. -/
noncomputable def powerCoverBasis (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) :
    @Module.Basis (PowerResidues r) (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)
      _ _ (powerSubstitution (R := R) r).toRingHom.toAlgebra.toModule :=
  RingHom.basisOfAddEquiv _ (powerCoverRepr r hr) (powerCoverRepr_substitution_mul r hr)

@[simp] theorem powerCoverBasis_apply (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (b : PowerResidues r) :
    powerCoverBasis (R := R) r hr b = monomial (residuePowerExponent b) 1 := by
  classical
  have hb : powerDivModEquiv r hr (residuePowerExponent b) = (b, 0) := by
    apply Prod.ext
    · funext i
      apply Fin.ext
      simp [powerDivModEquiv, Nat.mod_eq_of_lt (b i).isLt]
    · ext i
      simp [powerDivModEquiv, Nat.div_eq_of_lt (b i).isLt]
  rw [powerCoverBasis, RingHom.basisOfAddEquiv_apply, AddEquiv.symm_apply_eq,
    powerCoverRepr_monomial, hb, ← C_apply, C_1]

 theorem powerCoverRepr_residue_monomial (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (b : PowerResidues r) :
    powerCoverRepr (R := R) r hr (monomial (residuePowerExponent b) 1) =
      Finsupp.single b 1 := by
  rw [← powerCoverBasis_apply r hr b, powerCoverBasis, RingHom.basisOfAddEquiv_apply,
    AddEquiv.apply_symm_apply]

 theorem powerSubstitution_flat {R : Type*} [CommRing R]
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) :
    (powerSubstitution (R := R) r).toRingHom.Flat :=
  RingHom.flat_of_addEquiv _ (powerCoverRepr r hr) (powerCoverRepr_substitution_mul r hr)

 theorem powerSubstitution_finrank {R : Type*} [CommRing R]
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) :
    (powerSubstitution (R := R) r).toRingHom.finrank = fun _ ↦ ∏ i, r i := by
  rw [RingHom.finrank_of_addEquiv _ (powerCoverRepr r hr)
    (powerCoverRepr_substitution_mul r hr)]
  simp [PowerResidues, Nat.card_eq_fintype_card, Fintype.card_pi]

end PaperVerification.Fermion
