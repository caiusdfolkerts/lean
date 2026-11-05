module

public import PaperVerification.FermionNewtonMomentComparison
public import PaperVerification.FermionPowerCoverQuotient

/-!
# Newton colon boxes under arbitrary positive power coverings

Coordinatewise Euclidean division identifies the extended basis with the
literal enlarged rectangle.  Multiplication by the difference product embeds
the colon quotient into the ordinary moment quotient.  Shifting an exponent
inside the enlarged rectangle proves precisely the polynomial independence
needed by the two-color creator argument, without differentiation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def powerRectangleEquiv (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (h : Fin n → ℕ) :
    RectangleIndex (fun i ↦ r i * h i) ≃ PowerResidues r × RectangleIndex h where
  toFun a := ((powerDivModEquiv r hr a.val).1,
    ⟨(powerDivModEquiv r hr a.val).2,by
      intro i
      change a.val i / r i < h i
      exact (Nat.div_lt_iff_lt_mul (hr i)).mpr (by simpa only [Nat.mul_comm] using a.property i)⟩)
  invFun p := ⟨scalePowerExponent r p.2.val + residuePowerExponent p.1,by
    intro i
    simp only [Finsupp.add_apply,scalePowerExponent_apply,residuePowerExponent_apply]
    have ha := p.2.property i
    have hb := (p.1 i).isLt
    have hm := Nat.mul_le_mul_left (r i) (Nat.succ_le_of_lt ha)
    nlinarith⟩
  left_inv a := by
    apply Subtype.ext
    exact (powerDivModEquiv r hr).left_inv a.val
  right_inv p := by
    have he := (powerDivModEquiv r hr).right_inv (p.1,p.2.val)
    have he₁ := congrArg (fun z : PowerResidues r × (Fin n →₀ ℕ) ↦ z.1) he
    have he₂ := congrArg (fun z : PowerResidues r × (Fin n →₀ ℕ) ↦ z.2) he
    apply Prod.ext
    · exact he₁
    · apply Subtype.ext
      exact he₂

theorem powerRectangle_decomposition (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (h : Fin n → ℕ) (a : RectangleIndex (fun i ↦ r i * h i)) :
    scalePowerExponent r (powerRectangleEquiv r hr h a).2.val +
      residuePowerExponent (powerRectangleEquiv r hr h a).1 = a.val :=
  (powerDivModEquiv r hr).left_inv a.val

def powerCoverRectangleBasis (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (I : Ideal (P (F := F) (n := n))) (h : Fin n → ℕ)
    (B : Module.Basis (RectangleIndex h) F (P (F := F) (n := n) ⧸ I)) :
    Module.Basis (RectangleIndex (fun i ↦ r i * h i)) F
      (P (F := F) (n := n) ⧸ I.map (powerSubstitution r).toRingHom) :=
  (powerCoverQuotientBasis r hr I B).reindex (powerRectangleEquiv r hr h).symm

@[simp] theorem powerCoverRectangleBasis_apply
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (I : Ideal (P (F := F) (n := n))) (h : Fin n → ℕ)
    (B : Module.Basis (RectangleIndex h) F (P (F := F) (n := n) ⧸ I))
    (hB : ∀ a, B a = Ideal.Quotient.mk I (monomial a.val 1))
    (a : RectangleIndex (fun i ↦ r i * h i)) :
    powerCoverRectangleBasis r hr I h B a =
      Ideal.Quotient.mk (I.map (powerSubstitution r).toRingHom) (monomial a.val 1) := by
  rw [powerCoverRectangleBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  rw [powerCoverQuotientBasis_apply r hr I B (fun a ↦ monomial a.val 1) hB,
    powerSubstitution_monomial,monomial_mul_monomial,one_mul,powerRectangle_decomposition]

theorem map_powerMomentIdeal (r : Fin n → ℕ) (β : Fin n → F) (s : ℕ) :
    (powerMomentIdeal (fun _ ↦ 1) β s).map (powerSubstitution r).toRingHom =
      powerMomentIdeal r β s := by
  rw [powerMomentIdeal,Ideal.map_span,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  change powerSubstitution r (powerMoment (fun _ ↦ 1) β s j) = powerMoment r β s j
  simp only [powerMoment,map_sum,map_mul,map_pow,powerSubstitution,
    MvPolynomial.aeval_C,MvPolynomial.aeval_X,MvPolynomial.algebraMap_eq,one_mul,pow_mul]

theorem covered_principalColon_eq_map_contraction
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    principalColon (powerMomentIdeal r β s) (powerSubstitution r (differenceProduct σ)) =
      (contractionIdeal β (fun _ ↦ s) σ).map (powerSubstitution r).toRingHom := by
  rw [← map_powerMomentIdeal r β s,← map_principalColon_powerSubstitution r hr,
    ordinary_principalColon_eq_contraction β s hs σ hσ hβ]

/-- All literal enlarged monomials are independent modulo the covered
ordinary colon. This includes covering degrees divisible by the characteristic. -/
theorem covered_colon_rectangle_independent
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hh : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i) :
    LinearIndependent F
      (fun a : RectangleIndex (fun i ↦ r i * heightDegree (fun _ ↦ s) σ i) ↦
        Ideal.Quotient.mk
          (principalColon (powerMomentIdeal r β s) (powerSubstitution r (differenceProduct σ)))
          (monomial a.val 1)) := by
  rw [covered_principalColon_eq_map_contraction r hr β s hs σ hσ hβ]
  let B := contractionRectangleBasis β (fun _ ↦ s) σ (compatible_constant s σ) hσ hβ hh
  have h := (powerCoverRectangleBasis r hr (contractionIdeal β (fun _ ↦ s) σ)
    (heightDegree (fun _ ↦ s) σ) B).linearIndependent
  have hb : (fun a ↦ powerCoverRectangleBasis r hr (contractionIdeal β (fun _ ↦ s) σ)
      (heightDegree (fun _ ↦ s) σ) B a) =
      (fun a : RectangleIndex (fun i ↦ r i * heightDegree (fun _ ↦ s) σ i) ↦
        Ideal.Quotient.mk ((contractionIdeal β (fun _ ↦ s) σ).map (powerSubstitution r).toRingHom)
          (monomial a.val 1)) := by
    funext a
    exact powerCoverRectangleBasis_apply r hr _ _ B
      (fun a ↦ contractionRectangleBasis_apply β (fun _ ↦ s) σ (compatible_constant s σ) hσ hβ hh a) a
  change LinearIndependent F (fun a ↦ powerCoverRectangleBasis r hr _ _ B a) at h
  rw [hb] at h
  exact h

theorem covered_difference_rectangle_independent
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hh : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i) :
    LinearIndependent F
      (fun a : RectangleIndex (fun i ↦ r i * heightDegree (fun _ ↦ s) σ i) ↦
        Ideal.Quotient.mk (powerMomentIdeal r β s)
          (powerSubstitution r (differenceProduct σ) * monomial a.val 1)) := by
  have h := (covered_colon_rectangle_independent r hr β s hs σ hσ hβ hh).map'
    (colonMultiplication (K := F) (powerMomentIdeal r β s) (powerSubstitution r (differenceProduct σ)))
    (LinearMap.ker_eq_bot.mpr (colonMultiplication_injective _ _))
  simpa only [Function.comp_def,colonMultiplication_mk] using h

/-- Equation (14): shifting the small rectangle into the actual enlarged
colon rectangle proves its independence after multiplication by the full
diagonal factor. The bound is a genuine exponent containment condition. -/
theorem shifted_difference_rectangle_independent
    (r : Fin n → ℕ) (hr : ∀ i, 0 < r i) (β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i))
    (hh : ∀ i, 0 < profileHeight (fun _ ↦ s) σ i)
    (b : Fin n →₀ ℕ) (d : Fin n → ℕ)
    (hd : ∀ i, d i + b i ≤ r i * heightDegree (fun _ ↦ s) σ i) :
    LinearIndependent F
      (fun a : RectangleIndex d ↦ Ideal.Quotient.mk (powerMomentIdeal r β s)
        (monomial a.val 1 * (monomial b 1 * powerSubstitution r (differenceProduct σ)))) := by
  let shift : RectangleIndex d → RectangleIndex (fun i ↦ r i * heightDegree (fun _ ↦ s) σ i) :=
    fun a ↦ ⟨a.val + b,fun i ↦ by
      have ha := a.property i
      have hb := hd i
      simp only [Finsupp.add_apply]
      omega⟩
  have hinj : Function.Injective shift := by
    intro a c hac
    apply Subtype.ext
    have he : a.val + b = c.val + b := congrArg Subtype.val hac
    exact add_right_cancel he
  have h := (covered_difference_rectangle_independent r hr β s hs σ hσ hβ hh).comp shift hinj
  convert h using 1
  funext a
  dsimp only [shift,Function.comp_apply]
  apply congrArg (Ideal.Quotient.mk (powerMomentIdeal r β s))
  rw [show monomial (a.val + b) (1 : F) = monomial a.val 1 * monomial b 1 by
    rw [monomial_mul_monomial, one_mul]]
  ring

end PaperVerification.Fermion.Newton
