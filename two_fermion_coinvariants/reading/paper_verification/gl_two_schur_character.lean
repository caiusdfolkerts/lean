module

public import PaperVerification.FermionColorSchurCoefficients
public import TauCeti.RepresentationTheory.ClassicalGroups.UnitaryTrick
public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
public import TauCeti.LinearAlgebra.Trace.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Actual two-dimensional tensor powers and their symmetric-power summands

The summands carry the original symmetric-power action and determinant
character. Their multiplicities are the nonnegative binomial differences,
including the j=0 convention. Character equality is proved on the full
invertible diagonal torus; the pinned rational-representation theorem then
supplies an equivariant equivalence. No action is transported to make this
statement true. Irreducibility is a separate theorem, not a premise here.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct DirectSum

namespace PaperVerification.Fermion.ColorSchur

section Scalar
variable {F : Type*} [Field F]

/-- Homogenization at a nonzero second coordinate. -/
theorem scale_ratio_pow (u v : F) (hv : v ≠ 0) (n r : ℕ) (hr : r ≤ n) :
    v^n * (u/v)^r = u^r * v^(n-r) := by
  have hp : v^n = v^(n-r) * v^r := by
    rw [←pow_add, Nat.sub_add_cancel hr]
  rw [div_pow, hp]
  calc
    (v^(n-r) * v^r) * (u^r/v^r) =
        (u^r * v^(n-r)) * (v^r/v^r) := by ring
    _ = u^r * v^(n-r) := by rw [div_self (pow_ne_zero r hv), mul_one]

/-- The character polynomial of Sym^a(V) tensor det^b. -/
def schurValue (a b : ℕ) (u v : F) : F :=
  (u*v)^b * ∑ i ∈ Finset.range (a+1), u^i * v^(a-i)

theorem scale_schurWindow (ell j : ℕ) (hj : j ≤ ell/2)
    (u v : F) (hv : v ≠ 0) :
    v^ell * ((u/v)^j * ∑ i ∈ Finset.range (ell-2*j+1), (u/v)^i) =
      schurValue (ell-2*j) j u v := by
  unfold schurValue
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ ell-2*j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [←pow_add, scale_ratio_pow u v hv ell (j+i) (by omega)]
  rw [show ell-(j+i)=j+(ell-2*j-i) by omega, pow_add, pow_add, mul_pow]
  ring

/-- The complete tensor-power character identity at every invertible
second coordinate. The representation application uses only units. -/
theorem tensor_power_schur_value (ell : ℕ) (u v : F) (hv : v ≠ 0) :
    (u+v)^ell = ∑ j ∈ Finset.range (ell/2+1),
      (ballotMultiplicity ell j : F) * schurValue (ell-2*j) j u v := by
  have h := congrArg (Polynomial.eval₂RingHom (Nat.castRingHom F) (u/v))
    (tensor_power_schur_polynomial ell)
  simp only [schurWindow, geometricPolynomial, map_pow, map_add, map_one,
    map_sum, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Nat.coe_castRingHom] at h
  have h' := congrArg (fun z : F ↦ v^ell*z) h
  have hl : v^ell*(1+u/v)^ell=(u+v)^ell := by
    rw [←mul_pow]
    congr 1
    field_simp
    ring
  rw [hl, Finset.mul_sum] at h'
  refine h'.trans (Finset.sum_congr rfl fun j hj ↦ ?_)
  rw [mul_left_comm, scale_schurWindow ell j
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) u v hv]

end Scalar

abbrev SchurSpace (F : Type) [Field F] (a b : ℕ) :=
  (Sym[F]^a (Fin 2 → F)) ⊗[F] F

/-- Use the original tensor-product additive group through a named instance.
This keeps concrete-field elaboration from reconstructing the quotient and
tensor-product instance hierarchy at every dependent direct-sum component.
The determinant exponent changes the action but not this carrier, so the
same instance applies to every value of that exponent. -/
instance schurSpaceAddCommGroup (F : Type) [Field F] (a : ℕ) :
    AddCommGroup (SchurSpace F a 0) :=
  inferInstanceAs (AddCommGroup ((Sym[F]^a (Fin 2 → F)) ⊗[F] F))

/-- The independently defined standard symmetric-power and determinant actions. -/
def schurRepresentation (F : Type) [Field F] (a b : ℕ) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F) (SchurSpace F a b) :=
  (TauCeti.symPowerRep F 2 a).tprod (TauCeti.detPowerRep F 2 (b : ℤ))

theorem schurRepresentation_character {F : Type} [Field F]
    (a b : ℕ) (t : Fin 2 → Fˣ) :
    Representation.character (k := F) (V := SchurSpace F a b)
      (schurRepresentation F a b) (TauCeti.diagGL t) =
      schurValue a b (t 0 : F) (t 1 : F) := by
  rw [schurRepresentation, Representation.char_tensor, Pi.mul_apply,
    TauCeti.char_symPowerRep_diagonal, TauCeti.eval_hsymm_fin_two,
    TauCeti.char_detPowerRep]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, TauCeti.diagGL_apply,
    show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide,
    if_true, if_false, mul_zero, sub_zero]
  exact mul_comm _ _

theorem schurRepresentation_polynomial (a b : ℕ) :
    TauCeti.IsPolynomialRep (schurRepresentation ℂ a b) :=
  (TauCeti.isPolynomialRep_symPowerRep 2 a).tprod
    (TauCeti.isPolynomialRep_detPowerRep_of_nonneg (Int.natCast_nonneg b))

/-- Each copy is indexed explicitly, so the binomial difference is an
actual direct-sum multiplicity, not only a scalar coefficient. -/
abbrev SchurCopyIndex (ell : ℕ) :=
  Σ j : Fin (ell/2+1), Fin (ballotMultiplicity ell j.val)

def tensorSchurRepresentation (ell : ℕ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (⨁ j : SchurCopyIndex ell, SchurSpace ℂ (ell-2*j.1.val) j.1.val) :=
  Representation.directSum (fun j ↦ schurRepresentation ℂ (ell-2*j.1.val) j.1.val)

/-- Trace of the actual direct-sum linear action. -/
theorem trace_lmap {F J : Type*} [Field F] [Fintype J] [DecidableEq J]
    (M : J → Type*) [∀ j, AddCommGroup (M j)] [∀ j, Module F (M j)]
    [∀ j, Module.Finite F (M j)] (f : ∀ j, M j →ₗ[F] M j) :
    LinearMap.trace F (⨁ j, M j) (DirectSum.lmap f) =
      ∑ j, LinearMap.trace F (M j) (f j) := by
  let e := DirectSum.linearEquivFunOnFintype F J M
  have he : e.conj (DirectSum.lmap f) = LinearMap.piMap f := by
    apply LinearMap.ext
    intro x
    funext j
    change f j ((e.symm x) j) = f j (x j)
    rfl
  rw [←LinearMap.trace_conj' (DirectSum.lmap f) e, he, LinearMap.trace_piMap]

theorem tensorSchurRepresentation_rational (ell : ℕ) :
    TauCeti.IsRationalRep (tensorSchurRepresentation ell) := by
  change TauCeti.IsRationalRep (Representation.directSum
    (fun j : SchurCopyIndex ell ↦ schurRepresentation ℂ (ell-2*j.1.val) j.1.val))
  exact TauCeti.IsRationalRep.directSum
    (n := 2) (ι := SchurCopyIndex ell)
    (V := fun j : SchurCopyIndex ell ↦ SchurSpace ℂ (ell-2*j.1.val) j.1.val)
    (σ := fun j : SchurCopyIndex ell ↦ schurRepresentation ℂ (ell-2*j.1.val) j.1.val)
    (fun j : SchurCopyIndex ell ↦
      (schurRepresentation_polynomial (ell-2*j.1.val) j.1.val).isRationalRep)

theorem tensorSchurRepresentation_character (ell : ℕ) (t : Fin 2 → ℂˣ) :
    Representation.character (k := ℂ)
      (V := ⨁ j : SchurCopyIndex ell, SchurSpace ℂ (ell-2*j.1.val) j.1.val)
      (tensorSchurRepresentation ell) (TauCeti.diagGL t) =
      ((t 0 : ℂ)+(t 1 : ℂ))^ell := by
  change LinearMap.trace ℂ _ (DirectSum.lmap
    (fun j : SchurCopyIndex ell ↦
      schurRepresentation ℂ (ell-2*j.1.val) j.1.val (TauCeti.diagGL t))) = _
  rw [trace_lmap]
  change (∑ j : SchurCopyIndex ell,
    Representation.character (k := ℂ) (V := SchurSpace ℂ (ell-2*j.1.val) j.1.val)
      (schurRepresentation ℂ (ell-2*j.1.val) j.1.val) (TauCeti.diagGL t)) = _
  simp only [schurRepresentation_character, SchurCopyIndex, Fintype.sum_sigma,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (ballotMultiplicity ell j : ℂ)*
      schurValue (ell-2*j) j (t 0 : ℂ) (t 1 : ℂ)) (ell/2+1)]
  exact (tensor_power_schur_value ell (t 0 : ℂ) (t 1 : ℂ) (Units.ne_zero _)).symm

/-- Every length, including length zero: the genuine tensor-power
representation is equivalent to precisely the displayed symmetric powers
and determinant twists, with the full binomial-difference multiplicities. -/
theorem tensor_power_schur_decomposition (ell : ℕ) :
    Nonempty ((TauCeti.tensorPowerRep ℂ 2 ell).Equiv (tensorSchurRepresentation ell)) := by
  apply TauCeti.IsRationalRep.nonempty_equiv_of_forall_character_diagGL_eq
    (n := 2) (W := ⨂[ℂ]^ell (Fin 2 → ℂ))
    (W' := ⨁ j : SchurCopyIndex ell, SchurSpace ℂ (ell-2*j.1.val) j.1.val)
    (ρ := TauCeti.tensorPowerRep ℂ 2 ell) (σ := tensorSchurRepresentation ell)
    (TauCeti.isPolynomialRep_tensorPowerRep 2 ell).isRationalRep
    (tensorSchurRepresentation_rational ell)
  intro t
  rw [tensorSchurRepresentation_character, TauCeti.char_tensorPowerRep]
  congr 1
  simp only [Matrix.trace, Fin.sum_univ_two,Matrix.diag_apply, TauCeti.diagGL_apply, if_true]

end PaperVerification.Fermion.ColorSchur
