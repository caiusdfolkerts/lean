module

public import PaperVerification.AlternatingFormsPolynomialAction
import Lean.Elab.Tactic.Omega

/-!
# The graded Betti spaces for the actual polynomial action

The homology comparison in this file uses Mathlib's genuine derived tensor
functor.  The internal grading is induced from the homogeneous polynomial
Koszul resolution, whose two generators have degree two.  In particular the
three exterior terms carry shifts zero, two and four.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits

universe u

section GradingTransport

variable {K A B : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem finiteHilbertLaurent_map [FiniteDimensional K A] [FiniteDimensional K B]
    (G : TauCeti.InternalGrading K A) (e : A ≃ₗ[K] B) :
    finiteHilbertLaurent (G.map e) = finiteHilbertLaurent G := by
  ext q
  simp only [finiteHilbertLaurent_coeff]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    ((congrArg (fun S : Submodule K B ↦ Module.finrank K S)
      (TauCeti.InternalGrading.map_piece G e q)).trans (e.finrank_map_eq (G.piece q)))

/-- The unique grading on an actual zero vector space. -/
def zeroInternalGrading [Subsingleton A] : TauCeti.InternalGrading K A where
  piece := fun _ => ⊥
  isInternal := by
    constructor
    · intro x y _
      exact Subsingleton.elim x y
    · intro x
      exact ⟨0, Subsingleton.elim _ _⟩

end GradingTransport

section HomologyComparison

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

/-- Degree-zero categorical homology is the literal quotient by the image
of the first displayed exterior differential. -/
def exteriorHomologyZeroEquiv (f g : ⋀[K]^2 M) :
    (exteriorPairComplex f g).homology 0 ≃ₗ[K]
      (ExteriorAlgebra K M ⧸ LinearMap.range (exteriorKoszulFirst f g)) :=
  ((exteriorPairComplex f g).isoHomologyι₀ ≪≫
    (exteriorPairComplex f g).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
      ((exteriorPairComplex f g).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv

/-- The middle categorical homology is exactly kernel modulo image, with
the map to cycles induced by the actual second differential. -/
def exteriorHomologyOneEquiv (f g : ⋀[K]^2 M) :
    (exteriorPairComplex f g).homology 1 ≃ₗ[K]
      (LinearMap.ker (exteriorKoszulFirst f g) ⧸
        LinearMap.range (shortComplexToCycles (exteriorKoszulSecond f g)
          (exteriorKoszulFirst f g) (exteriorKoszul_comp f g))) :=
  ((exteriorPairComplex f g).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ((exteriorPairComplex f g).sc' 2 1 0).moduleCatHomologyIso).toLinearEquiv

/-- There is no incoming map in homological degree two.  Its actual
homology is therefore the actual common annihilator, before applying any
dimension or duality theorem. -/
def exteriorHomologyTwoEquiv (f g : ⋀[K]^2 M) :
    (exteriorPairComplex f g).homology 2 ≃ₗ[K] ExteriorKoszulTopKernel f g := by
  let e : (exteriorPairComplex f g).homology 2 ≅
      ModuleCat.of K (LinearMap.ker (exteriorKoszulSecond f g)) :=
    ((exteriorPairComplex f g).isoHomologyπ 3 2 (by simp)
      (by simp [exteriorPairComplex, pairComplex_d, pairDifferential] <;> rfl)).symm ≪≫
      (exteriorPairComplex f g).cyclesIsoSc' 3 2 1 (by simp) (by simp) ≪≫
        ((exteriorPairComplex f g).sc' 3 2 1).moduleCatCyclesIso
  exact e.toLinearEquiv.trans (LinearEquiv.ofEq _ _ (by
    simp only [ExteriorKoszulTopKernel, shortComplexToCycles, LinearMap.ker_codRestrict]))

def exteriorTorZeroEquiv (f g : ⋀[K]^2 M) :
    exteriorPolynomialTor f g 0 ≃ₗ[K]
      (ExteriorAlgebra K M ⧸ LinearMap.range (exteriorKoszulFirst f g)) :=
  (exteriorPolynomialTorIso f g 0).toLinearEquiv.trans (exteriorHomologyZeroEquiv f g)

def exteriorTorOneEquiv (f g : ⋀[K]^2 M) :
    exteriorPolynomialTor f g 1 ≃ₗ[K]
      (LinearMap.ker (exteriorKoszulFirst f g) ⧸
        LinearMap.range (shortComplexToCycles (exteriorKoszulSecond f g)
          (exteriorKoszulFirst f g) (exteriorKoszul_comp f g))) :=
  (exteriorPolynomialTorIso f g 1).toLinearEquiv.trans (exteriorHomologyOneEquiv f g)

def exteriorTorTwoEquiv (f g : ⋀[K]^2 M) :
    exteriorPolynomialTor f g 2 ≃ₗ[K] ExteriorKoszulTopKernel f g :=
  (exteriorPolynomialTorIso f g 2).toLinearEquiv.trans (exteriorHomologyTwoEquiv f g)

instance exteriorPolynomialTor_finite (f g : ⋀[K]^2 M) (i : ℕ) :
    FiniteDimensional K (exteriorPolynomialTor f g i) := by
  cases i with
  | zero => exact Module.Finite.equiv (exteriorTorZeroEquiv f g).symm
  | succ i =>
    cases i with
    | zero => exact Module.Finite.equiv (exteriorTorOneEquiv f g).symm
    | succ i =>
      cases i with
      | zero => exact Module.Finite.equiv (exteriorTorTwoEquiv f g).symm
      | succ i =>
        letI : Subsingleton (exteriorPolynomialTor f g (i + 3)) :=
          ModuleCat.subsingleton_of_isZero (exteriorPolynomialTor_isZero_above f g (by omega))
        infer_instance

/-- The grading on actual Tor, transported along the canonical comparison
from the homogeneous Koszul resolution.  The shifts are those of the
resolution, not shifts chosen to fit a Hilbert-series answer. -/
def exteriorTorGrading (f g : ⋀[K]^2 M) : (i : ℕ) →
    TauCeti.InternalGrading K (exteriorPolynomialTor f g i)
  | 0 => (exteriorKoszulH₀Grading f g).map (exteriorTorZeroEquiv f g).symm
  | 1 => (exteriorKoszulH₁Grading f g).map (exteriorTorOneEquiv f g).symm
  | 2 => (exteriorKoszulH₂Grading f g).map (exteriorTorTwoEquiv f g).symm
  | i + 3 => by
    letI : Subsingleton (exteriorPolynomialTor f g (i + 3)) :=
      ModuleCat.subsingleton_of_isZero (exteriorPolynomialTor_isZero_above f g (by omega))
    exact zeroInternalGrading

/-- The Betti polynomial is the Hilbert series of the actual graded derived
tensor vector space, with the residue field at the origin of `K[u,v]`. -/
def exteriorBettiPolynomial (f g : ⋀[K]^2 M) (i : ℕ) : LaurentPolynomial ℤ :=
  finiteHilbertLaurent (exteriorTorGrading f g i)

@[simp] theorem exteriorBettiPolynomial_zero (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 0 = finiteHilbertLaurent (exteriorKoszulH₀Grading f g) :=
  finiteHilbertLaurent_map _ _

set_option maxHeartbeats 1000000 in
@[simp] theorem exteriorBettiPolynomial_one (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 1 = finiteHilbertLaurent (exteriorKoszulH₁Grading f g) :=
  finiteHilbertLaurent_map _ _

set_option maxHeartbeats 1000000 in
@[simp] theorem exteriorBettiPolynomial_two (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 2 = finiteHilbertLaurent (exteriorKoszulH₂Grading f g) :=
  finiteHilbertLaurent_map _ _

theorem exteriorBettiPolynomial_above (f g : ⋀[K]^2 M) {i : ℕ} (hi : 2 < i) :
    exteriorBettiPolynomial f g i = 0 := by
  have hi' : i = (i - 3) + 3 := by omega
  rw [hi']
  ext q
  simp only [exteriorBettiPolynomial, exteriorTorGrading, zeroInternalGrading,
    finiteHilbertLaurent_coeff, finrank_bot, Nat.cast_zero, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] <;> rfl

/-- Proposition 5.4: all graded Betti polynomials, for an arbitrary pair of
exterior two-forms and with no genericity, nondegeneracy, or rank assumption.

`exteriorPolynomialTor` is Mathlib's derived tensor, the polynomial action
is actual multiplication by the two forms, and the residue module is proved
isomorphic to the coefficient field.  The exact comparison with the
homogeneous free Koszul resolution supplies `exteriorTorGrading`.
-/
theorem paper_proposition_5_4 (f g : ⋀[K]^2 M) :
    exteriorBettiPolynomial f g 0 = exteriorQuotientHilbert f g ∧
    exteriorBettiPolynomial f g 2 =
      LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
        LaurentPolynomial.invert (exteriorQuotientHilbert f g) ∧
    exteriorBettiPolynomial f g 1 =
      exteriorQuotientHilbert f g +
        LaurentPolynomial.T ((Module.finrank K M : ℤ) + 4) *
          LaurentPolynomial.invert (exteriorQuotientHilbert f g) -
        (1 - LaurentPolynomial.T 2) ^ 2 *
          (1 + LaurentPolynomial.T 1) ^ Module.finrank K M ∧
    ∀ i : ℕ, 2 < i → IsZero (exteriorPolynomialTor f g i) ∧
      exteriorBettiPolynomial f g i = 0 := by
  obtain ⟨h₀, h₂, h₁⟩ := exteriorKoszul_all_hilbert_formulas f g
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [exteriorBettiPolynomial_zero] using h₀
  · simpa only [exteriorBettiPolynomial_two] using h₂
  · simpa only [exteriorBettiPolynomial_one] using h₁
  · intro i hi
    exact ⟨exteriorPolynomialTor_isZero_above f g hi,
      exteriorBettiPolynomial_above f g hi⟩

end HomologyComparison

end PaperVerification.AlternatingForms
