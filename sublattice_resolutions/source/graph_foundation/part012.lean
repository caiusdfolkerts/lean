module
public import graph_foundation.part011

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesBasis -/
section

/-! # Coordinates on the actual Rees algebra of an arbitrary ideal

The coefficient of auxiliary degree `s` belongs to the actual ideal `J^s`.
The algebra below is identified with Mathlib's usual Rees subalgebra of
`S[t]`; its basis is obtained from the proved triangular ideal bases.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped BigOperators

variable {K V : Type*} [CommRing K]
  (J : Ideal (MvPolynomial V K))

abbrev idealPowerPiece (s : ℕ) : Submodule K (MvPolynomial V K) :=
  (J ^ s).restrictScalars K

/-- The native ideal module and its scalar-restricted presentation have
the same elements and the same coefficient scalar action. -/
def idealScalarRestrictionEquiv : J ≃ₗ[K] J.restrictScalars K where
  toFun f := ⟨f.val,f.property⟩
  invFun f := ⟨f.val,f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem idealScalarRestrictionEquiv_val (f : J) :
    (idealScalarRestrictionEquiv J f).val=f.val := rfl

@[simp] theorem idealScalarRestrictionEquiv_symm_val (f : J.restrictScalars K) :
    ((idealScalarRestrictionEquiv J).symm f).val=f.val := rfl

theorem idealPowerPiece_one : (1 : MvPolynomial V K) ∈ idealPowerPiece J 0 := by
  simp [idealPowerPiece]

theorem idealPowerPiece_mul (s t : ℕ)
    (f : MvPolynomial V K) (hf : f ∈ idealPowerPiece J s)
    (g : MvPolynomial V K) (hg : g ∈ idealPowerPiece J t) :
    f * g ∈ idealPowerPiece J (s + t) := by
  change f * g ∈ J ^ (s + t)
  rw [pow_add]
  exact Ideal.mul_mem_mul hf hg

/-- Finite coefficient lists with coefficient `s` in `J^s`, and literal
convolution multiplication. -/
abbrev coefficientRees :=
  gradedCoefficientAlgebra (idealPowerPiece J)
    (idealPowerPiece_one J) (idealPowerPiece_mul J)

instance (priority := 1200) coefficientReesRing : Ring (coefficientRees J) :=
  Subalgebra.toRing (coefficientRees J)

instance (priority := 1200) coefficientReesAlgebra : Algebra K (coefficientRees J) :=
  Subalgebra.algebra (coefficientRees J)

/-- The coordinate construction is exactly the conventional Rees algebra,
including its multiplication and coefficient-ring action. -/
def coefficientReesPolynomialEquiv :
    coefficientRees J ≃ₐ[K] (reesAlgebra J).restrictScalars K where
  toFun x := ⟨Polynomial.ofFinsupp x.val, x.property⟩
  invFun x := ⟨x.val.toFinsupp, x.property⟩
  left_inv _ := rfl
  right_inv x := Subtype.ext (Polynomial.eta x.val)
  map_add' _ _ := Subtype.ext Polynomial.ofFinsupp_add
  map_mul' x y := Subtype.ext (Polynomial.ofFinsupp_mul x.val y.val)
  commutes' r := Subtype.ext (Polynomial.ofFinsupp_algebraMap r)

@[simp] theorem coefficientReesPolynomialEquiv_coeff
    (x : coefficientRees J) (s : ℕ) :
    (coefficientReesPolynomialEquiv J x).val.coeff s = x.val.coeff s := rfl

def idealReesSingle (s : ℕ) : idealPowerPiece J s →ₗ[K] coefficientRees J :=
  coefficientSingle (idealPowerPiece J) (idealPowerPiece_one J) (idealPowerPiece_mul J) s

@[simp] theorem idealReesSingle_polynomial (s : ℕ) (f : idealPowerPiece J s) :
    (coefficientReesPolynomialEquiv J (idealReesSingle J s f)).val =
      Polynomial.monomial s f.val :=
  Polynomial.ofFinsupp_single s f.val

section ChangeOfVariables

variable {W : Type*} (I : Ideal (MvPolynomial W K))
  (e : MvPolynomial V K ≃ₐ[K] MvPolynomial W K)
  (hJI : Ideal.map e.toRingHom J = I)

include hJI in
theorem coefficientRees_map :
    (coefficientRees J).map (AddMonoidAlgebra.mapAlgEquiv K ℕ e).toAlgHom =
      coefficientRees I := by
  have hp (s : ℕ) : Ideal.map e.toRingHom (J ^ s) = I ^ s := by
    rw [Ideal.map_pow, hJI]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩ s
    change e (y.coeff s) ∈ I ^ s
    rw [← hp]
    exact Ideal.mem_map_of_mem e.toRingHom (hy s)
  · intro x hx
    let y := AddMonoidAlgebra.mapAlgEquiv K ℕ e.symm x
    have hy : y ∈ coefficientRees J := by
      intro s
      change e.symm (x.coeff s) ∈ J ^ s
      apply (Ideal.apply_mem_of_equiv_iff (f := e.toRingEquiv)).mp
      change e (e.symm (x.coeff s)) ∈ Ideal.map e.toRingHom (J ^ s)
      rw [hp]
      have hs := hx s
      change x.coeff s ∈ I ^ s at hs
      simpa only [AlgEquiv.apply_symm_apply] using hs
    refine ⟨y, hy, ?_⟩
    exact (AddMonoidAlgebra.mapAlgEquiv K ℕ e).apply_symm_apply x

/-- Renaming the polynomial coefficient ring induces an actual algebra
equivalence of Rees algebras and preserves every auxiliary coefficient. -/
def coefficientReesCongr : coefficientRees J ≃ₐ[K] coefficientRees I :=
  ((AddMonoidAlgebra.mapAlgEquiv K ℕ e).subalgebraMap (coefficientRees J)).trans
    (Subalgebra.equivOfEq _ _ (coefficientRees_map J I e hJI))

@[simp] theorem coefficientReesCongr_coeff (x : coefficientRees J) (s : ℕ) :
    (coefficientReesCongr J I e hJI x).val.coeff s = e (x.val.coeff s) := rfl

end ChangeOfVariables

variable [Nontrivial K] (m : MonomialOrder V)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev GroebnerReesIndex := Σ s : ℕ, NonstandardIndex m (J ^ s)

/-- The triangular ideal basis, transported by the literal identity on
polynomials to the coefficient module used in the Rees algebra. -/
def groebnerPowerBasis (s : ℕ) :
    Module.Basis (NonstandardIndex m (J ^ s)) K (idealPowerPiece J s) :=
  (groebnerIdealBasis m (J ^ s) (G s) (hG s) (hu s)).map
    (idealScalarRestrictionEquiv (J ^ s))

@[simp] theorem groebnerPowerBasis_apply (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    groebnerPowerBasis J m G hG hu s a =
      idealScalarRestrictionEquiv (J ^ s)
        (idealLift m (J ^ s) (G s) (hG s) (hu s) a) := by
  rw [groebnerPowerBasis,Module.Basis.map_apply,groebnerIdealBasis_apply]

theorem groebnerPowerBasis_repr (s : ℕ) (f : idealPowerPiece J s)
    (a : NonstandardIndex m (J ^ s)) :
    (groebnerPowerBasis J m G hG hu s).repr f a=f.val.coeff a.val := by
  rw [groebnerPowerBasis,Module.Basis.map_repr,LinearEquiv.trans_apply,
    groebnerIdealBasis_repr,idealScalarRestrictionEquiv_symm_val]

/-- No quotient or flatness assertion enters this basis: it is a basis of
the actual coefficientwise Rees subalgebra. -/
def groebnerReesBasis : Module.Basis (GroebnerReesIndex J m) K (coefficientRees J) :=
  gradedCoefficientBasis (idealPowerPiece J)
    (idealPowerPiece_one J) (idealPowerPiece_mul J)
    (groebnerPowerBasis J m G hG hu)

theorem groebnerReesBasis_apply (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    groebnerReesBasis J m G hG hu ⟨s, a⟩ =
      idealReesSingle J s (idealLift m (J ^ s) (G s) (hG s) (hu s) a) := by
  rw [groebnerReesBasis, gradedCoefficientBasis_apply, groebnerPowerBasis_apply] <;> rfl

theorem groebnerReesBasis_repr (x : coefficientRees J) (s : ℕ)
    (a : NonstandardIndex m (J ^ s)) :
    (groebnerReesBasis J m G hG hu).repr x ⟨s, a⟩ =
      (x.val.coeff s).coeff a.val := by
  rw [groebnerReesBasis, gradedCoefficientBasis_repr, groebnerPowerBasis_repr] <;> rfl

theorem groebnerReesBasis_polynomial (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    (coefficientReesPolynomialEquiv J (groebnerReesBasis J m G hG hu ⟨s, a⟩)).val =
      Polynomial.monomial s
        (monomial a.val 1 - (hG s).normalForm (hu s) (monomial a.val 1)) := by
  rw [groebnerReesBasis_apply, idealReesSingle_polynomial] <;> rfl

abbrev InitialReesIndex := Σ s : ℕ,
  {a : V →₀ ℕ // monomial a (1 : K) ∈
    Ideal.span (m.leadingTerm '' (↑(J ^ s) : Set (MvPolynomial V K)))}

def groebnerInitialReesIndexEquiv : GroebnerReesIndex J m ≃ InitialReesIndex J m :=
  Equiv.sigmaCongrRight
    (fun s => nonstandardInitialIndexEquiv m (J ^ s) (G s) (hG s) (hu s))

def initialIndexedReesBasis :
    Module.Basis (InitialReesIndex J m) K (coefficientRees J) :=
  (groebnerReesBasis J m G hG hu).reindex (groebnerInitialReesIndexEquiv J m G hG hu)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialReesBasis -/
section

/-! # A common basis index for the original and initial Rees algebras -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial

variable {K V : Type*} [CommRing K] [Nontrivial K]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

/-- The actual initial ideal in degree `s` is the target power. This
equivalence retains each polynomial and explicitly compares its scalar actions. -/
def initialPowerCoefficientEquiv (s : ℕ) :
    initialIdealForBasis m (J ^ s) ≃ₗ[K] idealPowerPiece I s where
  toFun f := ⟨f.val,by
    change f.val ∈ I ^ s
    rw [← hinit s]
    exact f.property⟩
  invFun f := ⟨f.val,by
    change f.val ∈ initialIdealForBasis m (J ^ s)
    rw [hinit s]
    exact f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem initialPowerCoefficientEquiv_val (s : ℕ)
    (f : initialIdealForBasis m (J ^ s)) :
    (initialPowerCoefficientEquiv m J I hinit s f).val=f.val := rfl

@[simp] theorem initialPowerCoefficientEquiv_symm_val (s : ℕ)
    (f : idealPowerPiece I s) :
    ((initialPowerCoefficientEquiv m J I hinit s).symm f).val=f.val := rfl

def initialPowerBasis (s : ℕ) :
    Module.Basis (NonstandardIndex m (J ^ s)) K (idealPowerPiece I s) :=
  (initialIdealBasis m (J ^ s) (G s) (hG s) (hu s)).map
    (initialPowerCoefficientEquiv m J I hinit s)

@[simp] theorem initialPowerBasis_val (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    (initialPowerBasis m J I hinit G hG hu s a).val = monomial a.val (1 : K) := by
  rw [initialPowerBasis, Module.Basis.map_apply, initialPowerCoefficientEquiv_val,
    initialIdealBasis_apply] <;> rfl

theorem initialPowerBasis_repr (s : ℕ) (f : idealPowerPiece I s)
    (a : NonstandardIndex m (J ^ s)) :
    (initialPowerBasis m J I hinit G hG hu s).repr f a = f.val.coeff a.val := by
  rw [initialPowerBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    initialIdealBasis_repr, initialPowerCoefficientEquiv_symm_val]

def initialReesBasis : Module.Basis (GroebnerReesIndex J m) K (coefficientRees I) :=
  gradedCoefficientBasis (idealPowerPiece I) (idealPowerPiece_one I) (idealPowerPiece_mul I)
    (initialPowerBasis m J I hinit G hG hu)

@[simp] theorem initialReesBasis_apply (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    initialReesBasis m J I hinit G hG hu ⟨s, a⟩ =
      idealReesSingle I s (initialPowerBasis m J I hinit G hG hu s a) := by
  rw [initialReesBasis, gradedCoefficientBasis_apply] <;> rfl

theorem initialReesBasis_val (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    (initialReesBasis m J I hinit G hG hu ⟨s, a⟩).val =
      AddMonoidAlgebra.single s (monomial a.val (1 : K)) := by
  rw [initialReesBasis_apply, idealReesSingle, coefficientSingle_val, initialPowerBasis_val]

theorem initialReesBasis_repr (x : coefficientRees I) (s : ℕ)
    (a : NonstandardIndex m (J ^ s)) :
    (initialReesBasis m J I hinit G hG hu).repr x ⟨s, a⟩ =
      (x.val.coeff s).coeff a.val := by
  rw [initialReesBasis, gradedCoefficientBasis_repr, initialPowerBasis_repr]
  rfl

/-- The genuine coefficient modules of all powers are compared by the
proved triangular bases. This is a module equivalence, not an assertion
that the original Rees algebra and its initial algebra are isomorphic. -/
def reesInitialLinearEquiv : coefficientRees J ≃ₗ[K] coefficientRees I :=
  (groebnerReesBasis J m G hG hu).repr.trans (initialReesBasis m J I hinit G hG hu).repr.symm

@[simp] theorem reesInitialLinearEquiv_basis (a : GroebnerReesIndex J m) :
    reesInitialLinearEquiv m J I hinit G hG hu (groebnerReesBasis J m G hG hu a) =
      initialReesBasis m J I hinit G hG hu a := by
  simp only [reesInitialLinearEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Module.Basis.repr_symm_single_one]

theorem reesInitialLinearEquiv_repr (x : coefficientRees J) (a : GroebnerReesIndex J m) :
    (initialReesBasis m J I hinit G hG hu).repr
      (reesInitialLinearEquiv m J I hinit G hG hu x) a =
      (groebnerReesBasis J m G hG hu).repr x a := by
  rw [reesInitialLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

def initialReesIndexAdd (a b : GroebnerReesIndex J m) : GroebnerReesIndex J m :=
  ⟨a.1 + b.1, ⟨a.2.val + b.2.val, by
    apply (monomial_mem_initial_iff_not_standard m (J ^ (a.1 + b.1))
      (G (a.1 + b.1)) (hG (a.1 + b.1)) (hu (a.1 + b.1)) _).mp
    change monomial (a.2.val+b.2.val) (1 : K) ∈ initialIdealForBasis m (J ^ (a.1+b.1))
    rw [hinit (a.1 + b.1), pow_add]
    have ha := (initialPowerBasis m J I hinit G hG hu a.1 a.2).property
    have hb := (initialPowerBasis m J I hinit G hG hu b.1 b.2).property
    change (initialPowerBasis m J I hinit G hG hu a.1 a.2).val ∈ I ^ a.1 at ha
    change (initialPowerBasis m J I hinit G hG hu b.1 b.2).val ∈ I ^ b.1 at hb
    rw [initialPowerBasis_val] at ha hb
    simpa only [monomial_mul_monomial, one_mul] using Ideal.mul_mem_mul ha hb⟩⟩

theorem initialReesBasis_mul (a b : GroebnerReesIndex J m) :
    initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b =
      initialReesBasis m J I hinit G hG hu (initialReesIndexAdd m J I hinit G hG hu a b) := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, initialReesBasis_val, initialReesBasis_val, initialReesBasis_val,
    AddMonoidAlgebra.single_mul_single, monomial_mul_monomial, one_mul] <;> rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ParityHomologyMap -/
section

/-! # Maps and quotients of actual parity differential algebras

The induced homology maps below are maps of the literal cycles modulo literal
boundaries. Generation is therefore an algebraic statement about genuine
homology classes.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.ParityDifferential

variable {K A B : Type*} [CommRing K] [Ring A] [Ring B]
  [Algebra K A] [Algebra K B]

variable (D : ParityDifferential K A) (E : ParityDifferential K B)
  (f : A →ₐ[K] B) (hcomm : ∀ x, E.d (f x) = f (D.d x))

def cyclesMap : D.cycles →ₐ[K] E.cycles :=
  (f.comp D.cycles.val).codRestrict E.cycles (by
    intro x
    change E.d (f x.val) = 0
    rw [hcomm, x.property, map_zero])

def homologyMap : D.Homology →ₐ[K] E.Homology :=
  Ideal.Quotient.liftₐ D.boundaries.asIdeal
    (E.classMap.comp (cyclesMap D E f hcomm)) (by
      intro x hx
      apply (E.classMap_eq_zero _).mpr
      have hx' : x ∈ D.boundaries := TwoSidedIdeal.mem_asIdeal.mp hx
      obtain ⟨a, ha⟩ := (D.mem_boundaries x).mp hx'
      refine ⟨f a, ?_⟩
      change E.d (f a) = f x.val
      rw [hcomm, ha])

@[simp] theorem homologyMap_classMap (x : D.cycles) :
    homologyMap D E f hcomm (D.classMap x) =
      E.classMap (cyclesMap D E f hcomm x) := rfl

theorem homologyMap_surjective_of_generators (G : Set E.Homology)
    (hgen : Algebra.adjoin K G = ⊤)
    (hlift : G ⊆ Set.range (homologyMap D E f hcomm)) :
    Function.Surjective (homologyMap D E f hcomm) := by
  have hr : (⊤ : Subalgebra K E.Homology) ≤ (homologyMap D E f hcomm).range := by
    rw [← hgen]
    exact Algebra.adjoin_le hlift
  intro y
  exact hr (show y ∈ (⊤ : Subalgebra K E.Homology) from trivial)

/-- A class lift can be corrected by an actual boundary when the algebra map
is onto. The result is a cycle with exactly the requested image. -/
theorem strictCyclesLift_of_homologyMap_surjective
    (hf : Function.Surjective f)
    (hH : Function.Surjective (homologyMap D E f hcomm)) :
    ∀ y : B, E.d y = 0 → ∃ x : A, D.d x = 0 ∧ f x = y := by
  intro y hy
  obtain ⟨u, hu⟩ := hH (E.classMap ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := D.classMap_surjective u
  rw [homologyMap_classMap] at hu
  obtain ⟨v, hv⟩ := (E.classMap_eq_iff _ _).mp hu
  obtain ⟨w, rfl⟩ := hf v
  refine ⟨x.val - D.d w, ?_, ?_⟩
  · rw [map_sub, x.property, D.square_zero, sub_self]
  · change E.d (f w) = f x.val - y at hv
    rw [map_sub, ← hcomm, hv]
    abel

theorem strictCyclesLift_of_generators
    (hf : Function.Surjective f) (G : Set E.Homology)
    (hgen : Algebra.adjoin K G = ⊤)
    (hlift : G ⊆ Set.range (homologyMap D E f hcomm)) :
    ∀ y : B, E.d y = 0 → ∃ x : A, D.d x = 0 ∧ f x = y :=
  strictCyclesLift_of_homologyMap_surjective D E f hcomm hf
    (homologyMap_surjective_of_generators D E f hcomm G hgen hlift)

section Quotient

variable (I : TwoSidedIdeal A)
  (hd : ∀ x ∈ I, D.d x ∈ I) (hp : ∀ x ∈ I, D.parity x ∈ I)

def quotientDifferential : (A ⧸ I.asIdeal) →ₗ[K] (A ⧸ I.asIdeal) :=
  Submodule.mapQ (I.asIdeal.restrictScalars K) (I.asIdeal.restrictScalars K) D.d
    (by intro x hx; exact hd x hx)

def quotientParity : (A ⧸ I.asIdeal) →ₐ[K] (A ⧸ I.asIdeal) :=
  Ideal.Quotient.liftₐ I.asIdeal ((Ideal.Quotient.mkₐ K I.asIdeal).comp D.parity)
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact hp x hx)

def quotient : ParityDifferential K (A ⧸ I.asIdeal) where
  d := D.quotientDifferential I hd
  parity := D.quotientParity I hp
  square_zero x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I.asIdeal (D.d (D.d x)) = 0
    rw [D.square_zero, map_zero]
  parity_square x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I.asIdeal (D.parity (D.parity x)) =
      Ideal.Quotient.mk I.asIdeal x
    rw [D.parity_square]
  anticommute x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I.asIdeal (D.d (D.parity x)) =
      -Ideal.Quotient.mk I.asIdeal (D.parity (D.d x))
    rw [D.anticommute, map_neg]
  map_one := by
    change Ideal.Quotient.mk I.asIdeal (D.d 1) = 0
    rw [D.map_one, map_zero]
  leibniz x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I.asIdeal (D.d (x * y)) =
      Ideal.Quotient.mk I.asIdeal (D.d x) * Ideal.Quotient.mk I.asIdeal y +
      Ideal.Quotient.mk I.asIdeal (D.parity x) * Ideal.Quotient.mk I.asIdeal (D.d y)
    rw [D.leibniz, map_add, map_mul, map_mul]

@[simp] theorem quotient_d_mk (x : A) :
    (D.quotient I hd hp).d (Ideal.Quotient.mk I.asIdeal x) =
      Ideal.Quotient.mk I.asIdeal (D.d x) := rfl

end Quotient
end FourPapers.ParityDifferential

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.WellOrderedFilteredRees -/
section

/-! # Actual Rees algebras for well-ordered monomial filtrations

Term orders need not be representable by one integer weight on all monomials.
This construction uses their ordered additive monoid directly. The strict
filtration step consists of zero and the elements in a strictly earlier step;
linearity follows because the index order is total.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.WellOrderedFiltered

open Classical

variable (K A Γ : Type*) [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

structure MultiplicativeFiltration where
  level : Γ → Submodule K A
  mono : Monotone level
  exhaustive : ∀ x : A, ∃ n, x ∈ level n
  one_mem : (1 : A) ∈ level 0
  mul_mem : ∀ a b, ∀ x ∈ level a, ∀ y ∈ level b, x * y ∈ level (a + b)

namespace MultiplicativeFiltration

variable {K A Γ} (F : MultiplicativeFiltration K A Γ)

def lower (n : Γ) : Submodule K A where
  carrier := {x | x = 0 ∨ ∃ m < n, x ∈ F.level m}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | ⟨a, ha, hx⟩) (rfl | ⟨b, hb, hy⟩)
    · exact Or.inl (zero_add 0)
    · exact Or.inr ⟨b, hb, by simpa only [zero_add] using hy⟩
    · exact Or.inr ⟨a, ha, by simpa only [add_zero] using hx⟩
    · exact Or.inr ⟨max a b, max_lt ha hb,
        (F.level (max a b)).add_mem (F.mono (le_max_left a b) hx)
          (F.mono (le_max_right a b) hy)⟩
  smul_mem' := by
    rintro r x (rfl | ⟨a, ha, hx⟩)
    · exact Or.inl (smul_zero r)
    · exact Or.inr ⟨a, ha, (F.level a).smul_mem r hx⟩

@[simp] theorem mem_lower (n : Γ) (x : A) :
    x ∈ F.lower n ↔ x = 0 ∨ ∃ m < n, x ∈ F.level m := Iff.rfl

theorem lower_le (n : Γ) : F.lower n ≤ F.level n := by
  rintro x (rfl | ⟨m, hm, hx⟩)
  · exact (F.level n).zero_mem
  · exact F.mono hm.le hx

theorem lower_mono : Monotone F.lower := by
  intro a b hab x hx
  rcases hx with rfl | ⟨m, hm, hx⟩
  · exact (F.lower b).zero_mem
  · exact Or.inr ⟨m, hm.trans_le hab, hx⟩

theorem mul_mem_lower (a b : Γ) (x y : A)
    (hx : x ∈ F.level a) (hy : y ∈ F.lower b) : x * y ∈ F.lower (a + b) := by
  rcases hy with rfl | ⟨c, hc, hy⟩
  · exact Or.inl (mul_zero x)
  · exact Or.inr ⟨a + c, add_lt_add_right hc a, F.mul_mem a c x hx y hy⟩

theorem lower_mul_mem (a b : Γ) (x y : A)
    (hx : x ∈ F.lower a) (hy : y ∈ F.level b) : x * y ∈ F.lower (a + b) := by
  rcases hx with rfl | ⟨c, hc, hx⟩
  · exact Or.inl (zero_mul y)
  · exact Or.inr ⟨c + b, add_lt_add_left hc b, F.mul_mem c b x hx y hy⟩

abbrev rees : Subalgebra K (AddMonoidAlgebra A Γ) :=
  gradedCoefficientAlgebra F.level F.one_mem F.mul_mem

instance (priority := 1200) reesRing : Ring F.rees := Subalgebra.toRing F.rees
instance (priority := 1200) reesAlgebra : Algebra K F.rees := Subalgebra.algebra F.rees

def monomial (n : Γ) : F.level n →ₗ[K] F.rees :=
  coefficientSingle F.level F.one_mem F.mul_mem n

@[simp] theorem monomial_coeff (n i : Γ) (a : F.level n) :
    (F.monomial n a).val.coeff i = if n = i then a.val else 0 := by
  have hh := coefficientSingle_coeff F.level F.one_mem F.mul_mem n i a
  split_ifs at hh ⊢ <;> exact hh

def strictIdeal : TwoSidedIdeal F.rees :=
  TwoSidedIdeal.mk' {p : F.rees | ∀ n, p.val.coeff n ∈ F.lower n}
    (by intro n; exact (F.lower n).zero_mem)
    (by intro p q hp hq n; exact (F.lower n).add_mem (hp n) (hq n))
    (by intro p hp n; exact (F.lower n).neg_mem (hp n))
    (by
      intro p q hq n
      change (p.val * q.val).coeff n ∈ F.lower n
      rw [AddMonoidAlgebra.coeff_mul]
      apply Submodule.sum_mem
      intro a _
      apply Submodule.sum_mem
      intro b _
      dsimp only
      split_ifs with hab
      · subst n
        exact F.mul_mem_lower a b _ _ (p.property a) (hq b)
      · exact (F.lower n).zero_mem)
    (by
      intro p q hp n
      change (p.val * q.val).coeff n ∈ F.lower n
      rw [AddMonoidAlgebra.coeff_mul]
      apply Submodule.sum_mem
      intro a _
      apply Submodule.sum_mem
      intro b _
      dsimp only
      split_ifs with hab
      · subst n
        exact F.lower_mul_mem a b _ _ (hp a) (q.property b)
      · exact (F.lower n).zero_mem)

@[simp] theorem mem_strictIdeal (p : F.rees) :
    p ∈ F.strictIdeal ↔ ∀ n, p.val.coeff n ∈ F.lower n :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _

abbrev AssociatedGraded := F.rees ⧸ F.strictIdeal.asIdeal

instance (priority := 1200) associatedGradedRing : Ring F.AssociatedGraded :=
  Ideal.Quotient.ring F.strictIdeal.asIdeal
instance (priority := 1200) associatedGradedAlgebra : Algebra K F.AssociatedGraded :=
  Ideal.Quotient.algebra K (A := F.rees) (I := F.strictIdeal.asIdeal)

def leadingMap : F.rees →ₐ[K] F.AssociatedGraded :=
  Ideal.Quotient.mkₐ K F.strictIdeal.asIdeal

theorem leadingMap_surjective : Function.Surjective F.leadingMap :=
  Ideal.Quotient.mk_surjective

@[simp] theorem leadingMap_eq_zero (p : F.rees) :
    F.leadingMap p = 0 ↔ ∀ n, p.val.coeff n ∈ F.lower n := by
  change Ideal.Quotient.mk F.strictIdeal.asIdeal p = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.mem_asIdeal, F.mem_strictIdeal]

variable (D : ParityDifferential K A)
  (hd : ∀ n x, x ∈ F.level n → D.d x ∈ F.level n)
  (hp : ∀ n x, x ∈ F.level n → D.parity x ∈ F.level n)

def reesDGA : ParityDifferential K F.rees :=
  (D.onMonoidAlgebra (Γ := Γ)).restrict F.rees
    (by intro p h n; exact hd n (p.coeff n) (h n))
    (by intro p h n; exact hp n (p.coeff n) (h n))

@[simp] theorem reesDGA_d_coeff (p : F.rees) (n : Γ) :
    ((F.reesDGA D hd hp).d p).val.coeff n = D.d (p.val.coeff n) := rfl

theorem reesDGA_d_monomial (n : Γ) (a : F.level n) :
    (F.reesDGA D hd hp).d (F.monomial n a) =
      F.monomial n ⟨D.d a.val, hd n a.val a.property⟩ := by
  apply Subtype.ext
  ext i
  rw [F.reesDGA_d_coeff, F.monomial_coeff, F.monomial_coeff]
  split_ifs
  · rfl
  · exact map_zero D.d

include hd in
theorem differential_lower (n : Γ) (x : A) (hx : x ∈ F.lower n) :
    D.d x ∈ F.lower n := by
  rcases hx with rfl | ⟨m, hm, hx⟩
  · exact Or.inl (map_zero D.d)
  · exact Or.inr ⟨m, hm, hd m x hx⟩

include hp in
theorem parity_lower (n : Γ) (x : A) (hx : x ∈ F.lower n) :
    D.parity x ∈ F.lower n := by
  rcases hx with rfl | ⟨m, hm, hx⟩
  · exact Or.inl (map_zero D.parity)
  · exact Or.inr ⟨m, hm, hp m x hx⟩

def associatedDGA : ParityDifferential K F.AssociatedGraded :=
  (F.reesDGA D hd hp).quotient F.strictIdeal
    (by
      intro p h
      rw [F.mem_strictIdeal] at h ⊢
      intro n
      change D.d (p.val.coeff n)∈F.lower n
      exact F.differential_lower D hd n _ (h n))
    (by
      intro p h
      rw [F.mem_strictIdeal] at h ⊢
      intro n
      change D.parity (p.val.coeff n)∈F.lower n
      exact F.parity_lower D hp n _ (h n))

@[simp] theorem leadingMap_intertwines (p : F.rees) :
    (F.associatedDGA D hd hp).d (F.leadingMap p) =
      F.leadingMap ((F.reesDGA D hd hp).d p) := rfl

def homologySpecialization :
    (F.reesDGA D hd hp).Homology →ₐ[K] (F.associatedDGA D hd hp).Homology :=
  ParityDifferential.homologyMap (K := K) (F.reesDGA D hd hp) (F.associatedDGA D hd hp)
    F.leadingMap (F.leadingMap_intertwines D hd hp)

def LiftsCycles : Prop :=
  ∀ n (x : A), x ∈ F.level n → D.d x ∈ F.lower n →
    ∃ z, z ∈ F.level n ∧ D.d z = 0 ∧ x - z ∈ F.lower n

theorem liftsCycles_of_homologySpecialization_surjective
    (hH : Function.Surjective (F.homologySpecialization D hd hp)) :
    F.LiftsCycles D := by
  have hlift := ParityDifferential.strictCyclesLift_of_homologyMap_surjective (K := K)
    (F.reesDGA D hd hp) (F.associatedDGA D hd hp) F.leadingMap
    (F.leadingMap_intertwines D hd hp) F.leadingMap_surjective hH
  intro n x hx hdx
  let r := F.monomial n ⟨x, hx⟩
  have hr : (F.associatedDGA D hd hp).d (F.leadingMap r) = 0 := by
    rw [F.leadingMap_intertwines, F.leadingMap_eq_zero]
    intro i
    rw [F.reesDGA_d_coeff, F.monomial_coeff]
    split_ifs with hi
    · subst i; exact hdx
    · rw [map_zero]; exact (F.lower i).zero_mem
  obtain ⟨q, hq, he⟩ := hlift (F.leadingMap r) hr
  refine ⟨q.val.coeff n, q.property n, ?_, ?_⟩
  · exact congrArg (fun p : F.rees => p.val.coeff n) hq
  · have hz : F.leadingMap (r - q) = 0 := by rw [map_sub, he, sub_self]
    have hh := (F.leadingMap_eq_zero (r - q)).mp hz n
    change r.val.coeff n - q.val.coeff n ∈ F.lower n at hh
    simpa [r, F.monomial_coeff] using hh

theorem liftsCycles_of_generators
    (G : Set (F.associatedDGA D hd hp).Homology)
    (hgen : Algebra.adjoin K G = ⊤)
    (hlift : G ⊆ Set.range (F.homologySpecialization D hd hp)) :
    F.LiftsCycles D :=
  F.liftsCycles_of_homologySpecialization_surjective D hd hp
    (ParityDifferential.homologyMap_surjective_of_generators (K := K)
      (F.reesDGA D hd hp) (F.associatedDGA D hd hp) F.leadingMap
      (F.leadingMap_intertwines D hd hp) G hgen hlift)

end MultiplicativeFiltration
end FourPapers.WellOrderedFiltered

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesFiltration -/
section

/-! # The original term-order filtration on the actual Rees algebra

An element is bounded by `γ` when every polynomial coefficient in its Rees
expansion is bounded by `γ` in the given term order. This filtration is
defined on the actual coefficient algebra and is proved multiplicative.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped BigOperators

variable {K V : Type*} [CommRing K]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))

theorem mem_monomialOrderBound_iff (f : MvPolynomial V K) (n : m.syn) :
    f ∈ monomialOrderBound m n ↔ m.toSyn (m.degree f) ≤ n := by
  change (∀ a ∈ f.support, m.toSyn a ≤ n) ↔ _
  simpa only [m.toSyn.apply_symm_apply] using
    (m.degree_le_iff (f := f) (d := m.toSyn.symm n)).symm

theorem monomialOrderBound_mono : Monotone (monomialOrderBound (K := K) m) := by
  intro a b hab f hf
  exact (mem_monomialOrderBound_iff m f b).mpr
    (((mem_monomialOrderBound_iff m f a).mp hf).trans hab)

theorem monomialOrderBound_mul (a b : m.syn)
    (f : MvPolynomial V K) (hf : f ∈ monomialOrderBound m a)
    (g : MvPolynomial V K) (hg : g ∈ monomialOrderBound m b) :
    f * g ∈ monomialOrderBound m (a + b) := by
  apply (mem_monomialOrderBound_iff m (f * g) (a + b)).mpr
  exact m.toSyn_degree_mul_le.trans (add_le_add
    ((mem_monomialOrderBound_iff m f a).mp hf)
    ((mem_monomialOrderBound_iff m g b).mp hg))

def reesOrderLevel (n : m.syn) : Submodule K (coefficientRees J) where
  carrier := {x | ∀ s, x.val.coeff s ∈ monomialOrderBound m n}
  zero_mem' := by intro s; exact (monomialOrderBound m n).zero_mem
  add_mem' hx hy := by
    intro s
    exact (monomialOrderBound m n).add_mem (hx s) (hy s)
  smul_mem' c x hx := by
    intro s
    exact (monomialOrderBound m n).smul_mem c (hx s)

theorem reesOrderLevel_mono : Monotone (reesOrderLevel m J) := by
  intro a b hab x hx s
  exact monomialOrderBound_mono m hab (hx s)

theorem reesOrderLevel_exhaustive (x : coefficientRees J) :
    ∃ n, x ∈ reesOrderLevel m J n := by
  let n : m.syn := x.val.coeff.support.sup (fun s => m.toSyn (m.degree (x.val.coeff s)))
  refine ⟨n, ?_⟩
  intro s
  apply (mem_monomialOrderBound_iff m _ n).mpr
  by_cases hs : s ∈ x.val.coeff.support
  · exact Finset.le_sup (f := fun s => m.toSyn (m.degree (x.val.coeff s))) hs
  · have hz := Finsupp.notMem_support_iff.mp hs
    rw [hz, m.degree_zero, map_zero]
    exact bot_le

theorem reesOrderLevel_one : (1 : coefficientRees J) ∈ reesOrderLevel m J 0 := by
  intro s
  change (1 : AddMonoidAlgebra (MvPolynomial V K) ℕ).coeff s ∈ monomialOrderBound m 0
  by_cases hs : (0 : ℕ) = s
  · subst s
    rw [AddMonoidAlgebra.coeff_one_zero]
    change (1 : MvPolynomial V K) ∈ monomialOrderBound m 0
    apply (mem_monomialOrderBound_iff m _ 0).mpr
    rw [m.degree_one,map_zero]
  · simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne (Ne.symm hs)]
    exact (monomialOrderBound m 0).zero_mem

theorem reesOrderLevel_mul (a b : m.syn) (x y : coefficientRees J)
    (hx : x ∈ reesOrderLevel m J a) (hy : y ∈ reesOrderLevel m J b) :
    x * y ∈ reesOrderLevel m J (a + b) := by
  intro s
  change (x.val * y.val).coeff s ∈ monomialOrderBound m (a + b)
  rw [AddMonoidAlgebra.coeff_mul]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  dsimp only
  split_ifs
  · exact monomialOrderBound_mul m a b _ (hx i) _ (hy j)
  · exact (monomialOrderBound m (a + b)).zero_mem

def groebnerReesFiltration :
    WellOrderedFiltered.MultiplicativeFiltration K (coefficientRees J) m.syn where
  level := reesOrderLevel m J
  mono := reesOrderLevel_mono m J
  exhaustive := reesOrderLevel_exhaustive m J
  one_mem := reesOrderLevel_one m J
  mul_mem := by
    intro a b x hx y hy
    exact reesOrderLevel_mul m J a b x y hx hy

variable [Nontrivial K]
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

theorem groebnerReesBasis_mem_orderLevel (s : ℕ) (a : NonstandardIndex m (J ^ s)) :
    groebnerReesBasis J m G hG hu ⟨s, a⟩ ∈
      reesOrderLevel m J (m.toSyn a.val) := by
  rw [groebnerReesBasis_apply]
  intro t
  rw [idealReesSingle, coefficientSingle_coeff]
  split_ifs with hst
  · exact idealLift_mem_orderBound m (J ^ s) (G s) (hG s) (hu s) a
  · exact (monomialOrderBound m (m.toSyn a.val)).zero_mem

/-- The actual coefficientwise filtration equals the filtration by leading
indices in the proved Rees basis. This is the bridge needed for finite
linear-algebra comparisons in a homogeneous strand. -/
theorem reesOrderLevel_eq_basis_span (n : m.syn) :
    reesOrderLevel m J n = Submodule.span K
      ((groebnerReesBasis J m G hG hu) ''
        {a : GroebnerReesIndex J m | m.toSyn a.2.val ≤ n}) := by
  ext x
  constructor
  · intro hx
    rw [Module.Basis.mem_span_image]
    rintro ⟨s, a⟩ ha
    have hc : (x.val.coeff s).coeff a.val ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp ha
      rwa [groebnerReesBasis_repr] at h
    exact (mem_restrictSupport_iff K).mp (hx s) (mem_support_iff.mpr hc)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨⟨s, a⟩, ha, rfl⟩ := hx
        exact reesOrderLevel_mono m J ha (groebnerReesBasis_mem_orderLevel m J G hG hu s a)
    | zero => exact (reesOrderLevel m J n).zero_mem
    | add x y hx hy ihx ihy => exact (reesOrderLevel m J n).add_mem ihx ihy
    | smul c x hx ih => exact (reesOrderLevel m J n).smul_mem c ih

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesLeading -/
section

/-! # Strict lower terms in the actual Rees multiplication

The comparison of the two Rees modules sends each triangular lift to its
leading monomial. The multiplication discrepancy is proved to have strictly
smaller original term-order weight. These identities also apply when a base
variable multiplies a coefficient, as required for the Koszul differential.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial

variable {K V : Type*} [CommRing K] [Nontrivial K]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

theorem idealLift_product_top_coeff
    (s t : ℕ) (a : NonstandardIndex m (J ^ s)) (b : NonstandardIndex m (J ^ t)) :
    ((idealLift m (J ^ s) (G s) (hG s) (hu s) a).val *
      (idealLift m (J ^ t) (G t) (hG t) (hu t) b).val).coeff (a.val + b.val) = 1 := by
  rw [m.coeff_mul_of_add_of_degree_le]
  · rw [idealLift_nonstandard_coeff, idealLift_nonstandard_coeff]
    simp
  · simpa only [m.toSyn.apply_symm_apply] using
      (mem_monomialOrderBound_iff m _ (m.toSyn a.val)).mp
        (idealLift_mem_orderBound m (J ^ s) (G s) (hG s) (hu s) a)
  · simpa only [m.toSyn.apply_symm_apply] using
      (mem_monomialOrderBound_iff m _ (m.toSyn b.val)).mp
        (idealLift_mem_orderBound m (J ^ t) (G t) (hG t) (hu t) b)

theorem idealLift_product_upper_coeff
    (s t : ℕ) (a : NonstandardIndex m (J ^ s)) (b : NonstandardIndex m (J ^ t))
    (c : V →₀ ℕ) (hc : m.toSyn (a.val + b.val) ≤ m.toSyn c) :
    ((idealLift m (J ^ s) (G s) (hG s) (hu s) a).val *
      (idealLift m (J ^ t) (G t) (hG t) (hu t) b).val).coeff c =
      if a.val + b.val = c then 1 else 0 := by
  by_cases he : a.val + b.val = c
  · rw [if_pos he, ← he]
    exact idealLift_product_top_coeff m J G hG hu s t a b
  · rw [if_neg he]
    apply m.coeff_eq_zero_of_lt
    have hbound := monomialOrderBound_mul m (m.toSyn a.val) (m.toSyn b.val)
      _ (idealLift_mem_orderBound m (J ^ s) (G s) (hG s) (hu s) a)
      _ (idealLift_mem_orderBound m (J ^ t) (G t) (hG t) (hu t) b)
    have hb := (mem_monomialOrderBound_iff m _ _).mp hbound
    rw [← map_add] at hb
    exact hb.trans_lt (lt_of_le_of_ne hc (fun h => he (m.toSyn.injective h)))

theorem groebnerReesBasis_product_upper_coeff
    (a b c : GroebnerReesIndex J m)
    (hc : m.toSyn (a.2.val + b.2.val) ≤ m.toSyn c.2.val) :
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
      if a.1 + b.1 = c.1 ∧ a.2.val + b.2.val = c.2.val then 1 else 0 := by
  rw [groebnerReesBasis_repr, groebnerReesBasis_apply, groebnerReesBasis_apply]
  change ((AddMonoidAlgebra.single a.1
      (idealLift m (J ^ a.1) (G a.1) (hG a.1) (hu a.1) a.2).val *
    AddMonoidAlgebra.single b.1
      (idealLift m (J ^ b.1) (G b.1) (hG b.1) (hu b.1) b.2).val).coeff c.1).coeff c.2.val = _
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hs : a.1 + b.1 = c.1
  · rw [if_pos hs]
    simpa only [hs, true_and] using
      idealLift_product_upper_coeff m J G hG hu a.1 b.1 a.2 b.2 c.2.val hc
  · simp [hs]

/-- The algebra discrepancy is strictly smaller in the original order.
The proof refers to literal coefficients of products in the original ideals. -/
theorem reesInitialLinearEquiv_mul_strict_basis
    (a b c : GroebnerReesIndex J m)
    (hc : (initialReesBasis m J I hinit G hG hu).repr
      (reesInitialLinearEquiv m J I hinit G hG hu
          (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) -
        reesInitialLinearEquiv m J I hinit G hG hu (groebnerReesBasis J m G hG hu a) *
          reesInitialLinearEquiv m J I hinit G hG hu (groebnerReesBasis J m G hG hu b)) c ≠ 0) :
    m.toSyn c.2.val < m.toSyn (a.2.val + b.2.val) := by
  by_contra hn
  apply hc
  rw [map_sub, Finsupp.sub_apply, reesInitialLinearEquiv_repr,
    reesInitialLinearEquiv_basis, reesInitialLinearEquiv_basis, initialReesBasis_mul,
    Module.Basis.repr_self, Finsupp.single_apply,
    groebnerReesBasis_product_upper_coeff m J G hG hu a b c (le_of_not_gt hn)]
  apply sub_eq_zero.mpr
  congr 1
  apply propext
  constructor
  · rintro ⟨hs, he⟩
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    rcases c with ⟨r, c⟩
    dsimp only at hs he
    subst r
    apply congrArg (Sigma.mk (s + t))
    exact Subtype.ext he
  · intro he
    exact ⟨congrArg Sigma.fst he, congrArg (fun i : GroebnerReesIndex J m => i.2.val) he⟩

theorem groebnerReesBasis_product_leading_coeff
    (a b c : GroebnerReesIndex J m)
    (hc : m.toSyn (a.2.val + b.2.val) ≤ m.toSyn c.2.val) :
    (groebnerReesBasis J m G hG hu).repr
      (groebnerReesBasis J m G hG hu a * groebnerReesBasis J m G hG hu b) c =
    (initialReesBasis m J I hinit G hG hu).repr
      (initialReesBasis m J I hinit G hG hu a * initialReesBasis m J I hinit G hG hu b) c := by
  by_contra hne
  apply (not_lt_of_ge hc)
  apply reesInitialLinearEquiv_mul_strict_basis m J I hinit G hG hu a b c
  rw [map_sub, Finsupp.sub_apply, reesInitialLinearEquiv_repr,
    reesInitialLinearEquiv_basis, reesInitialLinearEquiv_basis]
  exact sub_ne_zero.mpr hne

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorExteriorKoszul -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.TensorExteriorKoszul
open Classical CommAlg CommAlg.Koszul CategoryTheory
open scoped TensorProduct
universe u
variable {K R V M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype V] [LinearOrder V] [AddCommGroup M] [Module R M] [Module K M]
  [IsScalarTower K R M]

abbrev Total := M ⊗[K] Simplicial.Ambient V K

/-- Coordinates in the genuine tensor exterior algebra, before taking any
homological degree or quotient. Coefficients remain the original module. -/
def coordinates : Total (K := K) (V := V) (M := M) ≃ₗ[K] (Finset V →₀ M) :=
  TensorProduct.equivFinsuppOfBasisRight Simplicial.basis

@[simp] lemma coordinates_tmul_basis (m : M) (F : Finset V) :
    coordinates (m ⊗ₜ[K] Simplicial.basis F) = Finsupp.single F m := by
  ext G
  rw [coordinates,TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
    Module.Basis.repr_self]
  by_cases h : F=G <;> simp [Finsupp.single_apply,h]

@[simp] lemma coordinates_symm_single (m : M) (F : Finset V) :
    (coordinates (K := K) (M := M)).symm (Finsupp.single F m) =
      m ⊗ₜ[K] Simplicial.basis F := by
  apply (coordinates (K := K) (M := M)).injective
  rw [LinearEquiv.apply_symm_apply,coordinates_tmul_basis]

/-- The actual homological-degree submodule: its only exterior coordinates
have cardinality `i`. This definition imposes no cycle or homology condition. -/
def piece (i : ℕ) : Submodule K (Total (K := K) (V := V) (M := M)) :=
  (Finsupp.supported M K {F : Finset V | F.card=i}).comap coordinates.toLinearMap

def pieceCoordinates (i : ℕ) :
    piece (K := K) (V := V) (M := M) i ≃ₗ[K] (Set.powersetCard V i →₀ M) :=
  ((coordinates (K := K) (V := V) (M := M)).ofSubmodule'
    (Finsupp.supported M K {F : Finset V | F.card = i})).trans
      (Finsupp.supportedEquivFinsupp (R := K) {F : Finset V | F.card = i})

def lift (i : ℕ) : (Set.powersetCard V i →₀ M) →ₗ[K]
    Total (K := K) (V := V) (M := M) :=
  (piece i).subtype.comp (pieceCoordinates i).symm.toLinearMap

@[simp] lemma lift_single (i : ℕ) (F : Set.powersetCard V i) (m : M) :
    lift (K := K) i (Finsupp.single F m) = m ⊗ₜ[K] Simplicial.basis F.val := by
  change (coordinates (K := K) (V := V) (M := M)).symm
    ((Finsupp.supportedEquivFinsupp (R := K) {F : Finset V | F.card=i}).symm
      (Finsupp.single F m)).val = _
  rw [Finsupp.supportedEquivFinsupp_symm_single,coordinates_symm_single]

lemma lift_injective (i : ℕ) : Function.Injective (lift (K := K) (V := V) (M := M) i) :=
  Subtype.val_injective.comp (pieceCoordinates i).symm.injective

/-- The literal coefficient-action Koszul differential on the tensor exterior
module. It is subsequently compared to Mathlib's tensor Koszul complex. -/
def differential (x : V → R) : Module.End K (Total (K := K) (V := V) (M := M)) :=
  ∑ v : V, TensorProduct.map (Algebra.lsmul K K M (x v)) (Simplicial.contraction v)

lemma differential_tmul (x : V → R) (m : M) (z : Simplicial.Ambient V K) :
    differential x (m ⊗ₜ[K] z) =
      ∑ v : V, (x v • m) ⊗ₜ[K] Simplicial.contraction v z := by
  simp [differential,TensorProduct.map_tmul,Algebra.lsmul_apply]

lemma differential_lift_single (x : V → R) (i : ℕ)
    (F : Set.powersetCard V (i+1)) (m : M) :
    differential x (lift (K := K) (i+1) (Finsupp.single F m)) =
      lift (K := K) i
        (coordinateDifferential x (ModuleCat.of R M) i (Finsupp.single F m)) := by
  rw [lift_single,differential_tmul,coordinateDifferential_single,map_sum]
  calc
    (∑ v : V, (x v • m) ⊗ₜ[K] Simplicial.contraction v (Simplicial.basis F.val)) =
        ∑ v∈F.val, (x v • m) ⊗ₜ[K] Simplicial.contraction v (Simplicial.basis F.val) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      rw [Simplicial.contraction_basis,if_neg hv,TensorProduct.tmul_zero]
    _ = ∑ v : {v // v∈F.val},
        (x v.val • m) ⊗ₜ[K] Simplicial.contraction v.val (Simplicial.basis F.val) :=
      Finset.sum_subtype F.val (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Simplicial.contraction_basis,if_pos v.property,lift_single,TensorProduct.tmul_smul]
      change (TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val) •
          ((x v.val • m) ⊗ₜ[K] Simplicial.basis (F.val.erase v.val)) =
        (x v.val • (TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val • m)) ⊗ₜ[K]
          Simplicial.basis (F.val.erase v.val)
      rw [smul_comm (x v.val) (TauCeti.ExteriorAlgebra.basisEraseSign v.val F.val),
        TensorProduct.smul_tmul']

/-- The actual standard differential in every homological degree, with the
comparison proved on all vectors, not only on basis elements. -/
theorem differential_lift (x : V → R) (i : ℕ) (z : Set.powersetCard V (i+1) →₀ M) :
    differential x (lift (K := K) (i+1) z) =
      lift (K := K) i (coordinateDifferential x (ModuleCat.of R M) i z) := by
  have h : (differential (K := K) (M := M) x).comp (lift (i+1)) =
      (lift i).comp ((coordinateDifferential x (ModuleCat.of R M) i).restrictScalars K) := by
    apply Finsupp.lhom_ext
    intro F m
    exact differential_lift_single x i F m
  exact LinearMap.congr_fun h z

def pieceDifferential (x : V → R) (i : ℕ) :
    piece (K := K) (V := V) (M := M) (i+1) →ₗ[K] piece (K := K) (V := V) (M := M) i :=
  (pieceCoordinates i).symm.toLinearMap.comp
    (((coordinateDifferential x (ModuleCat.of R M) i).restrictScalars K).comp
      (pieceCoordinates (i+1)).toLinearMap)

lemma pieceDifferential_val (x : V → R) (i : ℕ)
    (z : piece (K := K) (V := V) (M := M) (i+1)) :
    (pieceDifferential x i z).val = differential x z.val := by
  have h := differential_lift (K := K) x i (pieceCoordinates (i+1) z)
  simpa only [lift,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,pieceDifferential,LinearMap.restrictScalars_apply,
    Submodule.subtype_apply] using h.symm

lemma pieceDifferential_comp (x : V → R) (i : ℕ) :
    (pieceDifferential (K := K) (M := M) x i).comp (pieceDifferential x (i+1))=0 := by
  apply LinearMap.ext
  intro z
  simp only [pieceDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply,LinearEquiv.apply_symm_apply,LinearMap.zero_apply]
  rw [show coordinateDifferential x (ModuleCat.of R M) i
      (coordinateDifferential x (ModuleCat.of R M) (i+1) (pieceCoordinates (i+2) z))=0 from
    LinearMap.congr_fun (coordinateDifferential_comp x (ModuleCat.of R M) i) _]
  exact map_zero _

def complex (x : V → R) : ChainComplex (ModuleCat.{u} K) ℕ :=
  ChainComplex.of (fun i => ModuleCat.of K (piece (K := K) (V := V) (M := M) i))
    (fun i => ModuleCat.ofHom (pieceDifferential x i))
    (fun i => ModuleCat.hom_ext (pieceDifferential_comp x i))

/-- Scalar restriction is an identity on values, with its scalar compatibility
proved rather than presumed definitionally equal. -/
def restrictionEquiv (i : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap K R)).obj
      (ModuleCat.of R (Set.powersetCard V i →₀ M))) ≃ₗ[K]
        (Set.powersetCard V i →₀ M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := by
    change (algebraMap K R c) • (show Set.powersetCard V i →₀ M from z) =
      c • (show Set.powersetCard V i →₀ M from z)
    exact algebraMap_smul R c _

/-- A degreewise isomorphism from the genuine tensor Koszul complex, after
restriction of scalars, to the literal tensor-exterior complex above. -/
def coordinateIso (x : V → R) :
    ((ModuleCat.restrictScalars (algebraMap K R)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (coordinateComplex x (ModuleCat.of R M)) ≅
        complex (K := K) (M := M) x :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ((restrictionEquiv (K := K) (R := R) (M := M) i).trans
      (pieceCoordinates i).symm).toModuleIso) (by
      intro i j hij
      obtain rfl : i=j+1 := hij.symm
      simp only [Functor.mapHomologicalComplex_obj_d,coordinateComplex_d,
        complex,ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change pieceDifferential (K := K) x j
          ((pieceCoordinates (K := K) (V := V) (M := M) (j+1)).symm z) =
        (pieceCoordinates (K := K) (V := V) (M := M) j).symm
          (coordinateDifferential x (ModuleCat.of R M) j z)
      simp only [pieceDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearMap.restrictScalars_apply,LinearEquiv.apply_symm_apply])

def tensorKoszulIso (x : V → R) :
    ((ModuleCat.restrictScalars (algebraMap K R)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyCoefficientComplex x (ModuleCat.of R M)) ≅
        complex (K := K) (M := M) x :=
  ((ModuleCat.restrictScalars (algebraMap K R)).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapIso (coordinateComplexIso x (ModuleCat.of R M)) ≪≫
      coordinateIso x

section Polynomial
variable [Module (MvPolynomial V K) M] [IsScalarTower K (MvPolynomial V K) M]

/-- The paper's exact argument order `Tor^S(M,K)`, with the coefficient ring
carrying evaluation-at-zero action, is computed by the literal tensor exterior
complex. This is an isomorphism of genuine derived-functor homology objects. -/
def polynomialTorIso [Nontrivial K] (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))).obj
      (((Tor (ModuleCat (MvPolynomial V K)) i).obj
        (ModuleCat.of (MvPolynomial V K) M)).obj
          (residueCoefficientModule (V := V) (k := K))) ≅
      (complex (K := K) (M := M) (MvPolynomial.X : V → MvPolynomial V K)).homology i :=
  let F := ModuleCat.restrictScalars (algebraMap K (MvPolynomial V K))
  let N := ModuleCat.of (MvPolynomial V K) M
  let C := familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V K) N
  F.mapIso ((FourPapers.Sublattice.finitePolynomialTorPaperIso i N).symm ≪≫
      CommAlg.Koszul.finitePolynomialTorIso i N) ≪≫
    ((C.sc i).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat K) (ComplexShape.down ℕ) i).mapIso
      (tensorKoszulIso (K := K) (M := M) (MvPolynomial.X : V → MvPolynomial V K))

end Polynomial

end FourPapers.TensorExteriorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulLeibniz -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.TensorExteriorKoszul
open Classical CommAlg CommAlg.Koszul
open scoped TensorProduct
universe u
variable {K A V : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]

def involute : (A ⊗[K] Simplicial.Ambient V K) →ₐ[K]
    (A ⊗[K] Simplicial.Ambient V K) :=
  Algebra.TensorProduct.map (AlgHom.id K A) CliffordAlgebra.involute

@[simp] lemma involute_tmul (a : A) (z : Simplicial.Ambient V K) :
    involute (a ⊗ₜ[K] z)=a ⊗ₜ[K] CliffordAlgebra.involute z := by
  simp only [involute,Algebra.TensorProduct.map_tmul,AlgHom.id_apply]

/-- The full parity Leibniz identity for the actual coefficient-action
Koszul differential on the tensor exterior algebra. -/
theorem differential_mul (x : V → A)
    (z t : A ⊗[K] Simplicial.Ambient V K) :
    differential (K := K) (R := A) (M := A) x (z*t)=
      differential x z*t+involute z*differential x t := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w ihz ihw =>
    simp only [add_mul,map_add,ihz,ihw]
    abel
  | tmul a u =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add z w ihz ihw =>
      simp only [mul_add,map_add,ihz,ihw]
      abel
    | tmul b v =>
      rw [Algebra.TensorProduct.tmul_mul_tmul,differential_tmul,
        differential_tmul,differential_tmul,involute_tmul,
        Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      change ((x j*(a*b)) ⊗ₜ[K] Simplicial.contraction j (u*v))=
        ((x j*a) ⊗ₜ[K] Simplicial.contraction j u)*(b ⊗ₜ[K] v)+
          (a ⊗ₜ[K] CliffordAlgebra.involute u)*((x j*b) ⊗ₜ[K] Simplicial.contraction j v)
      rw [CliffordAlgebra.contractLeft_mul,TensorProduct.tmul_add,
        Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul]
      congr 1
      · rw [mul_assoc]
      · rw [mul_left_comm]

theorem differential_one (x : V → A) :
    differential (K := K) (R := A) (M := A) x (1 : A ⊗[K] Simplicial.Ambient V K)=0 := by
  change differential (K := K) (R := A) (M := A) x ((1:A) ⊗ₜ[K] (1:Simplicial.Ambient V K))=0
  rw [differential_tmul]
  apply Finset.sum_eq_zero
  intro v hv
  rw [CliffordAlgebra.contractLeft_one,TensorProduct.tmul_zero]

theorem cycles_mul (x : V → A) (z t : A ⊗[K] Simplicial.Ambient V K)
    (hz : differential (K := K) (R := A) (M := A) x z=0)
    (ht : differential (K := K) (R := A) (M := A) x t=0) :
    differential (K := K) (R := A) (M := A) x (z*t)=0 := by
  rw [differential_mul,hz,ht,zero_mul,mul_zero,zero_add]

theorem cycles_list_prod (x : V → A) (L : List (A ⊗[K] Simplicial.Ambient V K))
    (hL : ∀z∈L,differential (K := K) (R := A) (M := A) x z=0) :
    differential (K := K) (R := A) (M := A) x L.prod=0 := by
  induction L with
  | nil => exact differential_one x
  | cons z L ih =>
    exact cycles_mul x z L.prod (hL z (List.mem_cons_self ..))
      (ih (fun t ht => hL t (List.mem_cons_of_mem _ ht)))

end FourPapers.TensorExteriorKoszul
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulSquareZero -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.TensorExteriorKoszul
open Classical CommAlg CommAlg.Koszul
open scoped TensorProduct
universe u
variable {K R V M : Type u} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype V] [LinearOrder V] [AddCommGroup M] [Module R M] [Module K M]
  [IsScalarTower K R M]

lemma differential_lift_zero (x : V → R) (z : Set.powersetCard V 0 →₀ M) :
    differential (K := K) x (lift (K := K) 0 z)=0 := by
  have he : (differential (K := K) (M := M) x).comp (lift 0)=0 := by
    apply Finsupp.lhom_ext
    intro F m
    change differential x (lift (K := K) 0 (Finsupp.single F m))=0
    rw [lift_single,differential_tmul]
    have hf : F.val=∅ := Finset.card_eq_zero.mp F.property
    simp only [hf,Simplicial.contraction_basis,Finset.notMem_empty,if_false,
      TensorProduct.tmul_zero,Finset.sum_const_zero]
  exact LinearMap.congr_fun he z

lemma differential_square_tmul_basis (x : V → R) (m : M) (F : Finset V) :
    differential (K := K) x (differential x (m ⊗ₜ[K] Simplicial.basis F))=0 := by
  cases hc : F.card with
  | zero =>
    have hf : F=∅ := Finset.card_eq_zero.mp hc
    rw [differential_tmul]
    simp only [hf,Simplicial.contraction_basis,Finset.notMem_empty,if_false,
      TensorProduct.tmul_zero,Finset.sum_const_zero,map_zero]
  | succ n =>
    let F' : Set.powersetCard V (n+1) := ⟨F,hc⟩
    rw [show m ⊗ₜ[K] Simplicial.basis F=lift (K := K) (n+1) (Finsupp.single F' m) from
      (lift_single (n+1) F' m).symm,differential_lift]
    cases n with
    | zero => exact differential_lift_zero x _
    | succ i =>
      rw [differential_lift]
      have hz := LinearMap.congr_fun (coordinateDifferential_comp x (ModuleCat.of R M) i)
        (Finsupp.single F' m)
      change coordinateDifferential x (ModuleCat.of R M) i
        (coordinateDifferential x (ModuleCat.of R M) (i+1) (Finsupp.single F' m))=0 at hz
      rw [hz,map_zero]

/-- Square-zero for the actual total tensor differential, without imposing a
homological-degree restriction or freeness on the coefficient module. -/
theorem differential_comp (x : V → R) :
    (differential (K := K) (M := M) x).comp (differential x)=0 := by
  apply TensorProduct.ext'
  intro m z
  have he : ((differential (K := K) (M := M) x).comp (differential x)).comp
      ((TensorProduct.mk K M (Simplicial.Ambient V K)) m)=0 := by
    apply (Simplicial.basis (k := K)).ext
    intro F
    exact differential_square_tmul_basis x m F
  exact LinearMap.congr_fun he z

section CoefficientAlgebra
variable {A : Type u} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower K R A]

/-- Coefficient action through a polynomial quotient is exactly multiplication
by the images of the variables in that quotient. -/
theorem differential_algebraMap (x : V → R) :
    differential (K := K) (R := R) (M := A) x=
      differential (K := K) (R := A) (M := A) (fun v => algebraMap R A (x v)) := by
  apply TensorProduct.ext'
  intro a z
  rw [differential_tmul,differential_tmul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Algebra.smul_def]
  rfl

end CoefficientAlgebra
end FourPapers.TensorExteriorKoszul
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.TensorKoszulParity -/
section

/-! # The actual tensor Koszul differential as a parity differential algebra -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.TensorExteriorKoszul

open Classical CommAlg CommAlg.Koszul
open scoped TensorProduct

universe u
variable {K A V : Type u} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]

theorem involute_square (z : A ⊗[K] Simplicial.Ambient V K) :
    involute (involute z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a z => rw [involute_tmul, involute_tmul, CliffordAlgebra.involute_involute]

theorem differential_involute (x : V → A)
    (z : A ⊗[K] Simplicial.Ambient V K) :
    differential (K := K) (R := A) (M := A) x (involute z) =
      -involute (differential x z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw, neg_add]
  | tmul a z =>
      rw [involute_tmul, differential_tmul, differential_tmul, map_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rw [involute_tmul, CliffordAlgebra.involute_contractLeft,
        TensorProduct.tmul_neg, neg_neg]

/-- All operations are those of the tensor exterior algebra and the literal
sum of multiplication by `x v` followed by contraction in `v`. -/
def parityDifferential (x : V → A) :
    ParityDifferential K (A ⊗[K] Simplicial.Ambient V K) where
  d := differential (K := K) (R := A) (M := A) x
  parity := involute
  square_zero z := LinearMap.congr_fun (differential_comp x) z
  parity_square := involute_square
  anticommute := differential_involute x
  map_one := differential_one x
  leibniz := differential_mul x

end FourPapers.TensorExteriorKoszul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Universal.HomogeneousBasis -/
section

section
/-! # A homogeneous change of basis has a homogeneous inverse

This holds over an arbitrary commutative ring and for arbitrary index sets.
It follows by comparing the actual coefficient projections for each degree.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Universal

open Classical

variable {I J D K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

def basisDegreeProjection (b : Module.Basis I K M) (degree : I → D) (d : D) :
    M →ₗ[K] M :=
  b.repr.symm.toLinearMap.comp
    (({
      toFun := fun f : I →₀ K => f.filter (fun i => degree i = d)
      map_add' := by
        intro f g
        ext i
        by_cases hi : degree i = d <;> simp [Finsupp.filter_apply, hi]
      map_smul' := by
        intro c f
        ext i
        by_cases hi : degree i = d <;> simp [Finsupp.filter_apply, hi]
    } : (I →₀ K) →ₗ[K] (I →₀ K)).comp b.repr.toLinearMap)

@[simp] theorem basisDegreeProjection_repr (b : Module.Basis I K M)
    (degree : I → D) (d : D) (x : M) (i : I) :
    b.repr (basisDegreeProjection b degree d x) i =
      if degree i = d then b.repr x i else 0 := by
  simp [basisDegreeProjection, Finsupp.filter_apply]

@[simp] theorem basisDegreeProjection_basis (b : Module.Basis I K M)
    (degree : I → D) (d : D) (i : I) :
    basisDegreeProjection b degree d (b i) = if degree i = d then b i else 0 := by
  apply b.repr.injective
  ext j
  by_cases hi : degree i = d
  · by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [basisDegreeProjection_repr, hi, Module.Basis.repr_self,
        Finsupp.single_apply, hji, Ne.symm hji]
  · by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [basisDegreeProjection_repr, hi, Module.Basis.repr_self,
        Finsupp.single_apply, hji, Ne.symm hji]

theorem basisDegreeProjection_eq_of_homogeneous
    (b : Module.Basis I K M) (c : Module.Basis J K M)
    (degree : I → D) (degree' : J → D)
    (h : ∀ i j, degree i ≠ degree' j → b.repr (c j) i = 0) (d : D) :
    basisDegreeProjection b degree d = basisDegreeProjection c degree' d := by
  apply c.ext
  intro j
  rw [basisDegreeProjection_basis]
  apply b.repr.injective
  ext i
  rw [basisDegreeProjection_repr]
  by_cases hj : degree' j = d
  · rw [if_pos hj]
    by_cases hi : degree i = d
    · rw [if_pos hi]
    · rw [if_neg hi]
      exact (h i j (by simpa only [hj] using hi)).symm
  · rw [if_neg hj, map_zero, Finsupp.zero_apply]
    by_cases hi : degree i = d
    · rw [if_pos hi]
      exact h i j (fun he => hj (he.symm.trans hi))
    · rw [if_neg hi]

/-- The inverse coefficient matrix has the same exact degree blocks. -/
theorem basis_repr_homogeneous_symm
    (b : Module.Basis I K M) (c : Module.Basis J K M)
    (degree : I → D) (degree' : J → D)
    (h : ∀ i j, degree i ≠ degree' j → b.repr (c j) i = 0)
    (i : I) (j : J) (hne : degree' j ≠ degree i) : c.repr (b i) j = 0 := by
  have he := congrArg (fun f : M →ₗ[K] M => c.repr (f (b i)) j)
    (basisDegreeProjection_eq_of_homogeneous b c degree degree' h (degree i))
  simpa [hne] using he

end FourPapers.Universal
end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedBasisFiltration -/
section

/-! # Multiplicative filtrations from a genuine ordered basis -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.OrderedBasis

open Classical
open scoped BigOperators

variable {K A I Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (b : Module.Basis I K A) (w : I → Γ)

def level (n : Γ) : Submodule K A := Submodule.span K (b '' {i | w i ≤ n})
def lower (n : Γ) : Submodule K A := Submodule.span K (b '' {i | w i < n})

theorem level_mono : Monotone (level b w) := by
  intro n m hnm
  exact Submodule.span_mono (Set.image_mono (fun i hi => hi.trans hnm))

theorem level_exhaustive (x : A) : ∃ n, x ∈ level b w n := by
  by_cases hx : (b.repr x).support.Nonempty
  · let S := (b.repr x).support.image w
    have hS : S.Nonempty := hx.image w
    refine ⟨S.max' hS, ?_⟩
    rw [level, b.mem_span_image]
    intro i hi
    exact Finset.le_max' S _ (Finset.mem_image_of_mem w hi)
  · have he : x = 0 := by
      apply b.repr.injective
      rw [map_zero]
      exact Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hx)
    exact ⟨0, he ▸ (level b w 0).zero_mem⟩

theorem basis_mem_level (i : I) : b i ∈ level b w (w i) :=
  Submodule.subset_span ⟨i, le_rfl, rfl⟩

variable (h1 : ∀ i, b.repr (1 : A) i ≠ 0 → w i ≤ 0)
  (hmul : ∀ i j k, b.repr (b i * b j) k ≠ 0 → w k ≤ w i + w j)

include h1 in
theorem one_mem_level : (1 : A) ∈ level b w 0 := by
  rw [level, b.mem_span_image]
  intro i hi
  exact h1 i (Finsupp.mem_support_iff.mp hi)

include hmul in
theorem mul_mem_level (n m : Γ) (x y : A)
    (hx : x ∈ level b w n) (hy : y ∈ level b w m) :
    x * y ∈ level b w (n + m) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, hj, rfl⟩ := hy
          rw [level, b.mem_span_image]
          intro k hk
          exact (hmul i j k (Finsupp.mem_support_iff.mp hk)).trans (add_le_add hi hj)
      | zero => simpa only [mul_zero] using (level b w (n + m)).zero_mem
      | add y z hy hz ihy ihz => simpa only [mul_add] using (level b w (n + m)).add_mem ihy ihz
      | smul c y hy ih => simpa only [mul_smul_comm] using (level b w (n + m)).smul_mem c ih
  | zero => simpa only [zero_mul] using (level b w (n + m)).zero_mem
  | add x z hx hz ihx ihz => simpa only [add_mul] using (level b w (n + m)).add_mem ihx ihz
  | smul c x hx ih => simpa only [smul_mul_assoc] using (level b w (n + m)).smul_mem c ih

def filtration : WellOrderedFiltered.MultiplicativeFiltration K A Γ where
  level := level b w
  mono := level_mono b w
  exhaustive := level_exhaustive b w
  one_mem := one_mem_level b w h1
  mul_mem := fun n m x hx y hy => mul_mem_level b w hmul n m x y hx hy

theorem filtration_lower (n : Γ) : (filtration b w h1 hmul).lower n = lower b w n := by
  apply le_antisymm
  · rintro x (rfl | ⟨m, hm, hx⟩)
    · exact (lower b w n).zero_mem
    · exact (Submodule.span_mono (Set.image_mono (fun i hi => hi.trans_lt hm))) hx
  · apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    exact Or.inr ⟨w i, hi, basis_mem_level b w i⟩

theorem mem_lower_iff (n : Γ) (x : A) :
    x ∈ (filtration b w h1 hmul).lower n ↔
      ∀ i ∈ (b.repr x).support, w i < n := by
  rw [filtration_lower, lower, b.mem_span_image]
  rfl

theorem linear_preserves_level (d : A →ₗ[K] A)
    (hd : ∀ i j, b.repr (d (b i)) j ≠ 0 → w j ≤ w i)
    (n : Γ) (x : A) (hx : x ∈ level b w n) : d x ∈ level b w n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [level, b.mem_span_image]
      intro j hj
      exact (hd i j (Finsupp.mem_support_iff.mp hj)).trans hi
  | zero => simpa only [map_zero] using (level b w n).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (level b w n).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (level b w n).smul_mem c ih

end FourPapers.OrderedBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.GradedCoefficientLift -/
section

/-! # Maps out of actual coefficient algebras

The multiplication hypotheses below are checked on literal homogeneous
coefficients. They extend to the coefficient algebra by its finite expansion.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical
open scoped BigOperators

variable {K A Γ B : Type*} [CommRing K] [Ring A] [Algebra K A]
  [AddCommMonoid Γ] [Ring B] [Algebra K B]
  (P : Γ → Submodule K A) (h1 : (1 : A) ∈ P 0)
  (hmul : ∀ a b, ∀ x ∈ P a, ∀ y ∈ P b, x * y ∈ P (a + b))

theorem coefficientSingle_mul (a b : Γ) (x : P a) (y : P b) :
    coefficientSingle P h1 hmul a x * coefficientSingle P h1 hmul b y =
      coefficientSingle P h1 hmul (a + b)
        ⟨x.val * y.val, hmul a b x.val x.property y.val y.property⟩ := by
  apply Subtype.ext
  exact AddMonoidAlgebra.single_mul_single a b x.val y.val

theorem coefficientSingle_one :
    coefficientSingle P h1 hmul 0 ⟨1, h1⟩ = 1 := rfl

/-- Elimination by zero, sums, and literal homogeneous coefficients. -/
@[elab_as_elim] theorem gradedCoefficient_induction
    {C : gradedCoefficientAlgebra P h1 hmul → Prop}
    (hzero : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y))
    (hsingle : ∀ g x, C (coefficientSingle P h1 hmul g x))
    (x : gradedCoefficientAlgebra P h1 hmul) : C x := by
  rw [← coefficient_decomposition P h1 hmul x]
  exact Finset.sum_induction _ _ (fun a b ha hb => hadd a b ha hb) hzero
    (fun g _ => hsingle g _)

def gradedCoefficientLinearLift (f : ∀ g, P g →ₗ[K] B) :
    gradedCoefficientAlgebra P h1 hmul →ₗ[K] B :=
  (DFinsupp.lsum K f).comp (gradedCoefficientDFinsuppEquiv P h1 hmul).toLinearMap

@[simp] theorem gradedCoefficientLinearLift_single
    (f : ∀ g, P g →ₗ[K] B) (g : Γ) (x : P g) :
    gradedCoefficientLinearLift P h1 hmul f (coefficientSingle P h1 hmul g x) = f g x := by
  change DFinsupp.lsum K f
    (gradedCoefficientToDFinsupp P h1 hmul (coefficientSingle P h1 hmul g x)) = _
  rw [gradedCoefficientToDFinsupp_single, DFinsupp.lsum_single]

def gradedCoefficientAlgLift (f : ∀ g, P g →ₗ[K] B)
    (hf1 : f 0 ⟨1, h1⟩ = 1)
    (hfmul : ∀ a b (x : P a) (y : P b),
      f (a + b) ⟨x.val * y.val, hmul a b x.val x.property y.val y.property⟩ =
        f a x * f b y) : gradedCoefficientAlgebra P h1 hmul →ₐ[K] B :=
  AlgHom.ofLinearMap (gradedCoefficientLinearLift P h1 hmul f)
    (by
      rw [← coefficientSingle_one P h1 hmul, gradedCoefficientLinearLift_single, hf1])
    (by
      intro x y
      induction x using gradedCoefficient_induction P h1 hmul with
      | hzero => simp
      | hadd x z hx hz => simp only [add_mul, map_add, hx, hz]
      | hsingle a x =>
          induction y using gradedCoefficient_induction P h1 hmul with
          | hzero => simp
          | hadd y z hy hz => simp only [mul_add, map_add, hy, hz]
          | hsingle b y =>
              rw [coefficientSingle_mul, gradedCoefficientLinearLift_single,
                gradedCoefficientLinearLift_single, gradedCoefficientLinearLift_single, hfmul])

@[simp] theorem gradedCoefficientAlgLift_single
    (f : ∀ g, P g →ₗ[K] B) (hf1) (hfmul) (g : Γ) (x : P g) :
    gradedCoefficientAlgLift P h1 hmul f hf1 hfmul
      (coefficientSingle P h1 hmul g x) = f g x :=
  gradedCoefficientLinearLift_single P h1 hmul f g x

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedBasisAssociatedAlgebra -/
section

/-! # Associated algebras from proved leading multiplication coefficients

Both algebras and both bases are supplied as actual algebraic objects. The
only comparison hypotheses are explicit coefficient identities for products
and the unit. The associated-graded equivalence is constructed from them.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.OrderedBasis

open Classical
open scoped BigOperators

variable {K A B I Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [Ring B] [Algebra K B]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (b : Module.Basis I K A) (c : Module.Basis I K B) (w : I → Γ)

def leadingProjection (n : Γ) : A →ₗ[K] B :=
  (Universal.basisDegreeProjection c w n).comp
    (b.repr.trans c.repr.symm).toLinearMap

@[simp] theorem leadingProjection_repr (n : Γ) (x : A) (i : I) :
    c.repr (leadingProjection b c w n x) i = if w i = n then b.repr x i else 0 := by
  simp only [leadingProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Universal.basisDegreeProjection_repr, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

@[simp] theorem leadingProjection_basis (n : Γ) (i : I) :
    leadingProjection b c w n (b i) = if w i = n then c i else 0 := by
  apply c.repr.injective
  ext j
  rw [leadingProjection_repr, Module.Basis.repr_self]
  by_cases hi : w i = n
  · rw [if_pos hi, Module.Basis.repr_self]
    by_cases hij : i = j
    · subst j; simp [hi]
    · simp [Finsupp.single_apply, hij]
  · rw [if_neg hi, map_zero, Finsupp.zero_apply]
    by_cases hij : i = j
    · subst j; simp [hi]
    · simp [Finsupp.single_apply, hij]

variable
  (hcprod : ∀ i j k, c.repr (c i * c j) k ≠ 0 → w k = w i + w j)
  (hlead : ∀ i j k, w i + w j ≤ w k → b.repr (b i * b j) k = c.repr (c i * c j) k)

include hcprod hlead in
theorem product_nonincreasing (i j k : I) (hk : b.repr (b i * b j) k ≠ 0) :
    w k ≤ w i + w j := by
  by_contra hn
  have hgt := lt_of_not_ge hn
  have he := hlead i j k hgt.le
  have hck : c.repr (c i * c j) k ≠ 0 := by rwa [← he]
  exact (ne_of_lt hgt) (hcprod i j k hck).symm

include hcprod hlead in
theorem leadingProjection_mul_basis (n m : Γ) (i j : I)
    (hi : w i ≤ n) (hj : w j ≤ m) :
    leadingProjection b c w (n + m) (b i * b j) =
      leadingProjection b c w n (b i) * leadingProjection b c w m (b j) := by
  rw [leadingProjection_basis, leadingProjection_basis]
  by_cases hin : w i = n
  · rw [if_pos hin]
    by_cases hjm : w j = m
    · rw [if_pos hjm]
      apply c.repr.injective
      ext k
      rw [leadingProjection_repr]
      by_cases hk : w k = n + m
      · rw [if_pos hk]
        exact hlead i j k (by rw [hin, hjm, hk])
      · rw [if_neg hk]
        symm
        by_contra hne
        exact hk (by simpa only [hin, hjm] using hcprod i j k hne)
    · rw [if_neg hjm, mul_zero]
      apply c.repr.injective
      ext k
      rw [leadingProjection_repr, map_zero, Finsupp.zero_apply]
      split_ifs with hk
      · by_contra hne
        have hbound := product_nonincreasing b c w hcprod hlead i j k hne
        have hlt : w i + w j < n + m := by
          rw [hin]
          exact add_lt_add_of_le_of_lt (le_refl n) (lt_of_le_of_ne hj hjm)
        exact (not_lt_of_ge hbound) (by simpa only [hk] using hlt)
      · rfl
  · rw [if_neg hin, zero_mul]
    apply c.repr.injective
    ext k
    rw [leadingProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hk
    · by_contra hne
      have hbound := product_nonincreasing b c w hcprod hlead i j k hne
      have hlt : w i + w j < n + m :=
        add_lt_add_of_lt_of_le (lt_of_le_of_ne hi hin) hj
      exact (not_lt_of_ge hbound) (by simpa only [hk] using hlt)
    · rfl

include hcprod hlead in
theorem leadingProjection_mul (n m : Γ) (x y : A)
    (hx : x ∈ level b w n) (hy : y ∈ level b w m) :
    leadingProjection b c w (n + m) (x * y) =
      leadingProjection b c w n x * leadingProjection b c w m y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, hj, rfl⟩ := hy
          exact leadingProjection_mul_basis b c w hcprod hlead n m i j hi hj
      | zero => simp
      | add y z hy hz ihy ihz => simp only [mul_add, map_add, ihy, ihz]
      | smul r y hy ih => simp only [mul_smul_comm, map_smul, ih]
  | zero => simp
  | add x z hx hz ihx ihz => simp only [add_mul, map_add, ihx, ihz]
  | smul r x hx ih => simp only [smul_mul_assoc, map_smul, ih]

variable (h1 : ∀ i, b.repr (1 : A) i ≠ 0 → w i ≤ 0)
  (hone : leadingProjection b c w 0 1 = 1)

abbrev comparisonFiltration := filtration b w h1 (product_nonincreasing b c w hcprod hlead)

def specialization : (comparisonFiltration b c w hcprod hlead h1).rees →ₐ[K] B :=
  gradedCoefficientAlgLift (level b w) (one_mem_level b w h1)
    (fun n m x hx y hy => mul_mem_level b w (product_nonincreasing b c w hcprod hlead)
      n m x y hx hy)
    (fun n => (leadingProjection b c w n).domRestrict (level b w n)) hone
    (fun n m x y => leadingProjection_mul b c w hcprod hlead n m x.val y.val x.property y.property)

@[simp] theorem specialization_monomial (n : Γ) (x : level b w n) :
    specialization b c w hcprod hlead h1 hone
      ((comparisonFiltration b c w hcprod hlead h1).monomial n x) = leadingProjection b c w n x.val :=
  gradedCoefficientAlgLift_single _ _ _ _ _ _ _ _

theorem specialization_repr
    (x : (comparisonFiltration b c w hcprod hlead h1).rees) (i : I) :
    c.repr (specialization b c w hcprod hlead h1 hone x) i =
      b.repr (x.val.coeff (w i)) i := by
  induction x using gradedCoefficient_induction
      (level b w) (one_mem_level b w h1)
      (fun n m x hx y hy => mul_mem_level b w (product_nonincreasing b c w hcprod hlead)
        n m x y hx hy) with
  | hzero => simp
  | hadd x y hx hy =>
      simpa only [Subalgebra.coe_add, map_add, Finsupp.add_apply,
        AddMonoidAlgebra.coeff_add] using congrArg₂ (· + ·) hx hy
  | hsingle n x =>
      change c.repr (specialization b c w hcprod hlead h1 hone
        ((comparisonFiltration b c w hcprod hlead h1).monomial n x)) i =
          b.repr (((comparisonFiltration b c w hcprod hlead h1).monomial n x).val.coeff
            (w i)) i
      rw [specialization_monomial, leadingProjection_repr,
        (comparisonFiltration b c w hcprod hlead h1).monomial_coeff]
      by_cases hi : w i = n
      · subst n; simp
      · simp [hi, Ne.symm hi]

theorem specialization_ker :
    RingHom.ker (specialization b c w hcprod hlead h1 hone).toRingHom =
      (comparisonFiltration b c w hcprod hlead h1).strictIdeal.asIdeal := by
  ext x
  rw [RingHom.mem_ker, TwoSidedIdeal.mem_asIdeal,
    (comparisonFiltration b c w hcprod hlead h1).mem_strictIdeal]
  change specialization b c w hcprod hlead h1 hone x = 0 ↔
    ∀ n, x.val.coeff n ∈ (comparisonFiltration b c w hcprod hlead h1).lower n
  constructor
  · intro hx n
    rw [mem_lower_iff]
    intro i hi
    have hle : w i ≤ n := by
      exact (b.mem_span_image.mp (x.property n)) hi
    apply lt_of_le_of_ne hle
    intro he
    have hh := congrArg (fun z : B => c.repr z i) hx
    rw [specialization_repr, he, map_zero, Finsupp.zero_apply] at hh
    exact Finsupp.mem_support_iff.mp hi hh
  · intro hx
    apply c.repr.injective
    ext i
    rw [specialization_repr, map_zero, Finsupp.zero_apply]
    by_contra hi
    have hlt := (mem_lower_iff b w h1 (product_nonincreasing b c w hcprod hlead)
      (w i) (x.val.coeff (w i))).mp (hx (w i)) i (Finsupp.mem_support_iff.mpr hi)
    exact lt_irrefl _ hlt

theorem specialization_surjective : Function.Surjective (specialization b c w hcprod hlead h1 hone) := by
  let f := specialization b c w hcprod hlead h1 hone
  have hspan : (⊤ : Submodule K B) ≤ f.range.toSubmodule := by
    rw [← c.span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply f.mem_range.mpr
    refine ⟨(comparisonFiltration b c w hcprod hlead h1).monomial (w i)
      ⟨b i, basis_mem_level b w i⟩, ?_⟩
    rw [specialization_monomial, leadingProjection_basis, if_pos rfl]
  intro x
  exact f.mem_range.mp (hspan (Submodule.mem_top : x ∈ (⊤ : Submodule K B)))

/-- The actual associated algebra is identified by explicit coefficient
formulas. No algebra or homology equivalence is an input. -/
def associatedAlgebraEquiv :
    (comparisonFiltration b c w hcprod hlead h1).AssociatedGraded ≃ₐ[K] B :=
  (Ideal.quotientEquivAlgOfEq K (specialization_ker b c w hcprod hlead h1 hone).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (specialization_surjective b c w hcprod hlead h1 hone))

/-- Pointwise evaluation of the quotient isomorphism, with its source
algebra kept abstract so typeclass search does not unfold a filtration. -/
private theorem quotientEquivalence_apply_mk
    {R C D : Type*} [CommRing R] [Ring C] [Algebra R C]
    [Ring D] [Algebra R D] (f : C →ₐ[R] D)
    (I : Ideal C) [I.IsTwoSided]
    (hI : I = RingHom.ker f) (hf : Function.Surjective f) (x : C) :
    ((Ideal.quotientEquivAlgOfEq R hI).trans
      (Ideal.quotientKerAlgEquivOfSurjective hf)) (Ideal.Quotient.mk I x) = f x := by
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

set_option backward.isDefEq.respectTransparency true in
@[simp] theorem associatedAlgebraEquiv_leading
    (x : (comparisonFiltration b c w hcprod hlead h1).rees) :
    associatedAlgebraEquiv b c w hcprod hlead h1 hone
      ((comparisonFiltration b c w hcprod hlead h1).leadingMap x) =
        specialization b c w hcprod hlead h1 hone x := by
  exact quotientEquivalence_apply_mk (R := K)
    (C := (comparisonFiltration b c w hcprod hlead h1).rees) (D := B)
    (specialization b c w hcprod hlead h1 hone)
    (comparisonFiltration b c w hcprod hlead h1).strictIdeal.asIdeal
    (specialization_ker b c w hcprod hlead h1 hone).symm
    (specialization_surjective b c w hcprod hlead h1 hone) x

end FourPapers.OrderedBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ParityHomologyEquiv -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.ParityDifferential
variable {K A B : Type*} [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- Transport a differential algebra along a genuine algebra equivalence. The
transported differential will be identified with the literal Koszul formula in
its application; no generation or exactness assertion is built into this data. -/
def pullback (D : ParityDifferential K B) (e : A ≃ₐ[K] B) : ParityDifferential K A where
  d := e.symm.toLinearMap.comp (D.d.comp e.toLinearMap)
  parity := e.symm.toAlgHom.comp (D.parity.comp e.toAlgHom)
  square_zero x := by
    change e.symm (D.d (e (e.symm (D.d (e x))))) = 0
    rw [e.apply_symm_apply, D.square_zero, map_zero]
  parity_square x := by
    change e.symm (D.parity (e (e.symm (D.parity (e x))))) = x
    rw [e.apply_symm_apply, D.parity_square, e.symm_apply_apply]
  anticommute x := by
    change e.symm (D.d (e (e.symm (D.parity (e x))))) =
      -e.symm (D.parity (e (e.symm (D.d (e x)))))
    simp only [e.apply_symm_apply, D.anticommute, map_neg]
  map_one := by
    change e.symm (D.d (e 1)) = 0
    simp only [_root_.map_one, D.map_one, _root_.map_zero]
  leibniz x y := by
    change e.symm (D.d (e (x*y))) =
      e.symm (D.d (e x)) * y + e.symm (D.parity (e x)) * e.symm (D.d (e y))
    rw [map_mul,D.leibniz,map_add,map_mul,map_mul,e.symm_apply_apply]

@[simp] lemma pullback_d (D : ParityDifferential K B) (e : A ≃ₐ[K] B) (x : A) :
    (D.pullback e).d x = e.symm (D.d (e x)) := rfl

@[simp] lemma pullback_intertwines (D : ParityDifferential K B) (e : A ≃ₐ[K] B) (x : A) :
    e ((D.pullback e).d x) = D.d (e x) := e.apply_symm_apply _

variable (D : ParityDifferential K A) (D' : ParityDifferential K B)
  (e : A ≃ₐ[K] B) (hd : ∀ x, e (D.d x) = D'.d (e x))

include hd in
lemma cyclesEquiv_symm_closed (y : D'.cycles) : D.d (e.symm y.val) = 0 := by
  apply e.injective
  rw [hd,e.apply_symm_apply,show D'.d y.val = 0 from y.property,map_zero]

def cyclesEquiv : D.cycles ≃ₐ[K] D'.cycles where
  toFun x := ⟨e x.val,by
    change D'.d (e x.val) = 0
    rw [←hd,show D.d x.val = 0 from x.property,map_zero]⟩
  invFun y := ⟨e.symm y.val,cyclesEquiv_symm_closed D D' e hd y⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_mul' x y := Subtype.ext (map_mul e x.val y.val)
  commutes' c := Subtype.ext (e.commutes c)

@[simp] lemma cyclesEquiv_val (x : D.cycles) :
    (cyclesEquiv D D' e hd x).val = e x.val := rfl

lemma cyclesEquiv_boundaries (x : D.cycles) :
    cyclesEquiv D D' e hd x ∈ D'.boundaries ↔ x ∈ D.boundaries := by
  rw [D'.mem_boundaries,D.mem_boundaries]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨e.symm b, ?_⟩
    apply e.injective
    rw [hd,e.apply_symm_apply]
    exact hb
  · rintro ⟨a,ha⟩
    exact ⟨e a, by rw [←hd,ha]; rfl⟩

lemma cyclesEquiv_map_boundaries :
    D'.boundaries.asIdeal = D.boundaries.asIdeal.map
      (cyclesEquiv D D' e hd).toRingEquiv.toRingHom := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective
    (cyclesEquiv D D' e hd).toRingEquiv.toRingHom (cyclesEquiv D D' e hd).surjective]
  constructor
  · intro hy
    refine ⟨(cyclesEquiv D D' e hd).symm y, ?_, (cyclesEquiv D D' e hd).apply_symm_apply y⟩
    rw [TwoSidedIdeal.mem_asIdeal,←cyclesEquiv_boundaries D D' e hd,
      (cyclesEquiv D D' e hd).apply_symm_apply,←TwoSidedIdeal.mem_asIdeal]
    exact hy
  · rintro ⟨x,hx,rfl⟩
    apply TwoSidedIdeal.mem_asIdeal.mpr
    change cyclesEquiv D D' e hd x ∈ D'.boundaries
    exact (cyclesEquiv_boundaries D D' e hd x).mpr
      (TwoSidedIdeal.mem_asIdeal.mp hx)

/-- The induced algebra equivalence on actual cycles modulo actual boundaries. -/
def homologyEquiv : D.Homology ≃ₐ[K] D'.Homology :=
  Ideal.quotientEquivAlg D.boundaries.asIdeal D'.boundaries.asIdeal
    (cyclesEquiv D D' e hd) (cyclesEquiv_map_boundaries D D' e hd)

@[simp] lemma homologyEquiv_classMap (x : D.cycles) :
    homologyEquiv D D' e hd (D.classMap x) = D'.classMap (cyclesEquiv D D' e hd x) := rfl

end FourPapers.ParityDifferential

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.OrderedBasisAssociatedDGA -/
section

/-! # The differential on the constructed associated algebra

Leading differential coefficients and exact homogeneity of the initial
differential identify the actual associated differential. The same argument
handles parity, so the filtration is a genuine differential algebra
filtration throughout.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.OrderedBasis

open Classical

variable {K A B I Γ : Type*} [CommRing K] [Ring A] [Algebra K A]
  [Ring B] [Algebra K B]
  [AddCancelCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (b : Module.Basis I K A) (c : Module.Basis I K B) (w : I → Γ)

section LinearComparison

variable (f : A →ₗ[K] A) (g : B →ₗ[K] B)
  (hhom : ∀ i j, c.repr (g (c i)) j ≠ 0 → w j = w i)
  (hlead : ∀ i j, w i ≤ w j → b.repr (f (b i)) j = c.repr (g (c i)) j)

include hhom hlead in
theorem linear_nonincreasing (i j : I) (hj : b.repr (f (b i)) j ≠ 0) : w j ≤ w i := by
  by_contra hn
  have hgt := lt_of_not_ge hn
  have he := hlead i j hgt.le
  have hgj : c.repr (g (c i)) j ≠ 0 := by rwa [← he]
  exact (ne_of_lt hgt) (hhom i j hgj).symm

include hhom hlead in
theorem leadingProjection_linear_basis (n : Γ) (i : I) (hi : w i ≤ n) :
    leadingProjection b c w n (f (b i)) = g (leadingProjection b c w n (b i)) := by
  rw [leadingProjection_basis]
  by_cases hin : w i = n
  · rw [if_pos hin]
    apply c.repr.injective
    ext j
    rw [leadingProjection_repr]
    by_cases hj : w j = n
    · rw [if_pos hj]
      exact hlead i j (by rw [hin, hj])
    · rw [if_neg hj]
      symm
      by_contra hne
      exact hj ((hhom i j hne).trans hin)
  · rw [if_neg hin, map_zero]
    apply c.repr.injective
    ext j
    rw [leadingProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hj
    · by_contra hne
      have hle := linear_nonincreasing b c w f g hhom hlead i j hne
      exact (not_lt_of_ge hle) (by simpa only [hj] using lt_of_le_of_ne hi hin)
    · rfl

include hhom hlead in
theorem leadingProjection_linear (n : Γ) (x : A) (hx : x ∈ level b w n) :
    leadingProjection b c w n (f x) = g (leadingProjection b c w n x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact leadingProjection_linear_basis b c w f g hhom hlead n i hi
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul r x hx ih => simp only [map_smul, ih]

end LinearComparison

variable
  (hcprod : ∀ i j k, c.repr (c i * c j) k ≠ 0 → w k = w i + w j)
  (hlead : ∀ i j k, w i + w j ≤ w k → b.repr (b i * b j) k = c.repr (c i * c j) k)
  (h1 : ∀ i, b.repr (1 : A) i ≠ 0 → w i ≤ 0)
  (hone : leadingProjection b c w 0 1 = 1)
  (D : ParityDifferential K A) (E : ParityDifferential K B)
  (hdhom : ∀ i j, c.repr (E.d (c i)) j ≠ 0 → w j = w i)
  (hdlead : ∀ i j, w i ≤ w j → b.repr (D.d (b i)) j = c.repr (E.d (c i)) j)
  (hphom : ∀ i j, c.repr (E.parity (c i)) j ≠ 0 → w j = w i)
  (hplead : ∀ i j, w i ≤ w j → b.repr (D.parity (b i)) j = c.repr (E.parity (c i)) j)

def differential_preserves : ∀ n x,
    x ∈ (comparisonFiltration b c w hcprod hlead h1).level n →
      D.d x ∈ (comparisonFiltration b c w hcprod hlead h1).level n :=
  linear_preserves_level b w D.d (linear_nonincreasing b c w D.d E.d hdhom hdlead)

def parity_preserves : ∀ n x,
    x ∈ (comparisonFiltration b c w hcprod hlead h1).level n →
      D.parity x ∈ (comparisonFiltration b c w hcprod hlead h1).level n :=
  linear_preserves_level b w D.parity.toLinearMap
    (linear_nonincreasing b c w D.parity.toLinearMap E.parity.toLinearMap hphom hplead)

theorem specialization_d
    (x : (comparisonFiltration b c w hcprod hlead h1).rees) :
    specialization b c w hcprod hlead h1 hone
      (((comparisonFiltration b c w hcprod hlead h1).reesDGA D
        (differential_preserves b c w hcprod hlead h1 D E hdhom hdlead)
        (parity_preserves b c w hcprod hlead h1 D E hphom hplead)).d x) =
      E.d (specialization b c w hcprod hlead h1 hone x) := by
  induction x using gradedCoefficient_induction
      (level b w) (one_mem_level b w h1)
      (fun n m x hx y hy => mul_mem_level b w (product_nonincreasing b c w hcprod hlead)
        n m x y hx hy) with
  | hzero => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsingle n x =>
      change specialization b c w hcprod hlead h1 hone
        (((comparisonFiltration b c w hcprod hlead h1).reesDGA D _ _).d
          ((comparisonFiltration b c w hcprod hlead h1).monomial n x)) =
          E.d (specialization b c w hcprod hlead h1 hone
            ((comparisonFiltration b c w hcprod hlead h1).monomial n x))
      rw [WellOrderedFiltered.MultiplicativeFiltration.reesDGA_d_monomial,
        specialization_monomial, specialization_monomial]
      exact leadingProjection_linear b c w D.d E.d hdhom hdlead n x.val x.property

/-- This identifies the associated differential on every element of the
actual quotient algebra, not only on chosen generating cycles. -/
theorem associatedAlgebraEquiv_d
    (x : (comparisonFiltration b c w hcprod hlead h1).AssociatedGraded) :
    associatedAlgebraEquiv b c w hcprod hlead h1 hone
      (((comparisonFiltration b c w hcprod hlead h1).associatedDGA D
        (differential_preserves b c w hcprod hlead h1 D E hdhom hdlead)
        (parity_preserves b c w hcprod hlead h1 D E hphom hplead)).d x) =
      E.d (associatedAlgebraEquiv b c w hcprod hlead h1 hone x) := by
  obtain ⟨x, rfl⟩ := (comparisonFiltration b c w hcprod hlead h1).leadingMap_surjective x
  rw [WellOrderedFiltered.MultiplicativeFiltration.leadingMap_intertwines,
    associatedAlgebraEquiv_leading, associatedAlgebraEquiv_leading]
  exact specialization_d b c w hcprod hlead h1 hone D E hdhom hdlead hphom hplead x

/-- The resulting equivalence is on the literal homology algebras, with
cycles and boundaries transported through the proved differential identity. -/
def associatedHomologyEquiv :
    ((comparisonFiltration b c w hcprod hlead h1).associatedDGA D
      (differential_preserves b c w hcprod hlead h1 D E hdhom hdlead)
      (parity_preserves b c w hcprod hlead h1 D E hphom hplead)).Homology ≃ₐ[K] E.Homology :=
  ParityDifferential.homologyEquiv _ E
    (associatedAlgebraEquiv b c w hcprod hlead h1 hone)
    (associatedAlgebraEquiv_d b c w hcprod hlead h1 hone D E hdhom hdlead hphom hplead)

end FourPapers.OrderedBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesKoszulBasis -/
section

/-! # Actual tensor Koszul bases and their leading multiplication

The exterior weight is added to the polynomial exponent. This is essential:
contraction removes one exterior variable at the same time that the Koszul
differential multiplies its polynomial coefficient by that variable.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped TensorProduct

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m (J ^ s) = I ^ s)
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) (J ^ s))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

abbrev IdealReesKoszul := coefficientRees J ⊗[K] Simplicial.Ambient V K
abbrev IdealReesKoszulIndex := GroebnerReesIndex J m × Finset V

instance (priority := 1200) idealReesKoszulRing : Ring (IdealReesKoszul J) :=
  Algebra.TensorProduct.instRing

instance (priority := 1200) idealReesKoszulAlgebra : Algebra K (IdealReesKoszul J) :=
  Algebra.TensorProduct.instAlgebra

def groebnerReesKoszulBasis : Module.Basis (IdealReesKoszulIndex m J) K (IdealReesKoszul J) :=
  (groebnerReesBasis J m G hG hu).tensorProduct Simplicial.basis

def initialReesKoszulBasis : Module.Basis (IdealReesKoszulIndex m J) K (IdealReesKoszul I) :=
  (initialReesBasis m J I hinit G hG hu).tensorProduct Simplicial.basis

def reesKoszulFineDegree (a : IdealReesKoszulIndex m J) : V →₀ ℕ :=
  a.1.2.val + faceExponent a.2

def reesKoszulWeight (a : IdealReesKoszulIndex m J) : m.syn :=
  m.toSyn (reesKoszulFineDegree m J a)

theorem initialReesKoszul_product_homogeneous
    (a b c : IdealReesKoszulIndex m J)
    (hc : (initialReesKoszulBasis m J I hinit G hG hu).repr
      (initialReesKoszulBasis m J I hinit G hG hu a *
        initialReesKoszulBasis m J I hinit G hG hu b) c ≠ 0) :
    reesKoszulWeight m J c = reesKoszulWeight m J a + reesKoszulWeight m J b := by
  simp only [initialReesKoszulBasis, Module.Basis.tensorProduct_apply',
    Algebra.TensorProduct.tmul_mul_tmul, initialReesBasis_mul] at hc
  by_cases hab : Disjoint a.2 b.2
  · rw [faceBasis_mul_of_disjoint _ _ hab, TensorProduct.tmul_smul,
      map_zsmul_unit, Finsupp.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply] at hc
    have hF : a.2 ∪ b.2 = c.2 := by
      by_contra h
      simp [h] at hc
    have hA : initialReesIndexAdd m J I hinit G hG hu a.1 b.1 = c.1 := by
      by_contra h
      simp [h] at hc
    have hE : c.1.2.val = a.1.2.val + b.1.2.val := by
      simpa only [initialReesIndexAdd] using
        (congrArg (fun z : GroebnerReesIndex J m => z.2.val) hA).symm
    simp only [reesKoszulWeight, reesKoszulFineDegree, hE, ← hF,
      faceExponent_union_of_disjoint _ _ hab, map_add]
    abel
  · rw [faceBasis_mul_of_not_disjoint _ _ hab, TensorProduct.tmul_zero,
      map_zero, Finsupp.zero_apply] at hc
    exact (hc rfl).elim

/-- The leading coefficients of actual products agree with the products in
the actual initial Rees Koszul algebra, in the original monomial order. -/
theorem groebnerReesKoszul_product_leading
    (a b c : IdealReesKoszulIndex m J)
    (hc : reesKoszulWeight m J a + reesKoszulWeight m J b ≤ reesKoszulWeight m J c) :
    (groebnerReesKoszulBasis m J G hG hu).repr
      (groebnerReesKoszulBasis m J G hG hu a * groebnerReesKoszulBasis m J G hG hu b) c =
    (initialReesKoszulBasis m J I hinit G hG hu).repr
      (initialReesKoszulBasis m J I hinit G hG hu a *
        initialReesKoszulBasis m J I hinit G hG hu b) c := by
  simp only [groebnerReesKoszulBasis, initialReesKoszulBasis,
    Module.Basis.tensorProduct_apply', Algebra.TensorProduct.tmul_mul_tmul]
  by_cases hab : Disjoint a.2 b.2
  · rw [faceBasis_mul_of_disjoint _ _ hab, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, map_zsmul_unit, map_zsmul_unit,
      Finsupp.smul_apply, Finsupp.smul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply,
      Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hF : a.2 ∪ b.2 = c.2
    · rw [if_pos hF, one_smul, one_smul]
      congr 1
      apply groebnerReesBasis_product_leading_coeff m J I hinit G hG hu
      have he : reesKoszulWeight m J a + reesKoszulWeight m J b =
          m.toSyn (a.1.2.val + b.1.2.val) + m.toSyn (faceExponent c.2) := by
        simp only [reesKoszulWeight, reesKoszulFineDegree, ← hF,
          faceExponent_union_of_disjoint _ _ hab, map_add]
        abel
      rw [he] at hc
      apply (add_le_add_iff_right (m.toSyn (faceExponent c.2))).mp
      simpa only [reesKoszulWeight, reesKoszulFineDegree, map_add] using hc
    · rw [if_neg hF, zero_smul, zero_smul]
  · rw [faceBasis_mul_of_not_disjoint _ _ hab]
    simp

theorem reesKoszul_one_coeff_equal (a : IdealReesKoszulIndex m J) :
    (groebnerReesKoszulBasis m J G hG hu).repr 1 a =
      (initialReesKoszulBasis m J I hinit G hG hu).repr 1 a := by
  rcases a with ⟨⟨s, a⟩, F⟩
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def]
  simp only [groebnerReesKoszulBasis, initialReesKoszulBasis,
    Module.Basis.tensorProduct_repr_tmul_apply, groebnerReesBasis_repr,
    initialReesBasis_repr]
  rfl

theorem groebnerReesKoszul_one_weight (a : IdealReesKoszulIndex m J)
    (ha : (groebnerReesKoszulBasis m J G hG hu).repr 1 a ≠ 0) :
    reesKoszulWeight m J a = 0 := by
  rcases a with ⟨⟨s, a⟩, F⟩
  rw [Algebra.TensorProduct.one_def] at ha
  simp only [groebnerReesKoszulBasis, Module.Basis.tensorProduct_repr_tmul_apply,
    groebnerReesBasis_repr] at ha
  rw [← faceBasis_empty, Module.Basis.repr_self, Finsupp.single_apply] at ha
  have hF : (∅ : Finset V) = F := by
    by_contra h
    simp [h] at ha
  rw [if_pos hF, one_smul] at ha
  change ((1 : AddMonoidAlgebra (MvPolynomial V K) ℕ).coeff s).coeff a.val ≠ 0 at ha
  have hs : (0 : ℕ) = s := by
    by_contra h
    have hz : (1 : AddMonoidAlgebra (MvPolynomial V K) ℕ).coeff s = 0 := by
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_of_ne (Ne.symm h)]
    exact ha (by rw [hz, MvPolynomial.coeff_zero]; rfl)
  subst s
  rw [AddMonoidAlgebra.coeff_one_zero, MvPolynomial.coeff_one] at ha
  have he : (0 : V →₀ ℕ) = a.val := by
    by_contra h
    rw [if_neg h] at ha
    exact ha rfl
  change m.toSyn (a.val + faceExponent F) = 0
  rw [← hF, faceExponent_empty, add_zero, ← he, map_zero]

theorem groebnerReesKoszul_leading_one :
    OrderedBasis.leadingProjection (groebnerReesKoszulBasis m J G hG hu)
      (initialReesKoszulBasis m J I hinit G hG hu) (reesKoszulWeight m J) 0 1 = 1 := by
  apply (initialReesKoszulBasis m J I hinit G hG hu).repr.injective
  ext a
  rw [OrderedBasis.leadingProjection_repr]
  by_cases ha : reesKoszulWeight m J a = 0
  · rw [if_pos ha]
    exact reesKoszul_one_coeff_equal m J I hinit G hG hu a
  · rw [if_neg ha]
    symm
    by_contra hne
    apply ha
    apply groebnerReesKoszul_one_weight m J G hG hu a
    rwa [reesKoszul_one_coeff_equal m J I hinit G hG hu a]

def idealReesKoszulFiltration :
    WellOrderedFiltered.MultiplicativeFiltration K (IdealReesKoszul J) m.syn :=
  OrderedBasis.comparisonFiltration (groebnerReesKoszulBasis m J G hG hu)
    (initialReesKoszulBasis m J I hinit G hG hu) (reesKoszulWeight m J)
    (initialReesKoszul_product_homogeneous m J I hinit G hG hu)
    (groebnerReesKoszul_product_leading m J I hinit G hG hu)
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)

/-- The literal associated algebra of the actual tensor Koszul algebra is
the actual tensor Koszul algebra of the initial Rees algebra. -/
def idealReesKoszulAssociatedAlgebraEquiv :
    (idealReesKoszulFiltration m J I hinit G hG hu).AssociatedGraded ≃ₐ[K]
      IdealReesKoszul I :=
  OrderedBasis.associatedAlgebraEquiv (groebnerReesKoszulBasis m J G hG hu)
    (initialReesKoszulBasis m J I hinit G hG hu) (reesKoszulWeight m J)
    (initialReesKoszul_product_homogeneous m J I hinit G hG hu)
    (groebnerReesKoszul_product_leading m J I hinit G hG hu)
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)
    (groebnerReesKoszul_leading_one m J I hinit G hG hu)

end FourPapers.Sublattice

end
end
end


end
