module

public import PaperVerification.FermionSuperHighestForms
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Actual coefficient change in the polynomial/exterior algebra

The polynomial variables and both exterior families are fixed; only scalar
coefficients change.  The exterior map is constructed from its universal
property, and the tensor-product map from commuting actual inclusions.  Its
effect on the entire monomial/exterior basis gives the literal scalar-extension
linear equivalence used by quotient descent.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial
open scoped BigOperators TensorProduct

section Data

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem HasHighestPower.map (f : R →+* S) (r : Fin n → ℕ) (p : PolynomialRing R n)
    (i : Fin n) (d : ℕ) (hp : HasHighestPower r p i d) :
    HasHighestPower r (MvPolynomial.map f p) i d := by
  refine ⟨?_,?_⟩
  · rw [MvPolynomial.coeff_map,hp.1,map_one]
  · intro a ha hne
    exact hp.2 a (MvPolynomial.support_map_subset f p ha) hne

/-- Every ring homomorphism preserves the prescribed highest forms and all
required units.  No injectivity or reducedness is needed. -/
def PairedData.map (d : PairedData (K := R) (n := n)) (f : R →+* S) :
    PairedData (K := S) (n := n) where
  positive_n := d.positive_n
  s := d.s
  positive_s := d.positive_s
  r := d.r
  u := d.u
  v := d.v
  positive_r := d.positive_r
  degree_split := d.degree_split
  beta := f ∘ d.beta
  allowed_weights := by
    constructor
    · simpa only [map_natCast] using d.allowed_weights.1.map f
    · intro U hU
      simpa only [Function.comp_def,map_sum] using (d.allowed_weights.2 U hU).map f
  phi := fun i ↦ MvPolynomial.map f (d.phi i)
  a := fun i ↦ MvPolynomial.map f (d.a i)
  b := fun i ↦ MvPolynomial.map f (d.b i)
  highest_phi := fun i ↦ HasHighestPower.map f d.r (d.phi i) i (d.r i) (d.highest_phi i)
  highest_a := fun i ↦ HasHighestPower.map f d.r (d.a i) i (d.u i) (d.highest_a i)
  highest_b := fun i ↦ HasHighestPower.map f d.r (d.b i) i (d.v i) (d.highest_b i)

end Data

section Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

def oddCoefficientMap : OddModule R n →ₗ[R] OddModule S n where
  toFun v i := algebraMap R S (v i)
  map_add' v w := by
    funext i
    exact map_add _ _ _
  map_smul' c v := by
    funext i
    change algebraMap R S (c*v i) = c • algebraMap R S (v i)
    rw [map_mul,Algebra.smul_def]

@[simp] theorem oddCoefficientMap_single (i : OddIndex n) :
    oddCoefficientMap R S (Pi.single i 1) = Pi.single i 1 := by
  classical
  ext j
  by_cases h : j=i <;> simp [oddCoefficientMap,Pi.single_apply,h]

def exteriorCoefficientMap :
    ExteriorAlgebra R (OddModule R n) →ₐ[R] ExteriorAlgebra S (OddModule S n) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι S).restrictScalars R).comp (oddCoefficientMap R S),
      fun v ↦ ExteriorAlgebra.ι_sq_zero _⟩

@[simp] theorem exteriorCoefficientMap_ι (v : OddModule R n) :
    exteriorCoefficientMap R S (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι S (oddCoefficientMap R S v) := by
  exact ExteriorAlgebra.lift_ι_apply _ _ _ _

def polynomialCoefficientMap : PolynomialRing R n →ₐ[R] PolynomialRing S n :=
  MvPolynomial.mapAlgHom (Algebra.ofId R S)

@[simp] theorem polynomialCoefficientMap_apply (p : PolynomialRing R n) :
    polynomialCoefficientMap R S p = MvPolynomial.map (algebraMap R S) p := rfl

def superCoefficientMap : SuperRing R n →ₐ[R] SuperRing S n :=
  Algebra.TensorProduct.lift (R := R) (S := R)
    ((Algebra.TensorProduct.includeLeft (R := S) (S := S) (A := PolynomialRing S n)
      (B := ExteriorAlgebra S (OddModule S n))).restrictScalars R |>.comp
        (polynomialCoefficientMap R S))
    ((Algebra.TensorProduct.includeRight (R := S) (A := PolynomialRing S n)
      (B := ExteriorAlgebra S (OddModule S n))).restrictScalars R |>.comp
        (exteriorCoefficientMap R S))
    (fun p e ↦ (Commute.one_right (polynomialCoefficientMap R S p)).tmul
      (Commute.one_left (exteriorCoefficientMap R S e)))

@[simp] theorem superCoefficientMap_tmul (p : PolynomialRing R n)
    (e : ExteriorAlgebra R (OddModule R n)) :
    superCoefficientMap R S (p ⊗ₜ[R] e) =
      MvPolynomial.map (algebraMap R S) p ⊗ₜ[S] exteriorCoefficientMap R S e := by
  unfold superCoefficientMap
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [AlgHom.comp_apply,
    AlgHom.restrictScalars_apply,Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.tmul_mul_tmul,
    one_mul,mul_one,polynomialCoefficientMap_apply]

theorem superCoefficientMap_polynomial_smul (p : PolynomialRing R n) (x : SuperRing R n) :
    superCoefficientMap R S (p • x) =
      MvPolynomial.map (algebraMap R S) p • superCoefficientMap R S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero,map_zero]
  | tmul a e =>
      rw [TensorProduct.smul_tmul',superCoefficientMap_tmul,superCoefficientMap_tmul,
        TensorProduct.smul_tmul']
      change MvPolynomial.map (algebraMap R S) (p*a) ⊗ₜ[S] exteriorCoefficientMap R S e = _
      rw [map_mul]
      rfl
  | add x y hx hy => simp only [smul_add,map_add,hx,hy]

@[simp] theorem superCoefficientMap_theta (i : Fin n) :
    superCoefficientMap R S (theta R n i) = theta S n i := by
  simp only [theta,Algebra.TensorProduct.includeRight_apply,superCoefficientMap_tmul,
    map_one,exteriorCoefficientMap_ι,oddCoefficientMap_single]

@[simp] theorem superCoefficientMap_xi (i : Fin n) :
    superCoefficientMap R S (xi R n i) = xi S n i := by
  simp only [xi,Algebra.TensorProduct.includeRight_apply,superCoefficientMap_tmul,
    map_one,exteriorCoefficientMap_ι,oddCoefficientMap_single]

theorem superCoefficientMap_pairedCoefficients (β : Fin n → R)
    (a b : Fin n → PolynomialRing R n) (kind : MomentKind) (i : Fin n) :
    superCoefficientMap R S (pairedCoefficients β a b kind i) =
      pairedCoefficients (algebraMap R S ∘ β)
        (fun j ↦ MvPolynomial.map (algebraMap R S) (a j))
        (fun j ↦ MvPolynomial.map (algebraMap R S) (b j)) kind i := by
  cases kind <;>
    simp only [pairedCoefficients,superCoefficientMap_polynomial_smul,
      superCoefficientMap_theta,superCoefficientMap_xi,map_mul,map_one,
      MvPolynomial.map_C,Function.comp_def]

theorem superCoefficientMap_moment (φ : Fin n → PolynomialRing R n)
    (c : Fin n → SuperRing R n) (k : ℕ) :
    superCoefficientMap R S (moment φ c k) =
      moment (fun i ↦ MvPolynomial.map (algebraMap R S) (φ i))
        (fun i ↦ superCoefficientMap R S (c i)) k := by
  simp only [moment,map_sum,superCoefficientMap_polynomial_smul,map_pow]

variable [LinearOrder (OddIndex n)]

@[simp] theorem exteriorCoefficientMap_basis (T : Finset (OddIndex n)) :
    exteriorCoefficientMap R S ((Pi.basisFun R (OddIndex n)).ExteriorAlgebra T) =
      (Pi.basisFun S (OddIndex n)).ExteriorAlgebra T := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
  simp only [List.map_map,Function.comp_def,exteriorCoefficientMap_ι,
    Pi.basisFun_apply,oddCoefficientMap_single]

@[simp] theorem superCoefficientMap_basis (z : SuperMonomialIndex n) :
    superCoefficientMap R S (superMonomialBasis (K := R) z) =
      superMonomialBasis (K := S) z := by
  rw [superMonomialBasis_apply,superCoefficientMap_tmul,exteriorCoefficientMap_basis,
    superMonomialBasis_apply,MvPolynomial.map_monomial,map_one]

/-- Scalar extension of the actual superalgebra as a module.  The subsequent
formula identifies it with the canonical coefficient map on every element. -/
def superBaseChangeEquiv : S ⊗[R] SuperRing R n ≃ₗ[S] SuperRing S n :=
  ((superMonomialBasis (K := R) (n := n)).baseChange S).equiv
    (superMonomialBasis (K := S) (n := n)) (Equiv.refl _)

@[simp] theorem superBaseChangeEquiv_basis (z : SuperMonomialIndex n) :
    superBaseChangeEquiv R S (1 ⊗ₜ[R] superMonomialBasis (K := R) z) =
      superMonomialBasis (K := S) z := by
  rw [← Module.Basis.baseChange_apply,superBaseChangeEquiv,Module.Basis.equiv_apply]
  rfl

theorem superBaseChangeEquiv_eq_lift :
    (superBaseChangeEquiv R S (n := n)).toLinearMap =
      (superCoefficientMap R S).toLinearMap.liftBaseChange S := by
  apply ((superMonomialBasis (K := R) (n := n)).baseChange S).ext
  intro z
  simp only [Module.Basis.baseChange_apply,LinearEquiv.coe_coe,
    superBaseChangeEquiv_basis,LinearMap.liftBaseChange_tmul,one_smul,
    AlgHom.toLinearMap_apply,superCoefficientMap_basis]

@[simp] theorem superBaseChangeEquiv_tmul (s : S) (x : SuperRing R n) :
    superBaseChangeEquiv R S (s ⊗ₜ[R] x) = s • superCoefficientMap R S x := by
  exact LinearMap.congr_fun (superBaseChangeEquiv_eq_lift R S) (s ⊗ₜ[R] x)

end Algebra

end PaperVerification.Fermion
