module
public import Mathlib

/-! Theorem 8.1: initial ideals and an equivariant degeneration of the two-fermion quotient. -/
@[expose] public section
attribute [-instance] MvPolynomial.instModuleSelf MvPolynomial.instModule
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PalomarFermion
universe uDictionary
public theorem coefficientIdentityInvPair {R : Type uDictionary} [CommRing R] : RingHomInvPair (RingHom.id R) (RingHom.id R) := by sorry
public theorem coefficientCommutativeIdentityInvPair {R : Type uDictionary} [hR : CommRing R] : @RingHomInvPair R R hR.toCommSemiring.toSemiring hR.toCommSemiring.toSemiring (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) := by sorry
public theorem coefficientIdentitySurjective {R : Type uDictionary} [CommRing R] : RingHomSurjective (RingHom.id R) := by sorry
public theorem coefficientCommutativeIdentitySurjective {R : Type uDictionary} [hR : CommRing R] : @RingHomSurjective R R hR.toCommSemiring.toSemiring hR.toCommSemiring.toSemiring (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) := by sorry
public theorem finiteCoordinates (n : ℕ) : Finite (Fin n) := by sorry
public theorem finiteOddCoordinates (n : ℕ) : Finite (Fin n ⊕ Fin n) := by sorry
attribute [instance 2000] coefficientIdentityInvPair coefficientIdentitySurjective
attribute [instance 2100] coefficientCommutativeIdentityInvPair coefficientCommutativeIdentitySurjective finiteCoordinates finiteOddCoordinates
universe uCoordinateModule uCoordinateIndex
public abbrev coordinates {R : Type uDictionary} [CommRing R] {M : Type uCoordinateModule} {I : Type uCoordinateIndex} [AddCommGroup M] [Module R M] (b : Module.Basis I R M) : M →ₗ[R] (I →₀ R) :=
  @LinearEquiv.toLinearMap R R _ _ (RingHom.id R) (RingHom.id R)
    (coefficientCommutativeIdentityInvPair (R := R)) (coefficientCommutativeIdentityInvPair (R := R))
    M (I →₀ R) _ _ _ _ b.repr
@[simp] public theorem coordinates_apply {R : Type uDictionary} [CommRing R] {M : Type uCoordinateModule} {I : Type uCoordinateIndex} [AddCommGroup M] [Module R M] (b : Module.Basis I R M) (x : M) : coordinates b x = b.repr x := by sorry
end PalomarFermion
namespace PaperVerification.Fermion.WeightRees
open scoped Classical BigOperators LaurentPolynomial
variable (K A : Type*) [CommRing K] [Ring A] [Algebra K A]
def parameterMap : Polynomial K →+* LaurentPolynomial A := Polynomial.toLaurent.comp (Polynomial.mapRingHom (algebraMap K A))
@[simp] theorem parameterMap_C (c : K) :
    parameterMap K A (Polynomial.C c)=algebraMap K (LaurentPolynomial A) c := by sorry
@[simp] theorem parameterMap_monomial (r : ℕ) (c : K) :
    parameterMap K A (Polynomial.monomial r c)=
      AddMonoidAlgebra.single (r : ℤ) (algebraMap K A c) := by sorry
theorem parameterMap_central (p : Polynomial K) (z : LaurentPolynomial A) : parameterMap K A p*z=z*parameterMap K A p := by sorry
scoped instance parameterAlgebra : Algebra (Polynomial K) (LaurentPolynomial A) :=
  (parameterMap K A).toAlgebra' (parameterMap_central K A)
open scoped PaperVerification.Fermion.WeightRees
scoped instance parameterTower : IsScalarTower K (Polynomial K) (LaurentPolynomial A) :=
  IsScalarTower.of_algebraMap_eq (fun c ↦ (parameterMap_C K A c).symm)
variable {K A}
variable {I : Type*} [Fintype I] (b : Module.Basis I K A) (weight : I → ℕ)
def shiftedBasisVector (i : I) : LaurentPolynomial A := AddMonoidAlgebra.single (-(weight i : ℤ)) (b i)
def span : Submodule (Polynomial K) (LaurentPolynomial A) := Submodule.span (Polynomial K) (Set.range (shiftedBasisVector b weight))
def Multiplicative : Prop := ∀ i j k,b.repr (b i*b j) k≠0 → weight i+weight j≤weight k
theorem one_mem_span : (1 : LaurentPolynomial A)∈span b weight := by sorry
theorem span_mul_mem (hmul : Multiplicative b weight) (x y : LaurentPolynomial A) (hx : x∈span b weight) (hy : y∈span b weight) :
  x*y∈span b weight := by sorry
def algebra (hmul : Multiplicative b weight) :
    Subalgebra (Polynomial K) (LaurentPolynomial A) where
  carrier := span b weight
  zero_mem' := (span b weight).zero_mem
  add_mem' := (span b weight).add_mem
  one_mem' := one_mem_span b weight
  mul_mem' := fun hx hy ↦ span_mul_mem b weight hmul _ _ hx hy
  algebraMap_mem' c := by
    change algebraMap (Polynomial K) (LaurentPolynomial A) c∈span b weight
    rw [Algebra.algebraMap_eq_smul_one]
    exact (span b weight).smul_mem c (one_mem_span b weight)
def algebraRing (hmul : Multiplicative b weight) : Ring (algebra b weight hmul) := (algebra b weight hmul).toRing
def algebraPolynomialAlgebra (hmul : Multiplicative b weight) : Algebra (Polynomial K) (algebra b weight hmul) := (algebra b weight
  hmul).algebra
def algebraBaseAlgebra (hmul : Multiplicative b weight) : Algebra K (algebra b weight hmul) := (algebra b weight hmul).algebra'
def algebraScalarTower (hmul : Multiplicative b weight) : IsScalarTower K (Polynomial K) (algebra b weight hmul) := inferInstance
end PaperVerification.Fermion.WeightRees
namespace PaperVerification.Fermion.BlockInitial
open scoped BigOperators
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  (b : Module.Basis J P M) (weight : J → ℕ)
def LowerBound (r : ℕ) (x : M) : Prop := ∀ j,PalomarFermion.coordinates b x j≠0 → r≤weight j
variable (q : M →ₗ[K] Q) (D : J → Type*) [∀ j,Fintype (D j)]
structure TriangularPresentation where
  polynomial : (j : J) → D j → P
  basis : Module.Basis (Sigma D) K Q
  basis_apply : ∀ z,basis z=q (polynomial z.1 z.2 • b z.1)
  test : J → M →ₗ[K] N
  diagonal : J → P →ₗ[K] N
  test_same : ∀ j p,test j (p • b j)=diagonal j p
  test_higher : ∀ j t,j≠t → weight j≤weight t → ∀ p : P,test j (p • b t)=0
  kill : ∀ j,q.ker≤(test j).ker
  independent : ∀ j,LinearIndependent K (fun e ↦ diagonal j (polynomial j e))
end PaperVerification.Fermion.BlockInitial
namespace PaperVerification.Fermion
section
open scoped BigOperators
open Polynomial
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {n : ℕ}
def moment (x : Fin n → R) (v : Fin n → M) (k : ℕ) : M := ∑ i, x i ^ k • v i
end
variable {R : Type*} [CommRing R]
variable {n : ℕ}
variable {A : Type*} [Ring A] [Algebra R A]
def momentIdeal {κ : Type*} (x : Fin n → R) (v : κ → Fin n → A) : TwoSidedIdeal A := TwoSidedIdeal.span (Set.range fun p : κ × ℕ ↦
  moment x (v p.1) p.2)
end
open scoped BigOperators TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
abbrev PolynomialRing := MvPolynomial (Fin n) K
abbrev OddIndex := Fin n ⊕ Fin n
abbrev OddModule := OddIndex n → K
theorem polynomialSelfCommute : SMulCommClass K (PolynomialRing K n) (PolynomialRing K n) := by sorry
theorem polynomialSelfTower : IsScalarTower K (PolynomialRing K n) (PolynomialRing K n) := by sorry
theorem exteriorSelfCommute : SMulCommClass K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by sorry
theorem exteriorSelfTower : IsScalarTower K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by sorry
attribute [instance 2100] polynomialSelfCommute polynomialSelfTower exteriorSelfCommute exteriorSelfTower
abbrev SuperRing := PolynomialRing K n ⊗[K] ExteriorAlgebra K (OddModule K n)
@[reducible] noncomputable instance superQuotientModule (I : TwoSidedIdeal (SuperRing K n)) :
    Module K I.ringCon.Quotient := by
  let q : SuperRing K n →+ I.ringCon.Quotient :=
    { toFun := fun x ↦ (x : I.ringCon.Quotient)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact Function.Surjective.module K q
    (fun x ↦ I.ringCon.mk'_surjective x) (fun _ _ ↦ rfl)
noncomputable def theta (i : Fin n) : SuperRing K n := Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι K (Pi.single (Sum.inl i)
  1))
noncomputable def xi (i : Fin n) : SuperRing K n := Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι K (Pi.single (Sum.inr i) 1))
inductive MomentKind
  | polynomial | theta | xi | mixed
  deriving DecidableEq
variable {K n}
noncomputable def pairedCoefficients (β : Fin n → K)
    (a b : Fin n → PolynomialRing K n) : MomentKind → Fin n → SuperRing K n
  | .polynomial, i => (MvPolynomial.C (β i) * a i * b i) • (1 : SuperRing K n)
  | .theta, i => b i • theta K n i
  | .xi, i => (MvPolynomial.C (β i) * a i) • xi K n i
  | .mixed, i => theta K n i * xi K n i
noncomputable def strictCoefficients (β : Fin n → K)
    (φ : Fin n → PolynomialRing K n) : MomentKind → Fin n → SuperRing K n
  | .polynomial, i => (MvPolynomial.C (β i) * φ i) • (1 : SuperRing K n)
  | .theta, i => theta K n i
  | .xi, i => (MvPolynomial.C (β i) : PolynomialRing K n) • xi K n i
  | .mixed, i => theta K n i * xi K n i
noncomputable abbrev strictIdeal (β : Fin n → K) (φ : Fin n → PolynomialRing K n) : TwoSidedIdeal (SuperRing K n) := momentIdeal φ
  (strictCoefficients β φ)
abbrev StrictQuotient (β : Fin n → K) (φ : Fin n → PolynomialRing K n) := (strictIdeal β φ).ringCon.Quotient
def AllowedWeights (β : Fin n → K) : Prop := IsUnit (n.factorial : K) ∧ ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)
def monomialWeight (r : Fin n → ℕ) (e : Fin n →₀ ℕ) : ℚ := ∑ i, (e i : ℚ) / (r i : ℚ)
def HasHighestPower (r : Fin n → ℕ) (p : PolynomialRing K n) (i : Fin n) (d : ℕ) : Prop := p.coeff (Finsupp.single i d) = 1 ∧ ∀ e ∈
  p.support, e ≠ Finsupp.single i d → monomialWeight r e < (d : ℚ) / (r i : ℚ)
structure PairedData where
  positive_n : 0 < n
  s : ℕ
  positive_s : 0 < s
  r : Fin n → ℕ
  u : Fin n → ℕ
  v : Fin n → ℕ
  positive_r : ∀ i, 0 < r i
  degree_split : ∀ i, u i + v i = r i * s
  beta : Fin n → K
  allowed_weights : AllowedWeights beta
  phi : Fin n → PolynomialRing K n
  a : Fin n → PolynomialRing K n
  b : Fin n → PolynomialRing K n
  highest_phi : ∀ i, HasHighestPower r (phi i) i (r i)
  highest_a : ∀ i, HasHighestPower r (a i) i (u i)
  highest_b : ∀ i, HasHighestPower r (b i) i (v i)
structure StrictData where
  positive_n : 0 < n
  r : Fin n → ℕ
  positive_r : ∀ i, 0 < r i
  beta : Fin n → K
  allowed_weights : AllowedWeights beta
  phi : Fin n → PolynomialRing K n
  highest_phi : ∀ i, HasHighestPower r (phi i) i (r i)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Exterior
open scoped BigOperators
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
def modeRank : Fin n ⊕ Fin n → ℕ
  | .inl i => i.val
  | .inr i => n + i.val
theorem modeRank_injective : Function.Injective (modeRank (n := n)) := by sorry
def modeIndex : OddIndex n → Fin n
  | .inl i => i
  | .inr i => i
def multiplicityModeWeight (j : OddIndex n) : ℕ := 3^(modeIndex j).val
def multiplicityWordWeight (T : Finset (OddIndex n)) : ℕ := ∑ j ∈ T,multiplicityModeWeight j
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion.Newton
open MvPolynomial
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
abbrev RectangleIndex (h : Fin n → ℕ) := {a : Fin n →₀ ℕ // ∀ i, a i < h i}
theorem rectangleForwardBounds (h : Fin n → ℕ) (a : RectangleIndex h) : ∀ i, a.val i < h i := by sorry
theorem rectangleBackwardBounds (h : Fin n → ℕ) (a : ∀ i, Fin (h i)) : ∀ i, Finsupp.equivFunOnFinite.symm (fun j => (a j).val) i < h i := by sorry
def rectangleForward (h : Fin n → ℕ) (a : RectangleIndex h) : ∀ i, Fin (h i) := fun i => ⟨a.val i,rectangleForwardBounds h a i⟩
def rectangleBackward (h : Fin n → ℕ) (a : ∀ i, Fin (h i)) : RectangleIndex h := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val),rectangleBackwardBounds h a⟩
theorem rectangleLeftInverse (h : Fin n → ℕ) : Function.LeftInverse (rectangleBackward h) (rectangleForward h) := by sorry
theorem rectangleRightInverse (h : Fin n → ℕ) : Function.RightInverse (rectangleBackward h) (rectangleForward h) := by sorry
 def rectangleIndexEquiv (h : Fin n → ℕ) : RectangleIndex h ≃ (∀ i : Fin n, Fin (h i)) where
  toFun := rectangleForward h
  invFun := rectangleBackward h
  left_inv := rectangleLeftInverse h
  right_inv := rectangleRightInverse h
instance rectangleIndex_fintype (h : Fin n → ℕ) : Fintype (RectangleIndex h) :=
  Fintype.ofEquiv _ (rectangleIndexEquiv h).symm
end PaperVerification.Fermion.Newton
namespace PaperVerification.Fermion.Exterior
def interleavedOddRank {n : ℕ} : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun i => 2 * i.val + 1) (fun i => 2 * i.val)
theorem interleavedOddRank_injective (n : ℕ) : Function.Injective (@interleavedOddRank n) := by sorry
def interleavedOddOrder (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) := LinearOrder.lift' interleavedOddRank (interleavedOddRank_injective n)
def pairedPrefix (n i : ℕ) : Finset (Fin n ⊕ Fin n) := (Finset.univ.filter (fun j : Fin n ↦ j.val < i)).disjSum (Finset.univ.filter
  (fun j : Fin n ↦ j.val < i))
open scoped BigOperators
open Polynomial
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
local instance FermionHarmonicEndpoint_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicEndpoint_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicEndpoint_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicEndpoint_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicEndpoint_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicEndpoint_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq
def wordHeight (T : Finset (Fin n ⊕ Fin n)) (i : ℕ) : ℕ := i - (T ∩ pairedPrefix n i).card
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
section
open scoped BigOperators
open MvPolynomial Exterior
variable {K : Type*} [Field K] {n : ℕ}
local instance FermionPowerHarmonicBound_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionPowerHarmonicBound_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionPowerHarmonicBound_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionPowerHarmonicBound_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionPowerHarmonicBound_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionPowerHarmonicBound_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq
def ValidWord (T : Finset (Fin n ⊕ Fin n)) : Prop := ∀ i ≤ n, (T ∩ pairedPrefix n i).card ≤ i
end
open scoped TensorProduct BigOperators
variable {K : Type*} [CommRing K] {n : ℕ}
variable [LinearOrder (OddIndex n)]
def superPolynomialBasis : Module.Basis (Finset (OddIndex n)) (PolynomialRing K n) (SuperRing K n) := ((Pi.basisFun K (OddIndex
  n)).ExteriorAlgebra).baseChange (PolynomialRing K n)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Universal
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
open scoped BigOperators
inductive Kind
  | phi
  | left
  | right
  deriving DecidableEq, Fintype
variable {K : Type*} [CommRing K] {n : ℕ}
def degree (d : PairedData (K := K) (n := n)) : Kind → Fin n → ℕ
  | .phi,i => d.r i
  | .left,i => d.u i
  | .right,i => d.v i
def input (d : PairedData (K := K) (n := n)) : Kind → Fin n → PolynomialRing K n
  | .phi,i => d.phi i
  | .left,i => d.a i
  | .right,i => d.b i
def lowerSupport (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (input d k i).support.erase (Finsupp.single i (degree d k i))
abbrev Variables (d : PairedData (K := K) (n := n)) := Fin n ⊕ (Σ k : Kind, Σ i : Fin n, {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i})
abbrev Coefficients (d : PairedData (K := K) (n := n)) := MvPolynomial (Variables d) ℤ
def beta (d : PairedData (K := K) (n := n)) (i : Fin n) : Coefficients d := X (.inl i)
end PaperVerification.Fermion.Universal
namespace PaperVerification.Fermion
section
open MvPolynomial
variable {R : Type*} [CommRing R] {n : ℕ}
theorem highestPower_X_pow (r : Fin n → ℕ) (i : Fin n) (e : ℕ) : HasHighestPower r (X i^e : PolynomialRing R n) i e := by sorry
end
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Newton
open scoped BigOperators
variable {n : ℕ}
local instance FermionStrictPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
def strictWordBoxBounds (r : Fin n → ℕ) (T : Finset (OddIndex n)) (i : Fin n) : ℕ := r i*wordHeight T (i.val+1)
def StrictWordPolynomialIndex (r : Fin n → ℕ) (T : Finset (OddIndex n)) := {a : RectangleIndex (strictWordBoxBounds r T) // ValidWord
  T}
instance strictWordPolynomialIndex_fintype (r : Fin n → ℕ) (T : Finset (OddIndex n)) :
    Fintype (StrictWordPolynomialIndex r T) := by
  classical
  unfold StrictWordPolynomialIndex
  infer_instance
abbrev StrictPowerIndex (r : Fin n → ℕ) := Sigma (StrictWordPolynomialIndex r)
end
section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Newton
open scoped BigOperators TensorProduct
section
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionStrictCoupledIndependence_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictCoupledClasses (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) : StrictQuotient d.beta d.phi := (strictIdeal
  d.beta d.phi).ringCon.mkₐ R (monomial z.2.val.val 1 ⊗ₜ[R] (Pi.basisFun R (OddIndex n)).ExteriorAlgebra z.1)
end
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictCoupledIndependence_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
theorem strictCoupledClasses_linearIndependent (d : StrictData (K := F) (n := n)) : LinearIndependent F (strictCoupledClasses d) := by
  sorry
end
section
set_option backward.isDefEq.respectTransparency false
section
open Exterior Newton
open scoped BigOperators
variable {n : ℕ}
local instance FermionStrictIndexRecursion_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
theorem card_strictPowerIndex (r : Fin n → ℕ) (hn : 0<n) : Fintype.card (StrictPowerIndex r)=2^(n-1)*(∏ i,r i)*n.factorial := by sorry
end
open scoped BigOperators
section
variable {R : Type*} [CommRing R] {n : ℕ}
theorem strictCoupled_quotient_finite (d : StrictData (K := R) (n := n)) : Module.Finite R (StrictQuotient d.beta d.phi) := by sorry
end
variable {F : Type*} [Field F] {n : ℕ}
theorem strictCoupled_finrank (d : StrictData (K := F) (n := n)) : Module.finrank F (StrictQuotient d.beta d.phi)=2^(n-1)*(∏ i,d.r
  i)*n.factorial := by sorry
end
open Exterior
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictCoupledBasis_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictCoupledBasis (d : StrictData (K := F) (n := n)) :
    Module.Basis (StrictPowerIndex d.r) F (StrictQuotient d.beta d.phi) := by
  letI := strictCoupled_quotient_finite d
  exact basisOfLinearIndependentOfCardEqFinrank' (strictCoupledClasses d)
    (strictCoupledClasses_linearIndependent d)
    ((card_strictPowerIndex d.r d.positive_n).trans (strictCoupled_finrank d).symm)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.BlockInitial
open scoped BigOperators
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  {b : Module.Basis J P M} {weight : J → ℕ} {q : M →ₗ[K] Q}
  {D : J → Type*} [∀ j,Fintype (D j)]
  (h : TriangularPresentation (N := N) b weight q D)
def lowerSubmodule (b : Module.Basis J P M) (weight : J → ℕ) (r : ℕ) : Submodule P M where
  carrier := {x | LowerBound b weight r x}
  zero_mem' := by intro i hi; exact (hi (by simp)).elim
  add_mem' := by
    intro x y hx hy i hi
    by_cases hxi : PalomarFermion.coordinates b x i=0
    · apply hy i
      simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
    · exact hx i hxi
  smul_mem' := by
    intro c x hx i hi
    apply hx i
    intro hz
    exact hi (by simp only [map_smul,Finsupp.smul_apply,hz,smul_zero])
end PaperVerification.Fermion.BlockInitial
namespace PaperVerification.Fermion.WeightRees
open scoped BigOperators LaurentPolynomial PaperVerification.Fermion.WeightRees
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (weight : I → ℕ)
theorem mem_algebra_iff_filtration (hmul : Multiplicative b weight) (z : LaurentPolynomial A) : z∈algebra b weight hmul ↔ ∀ e,z.coeff
  e∈BlockInitial.lowerSubmodule b weight (-e).toNat := by sorry
end PaperVerification.Fermion.WeightRees
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictWeightRees_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictBasisMultiplicityWeight (d : StrictData (K := F) (n := n)) (z : StrictPowerIndex d.r) : ℕ := multiplicityWordWeight z.1
def strictMultiplicityFiltration (d : StrictData (K := F) (n := n)) (r : ℕ) : Submodule F (StrictQuotient d.beta d.phi) :=
  ((BlockInitial.lowerSubmodule (superPolynomialBasis (K := F)) multiplicityWordWeight r).restrictScalars F).map (((strictIdeal d.beta
  d.phi).ringCon.mkₐ F).toLinearMap)
theorem strictBasisMultiplicityWeight_multiplicative (d : StrictData (K := F) (n := n)) : WeightRees.Multiplicative (K := F) (A :=
  StrictQuotient d.beta d.phi) (I := StrictPowerIndex d.r) (strictCoupledBasis d) (strictBasisMultiplicityWeight d) := by sorry
def StrictMultiplicityRees (d : StrictData (K := F) (n := n)) := WeightRees.algebra (K := F) (A := StrictQuotient d.beta d.phi) (I :=
  StrictPowerIndex d.r) (strictCoupledBasis d) (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d)
attribute [local instance] FermionStrictWeightRees_localInst_1
set_option maxHeartbeats 1000000
instance strictMultiplicityReesRing (d : StrictData (K := F) (n := n)) :
    Ring (StrictMultiplicityRees d) := by
  let r := WeightRees.algebraRing (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact r
instance strictMultiplicityReesPolynomialAlgebra (d : StrictData (K := F) (n := n)) :
    Algebra (Polynomial F) (StrictMultiplicityRees d) := by
  let a := WeightRees.algebraPolynomialAlgebra (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact a
attribute [local instance] FermionStrictWeightRees_localInst_1
@[reducible] instance strictMultiplicityReesPolynomialModule
    (d : StrictData (K := F) (n := n)) : Module (Polynomial F) (StrictMultiplicityRees d) :=
  @Algebra.toModule (Polynomial F) (StrictMultiplicityRees d) _ _
    (strictMultiplicityReesPolynomialAlgebra d)
attribute [local instance] FermionStrictWeightRees_localInst_1
set_option maxHeartbeats 1000000
instance strictMultiplicityReesFieldAlgebra (d : StrictData (K := F) (n := n)) :
    Algebra F (StrictMultiplicityRees d) := by
  let a := WeightRees.algebraBaseAlgebra (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact a
attribute [local instance] FermionStrictWeightRees_localInst_1
@[reducible] instance strictMultiplicityReesFieldModule
    (d : StrictData (K := F) (n := n)) : Module F (StrictMultiplicityRees d) :=
  @Algebra.toModule F (StrictMultiplicityRees d) _ _
    (strictMultiplicityReesFieldAlgebra d)
attribute [local instance] FermionStrictWeightRees_localInst_1
set_option maxHeartbeats 1000000
instance strictMultiplicityReesScalarTower (d : StrictData (K := F) (n := n)) :
    IsScalarTower F (Polynomial F) (StrictMultiplicityRees d) := by
  let h := WeightRees.algebraScalarTower (K := F) (A := StrictQuotient d.beta d.phi)
      (I := StrictPowerIndex d.r)
      (strictCoupledBasis d) (strictBasisMultiplicityWeight d)
      (strictBasisMultiplicityWeight_multiplicative d)
  exact h
end PaperVerification.Fermion
namespace PaperVerification.Fermion.DescendingAlgebra
open scoped DirectSum
universe u w
variable (R : Type u) (A : Type w) [CommRing R] [Ring A] [Algebra R A]
structure Filtration where
  piece : ℕ → Submodule R A
  antitone : Antitone piece
  one_mem : (1 : A) ∈ piece 0
  mul_mem : ∀ {i j : ℕ} {x y : A}, x ∈ piece i → y ∈ piece j → x*y ∈ piece (i+j)
end PaperVerification.Fermion.DescendingAlgebra
namespace PaperVerification.Fermion.DescendingBasis
open scoped Classical BigOperators DirectSum
open DescendingAlgebra
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (w : I → ℕ) (hmul : WeightRees.Multiplicative b w)
section
include hmul
theorem tail_mul {d e : ℕ} {x y : A} (hx : x∈BlockInitial.lowerSubmodule b w d) (hy : y∈BlockInitial.lowerSubmodule b w e) :
  x*y∈BlockInitial.lowerSubmodule b w (d+e) := by sorry
end
def filtration : DescendingAlgebra.Filtration K A where
  piece := BlockInitial.lowerSubmodule b w
  antitone := fun d e h x hx i hi ↦ h.trans (hx i hi)
  one_mem := fun i hi ↦ Nat.zero_le _
  mul_mem := tail_mul b w hmul
end PaperVerification.Fermion.DescendingBasis
namespace PaperVerification.Fermion
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators DirectSum
open MvPolynomial Exterior
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityAssociatedGraded_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
abbrev strictMultiplicityDescendingFiltration (d : StrictData (K := F) (n := n)) : DescendingAlgebra.Filtration F (StrictQuotient
  d.beta d.phi) := DescendingBasis.filtration (K := F) (A := StrictQuotient d.beta d.phi) (strictCoupledBasis d)
  (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d)
end
section
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B]
theorem ringCon_le_ker_of_kills (I : TwoSidedIdeal A) (f : A →ₐ[R] B) (hf : ∀ a ∈ I, f a = 0) : I.ringCon ≤ RingCon.ker f.toRingHom :=
  by sorry
theorem quotientMk_eq_zero_of_mem (I : TwoSidedIdeal A) (a : A) (ha : a ∈ I) : I.ringCon.mkₐ R a = 0 := by sorry
end
open scoped TensorProduct Classical
variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
def twoSidedQuotientEquiv (e : A ≃ₐ[R] B)
    (I : TwoSidedIdeal A) (J : TwoSidedIdeal B)
    (he : ∀ a∈I,e a∈J) (hei : ∀ b∈J,e.symm b∈I) :
    I.ringCon.Quotient ≃ₐ[R] J.ringCon.Quotient := by
  let qI : A →ₐ[R] I.ringCon.Quotient := I.ringCon.mkₐ R
  let qJ : B →ₐ[R] J.ringCon.Quotient := J.ringCon.mkₐ R
  let f : I.ringCon.Quotient →ₐ[R] J.ringCon.Quotient :=
    I.ringCon.liftₐ (qJ.comp e.toAlgHom)
      (ringCon_le_ker_of_kills I (qJ.comp e.toAlgHom) (by
        intro a ha
        exact quotientMk_eq_zero_of_mem (R := R) J (e a) (he a ha)))
  let g : J.ringCon.Quotient →ₐ[R] I.ringCon.Quotient :=
    J.ringCon.liftₐ (qI.comp e.symm.toAlgHom)
      (ringCon_le_ker_of_kills J (qI.comp e.symm.toAlgHom) (by
        intro b hb
        exact quotientMk_eq_zero_of_mem (R := R) I (e.symm b) (hei b hb)))
  exact AlgEquiv.ofAlgHom f g
    (by
      apply RingCon.Quotient.hom_extₐ
      apply AlgHom.ext
      intro b
      change qJ (e (e.symm b))=qJ b
      rw [AlgEquiv.apply_symm_apply])
    (by
      apply RingCon.Quotient.hom_extₐ
      apply AlgHom.ext
      intro a
      change qI (e.symm (e a))=qI a
      rw [AlgEquiv.symm_apply_apply])
end PaperVerification.Fermion
namespace PaperVerification.Fermion.ColorAction
set_option backward.isDefEq.respectTransparency false
section
open scoped BigOperators TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
abbrev ColorMatrix (R : Type*) := Matrix (Fin 2) (Fin 2) R
def linear (A : ColorMatrix R) : OddModule R n →ₗ[R] OddModule R n where
  toFun v := Sum.elim
    (fun i => A 0 0 * v (.inl i) + A 0 1 * v (.inr i))
    (fun i => A 1 0 * v (.inl i) + A 1 1 * v (.inr i))
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> ring
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply] <;> ring
def ambient (A : ColorMatrix R) : SuperRing R n →ₐ[PolynomialRing R n] SuperRing R n := Algebra.TensorProduct.map (AlgHom.id
  (PolynomialRing R n) (PolynomialRing R n)) (ExteriorAlgebra.map (linear A))
@[simp] theorem ambient_one :
    ambient (n := n) (1 : ColorMatrix R) = AlgHom.id (PolynomialRing R n) _ := by sorry
theorem ambient_mul (A B : ColorMatrix R) : ambient (n := n) (A * B) = (ambient A).comp (ambient B) := by sorry
theorem ambient_preserves_strictIdeal (A : ColorMatrix R) (phi : Fin n → PolynomialRing R n) {z : SuperRing R n} (hz : z ∈ strictIdeal
  (fun _ => 1) phi) : ambient A z ∈ strictIdeal (fun _ => 1) phi := by sorry
def ambientEquiv (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    SuperRing R n ≃ₐ[PolynomialRing R n] SuperRing R n :=
  AlgEquiv.ofAlgHom (ambient g.val) (ambient g.inv)
    (by rw [← ambient_mul, g.val_inv, ambient_one])
    (by rw [← ambient_mul, g.inv_val, ambient_one])
def quotientEquiv (g : Matrix.GeneralLinearGroup (Fin 2) R) (phi : Fin n → PolynomialRing R n) : StrictQuotient (fun _ => (1 : R)) phi
  ≃ₐ[R] StrictQuotient (fun _ => (1 : R)) phi := twoSidedQuotientEquiv ((ambientEquiv g).restrictScalars R) (strictIdeal (fun _ => 1)
  phi) (strictIdeal (fun _ => 1) phi) (fun _ hz => ambient_preserves_strictIdeal g.val phi hz) (fun _ hz =>
  ambient_preserves_strictIdeal g.inv phi hz)
@[simp] theorem quotientEquiv_one (phi : Fin n → PolynomialRing R n) :
    quotientEquiv (1 : Matrix.GeneralLinearGroup (Fin 2) R) phi = 1 := by sorry
theorem quotientEquiv_mul (g h : Matrix.GeneralLinearGroup (Fin 2) R) (phi : Fin n → PolynomialRing R n) : quotientEquiv (g*h) phi =
  quotientEquiv g phi * quotientEquiv h phi := by sorry
def quotientAction (phi : Fin n → PolynomialRing R n) :
    Matrix.GeneralLinearGroup (Fin 2) R →*
      (StrictQuotient (fun _ => (1 : R)) phi ≃ₐ[R]
        StrictQuotient (fun _ => (1 : R)) phi) where
  toFun g := quotientEquiv g phi
  map_one' := quotientEquiv_one phi
  map_mul' g h := quotientEquiv_mul g h phi
end
open scoped Classical BigOperators TensorProduct
open Exterior
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionColorFiltration_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def quotientFiltration (phi : Fin n → PolynomialRing R n) (r : ℕ) : Submodule R (StrictQuotient (fun _ => (1 : R)) phi) :=
  ((BlockInitial.lowerSubmodule (superPolynomialBasis (K := R)) multiplicityWordWeight r).restrictScalars R).map (((strictIdeal (fun _
  => (1 : R)) phi).ringCon.mkₐ R).toLinearMap)
theorem quotientEquiv_filtration_iff (g : Matrix.GeneralLinearGroup (Fin 2) R) (phi : Fin n → PolynomialRing R n) (r : ℕ) (z :
  StrictQuotient (fun _ => (1 : R)) phi) : quotientEquiv g phi z ∈ quotientFiltration phi r ↔ z ∈ quotientFiltration phi r := by sorry
end PaperVerification.Fermion.ColorAction
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance FermionTypeAMultiplicity_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance typeAMultiplicityDecidableEq : DecidableEq (OddIndex n) :=
  (interleavedOddOrder n).toDecidableEq
def data (hn : 0<n) : StrictData (K := F) (n := n) where
  positive_n := hn
  r := fun _ ↦ 1
  positive_r := fun _ ↦ Nat.zero_lt_one
  beta := fun _ ↦ 1
  allowed_weights := by
    refine ⟨isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),?_⟩
    intro U hU
    have hc : (U.card : F)≠0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hU)
    simpa only [Finset.sum_const,nsmul_one] using isUnit_iff_ne_zero.mpr hc
  phi := fun i ↦ X i
  highest_phi := fun i ↦ by simpa only [pow_one] using highestPower_X_pow (fun _ : Fin n ↦ 1) i 1
end PaperVerification.Fermion.TypeA
namespace PaperVerification.Fermion.WeightRees
open scoped Classical BigOperators LaurentPolynomial PaperVerification.Fermion.WeightRees
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
def parameterLaurentEquiv (e : A ≃ₐ[K] A) :
    LaurentPolynomial A ≃ₐ[Polynomial K] LaurentPolynomial A where
  __ := (AddMonoidAlgebra.mapAlgEquiv K ℤ e).toRingEquiv
  commutes' p := by
    change AddMonoidAlgebra.mapAlgHom ℤ e.toAlgHom (parameterMap K A p)=parameterMap K A p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial r c =>
        rw [parameterMap_monomial,AddMonoidAlgebra.mapAlgHom_single]
        exact congrArg (AddMonoidAlgebra.single (r : ℤ)) (e.commutes c)
@[simp] theorem parameterLaurentEquiv_coeff (e : A ≃ₐ[K] A)
    (z : LaurentPolynomial A) (r : ℤ) :
    (parameterLaurentEquiv e z).coeff r=e (z.coeff r) := by sorry
@[simp] theorem parameterLaurentEquiv_symm_coeff (e : A ≃ₐ[K] A)
    (z : LaurentPolynomial A) (r : ℤ) :
    ((parameterLaurentEquiv e).symm z).coeff r=e.symm (z.coeff r) := by sorry
variable (b : Module.Basis I K A) (weight : I → ℕ) (hmul : Multiplicative b weight)
def filtrationEquiv (e : A ≃ₐ[K] A)
    (he : ∀ r x, e x ∈ BlockInitial.lowerSubmodule b weight r ↔
      x ∈ BlockInitial.lowerSubmodule b weight r) :
    algebra b weight hmul ≃ₐ[Polynomial K] algebra b weight hmul where
  toFun z := ⟨parameterLaurentEquiv e z,by
    have hz := z.property
    rw [mem_algebra_iff_filtration] at hz ⊢
    intro r
    rw [parameterLaurentEquiv_coeff]
    exact (he _ _).mpr (hz r)⟩
  invFun z := ⟨(parameterLaurentEquiv e).symm z,by
    have hz := z.property
    rw [mem_algebra_iff_filtration] at hz ⊢
    intro r
    rw [parameterLaurentEquiv_symm_coeff]
    apply (he _ _).mp
    rw [e.apply_symm_apply]
    exact hz r⟩
  left_inv z := by
    apply Subtype.ext
    exact (parameterLaurentEquiv e).symm_apply_apply z
  right_inv z := by
    apply Subtype.ext
    exact (parameterLaurentEquiv e).apply_symm_apply z
  map_mul' x y := Subtype.ext ((parameterLaurentEquiv e).map_mul x y)
  map_add' x y := Subtype.ext ((parameterLaurentEquiv e).map_add x y)
  commutes' p := Subtype.ext ((parameterLaurentEquiv e).commutes p)
@[simp] theorem filtrationEquiv_coeff (e : A ≃ₐ[K] A)
    (he : ∀ r x, e x ∈ BlockInitial.lowerSubmodule b weight r ↔
      x ∈ BlockInitial.lowerSubmodule b weight r)
    (z : algebra b weight hmul) (r : ℤ) :
    ((filtrationEquiv b weight hmul e he z : algebra b weight hmul) :
      LaurentPolynomial A).coeff r=e ((z : LaurentPolynomial A).coeff r) := by sorry
variable {G : Type*} [Monoid G]
def filtrationAction (rho : G →* (A ≃ₐ[K] A))
    (hrho : ∀ g r x, rho g x ∈ BlockInitial.lowerSubmodule b weight r ↔
      x ∈ BlockInitial.lowerSubmodule b weight r) :
    G →* (algebra b weight hmul ≃ₐ[Polynomial K] algebra b weight hmul) where
  toFun g := filtrationEquiv b weight hmul (rho g) (hrho g)
  map_one' := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    apply LaurentPolynomial.ext
    intro r
    simp only [filtrationEquiv_coeff,map_one,AlgEquiv.one_apply]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    apply LaurentPolynomial.ext
    intro r
    simp only [AlgEquiv.mul_apply,filtrationEquiv_coeff,map_mul]
end PaperVerification.Fermion.WeightRees
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
section
open scoped PaperVerification.Fermion.WeightRees
open MvPolynomial
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
theorem colorFiltration_eq_basisTail (hn : 0<n) (r : ℕ) : ColorAction.quotientFiltration (fun i : Fin n ↦ (X i : PolynomialRing F n)) r
  = BlockInitial.lowerSubmodule (strictCoupledBasis (data (F := F) hn)) (strictBasisMultiplicityWeight (data hn)) r := by sorry
set_option maxHeartbeats 1000000
def reesColorAction (hn : 0<n) :
    Matrix.GeneralLinearGroup (Fin 2) F →*
      (StrictMultiplicityRees (data (F := F) hn) ≃ₐ[Polynomial F]
        StrictMultiplicityRees (data (F := F) hn)) := by
  let f := WeightRees.filtrationAction (K := F) (A := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i))
      (strictCoupledBasis (data hn))
      (strictBasisMultiplicityWeight (data hn))
      (strictBasisMultiplicityWeight_multiplicative (data hn))
      (ColorAction.quotientAction (fun i : Fin n ↦ (X i : PolynomialRing F n)))
      (fun g r x ↦ by
        rw [←colorFiltration_eq_basisTail hn r]
        exact ColorAction.quotientEquiv_filtration_iff g _ r x)
  exact f
end
open scoped Classical BigOperators TensorProduct DirectSum
  PaperVerification.Fermion.WeightRees
open MvPolynomial Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance theoremEightOneOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
set_option maxHeartbeats 1000000
theorem palomarColorFamily (hn : 0<n) : (∀ r : ℕ, (strictMultiplicityDescendingFiltration (data (F := F) hn)).piece r=
  strictMultiplicityFiltration (data (F := F) hn) r) ∧ (∀ z : LaurentPolynomial (StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X
  i)), z∈StrictMultiplicityRees (data (F := F) hn) ↔ ∀ e,z.coeff e∈strictMultiplicityFiltration (data (F := F) hn) (-e).toNat) ∧
  (Module.Finite (Polynomial F) (StrictMultiplicityRees (data (F := F) hn)) ∧ Module.Free (Polynomial F) (StrictMultiplicityRees (data
  (F := F) hn)) ∧ Module.Flat (Polynomial F) (StrictMultiplicityRees (data (F := F) hn))) ∧ (∀ (g : Matrix.GeneralLinearGroup (Fin 2)
  F) (z : StrictMultiplicityRees (data (F := F) hn)) (r : ℤ), (reesColorAction hn g z).val.coeff r= ColorAction.quotientEquiv g (fun i
  ↦ X i) (z.val.coeff r)) := by sorry
end PaperVerification.Fermion.TypeA
