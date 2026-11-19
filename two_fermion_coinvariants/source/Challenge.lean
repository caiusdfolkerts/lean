module
public import Mathlib
/-!
# Weighted two-fermion quotients over every commutative ring
Theorems1.1/1.2 retain both prescribed monomial bases and ranks, actual
exterior-degree/Hilbert and associated-graded clauses, and the genuine finite-free
flat homogenized family with both fibers. Coupled lower terms, factorial units,
every nonempty weight sum and the zero ring remain in the exact hypotheses.
-/
@[expose] public section
-- Match the measured original canonical polynomial scalar action.
attribute [-instance] MvPolynomial.instModuleSelf MvPolynomial.instModule
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PalomarFermion
universe uDictionary
/-- Exact identity inverse-pair law at the ring dictionary. -/
public theorem coefficientIdentityInvPair {R : Type uDictionary} [CommRing R] : RingHomInvPair (RingHom.id R) (RingHom.id R) := by sorry
/-- Exact identity inverse-pair law at the commutative-semiring dictionary. -/
public theorem coefficientCommutativeIdentityInvPair {R : Type uDictionary} [hR : CommRing R] : @RingHomInvPair R R hR.toCommSemiring.toSemiring hR.toCommSemiring.toSemiring (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) := by sorry
/-- Exact identity-surjectivity law at the ring dictionary. -/
public theorem coefficientIdentitySurjective {R : Type uDictionary} [CommRing R] : RingHomSurjective (RingHom.id R) := by sorry
/-- Exact identity-surjectivity law at the commutative-semiring dictionary. -/
public theorem coefficientCommutativeIdentitySurjective {R : Type uDictionary} [hR : CommRing R] : @RingHomSurjective R R hR.toCommSemiring.toSemiring hR.toCommSemiring.toSemiring (@RingHom.id R hR.toCommSemiring.toSemiring.toNonAssocSemiring) := by sorry
/-- The primitive finite set of polynomial indices. -/
public theorem finiteCoordinates (n : ℕ) : Finite (Fin n) := by sorry
/-- The primitive finite set of the two separately labeled exterior families. -/
public theorem finiteOddCoordinates (n : ℕ) : Finite (Fin n ⊕ Fin n) := by sorry
attribute [instance 2000] coefficientIdentityInvPair coefficientIdentitySurjective
attribute [instance 2100] coefficientCommutativeIdentityInvPair coefficientCommutativeIdentitySurjective finiteCoordinates finiteOddCoordinates
universe uCoordinateModule uCoordinateIndex
/-- The same exact basis coordinates, with both identity inverse-pair projection arguments explicit. -/
public abbrev coordinates {R : Type uDictionary} [CommRing R] {M : Type uCoordinateModule} {I : Type uCoordinateIndex} [AddCommGroup M] [Module R M] (b : Module.Basis I R M) : M →ₗ[R] (I →₀ R) :=
  @LinearEquiv.toLinearMap R R _ _ (RingHom.id R) (RingHom.id R)
    (coefficientCommutativeIdentityInvPair (R := R)) (coefficientCommutativeIdentityInvPair (R := R))
    M (I →₀ R) _ _ _ _ b.repr
/-- Pointwise equality with the original imported basis coordinate accessor. -/
@[simp] public theorem coordinates_apply {R : Type uDictionary} [CommRing R] {M : Type uCoordinateModule} {I : Type uCoordinateIndex} [AddCommGroup M] [Module R M] (b : Module.Basis I R M) (x : M) : coordinates b x = b.repr x := by sorry
end PalomarFermion
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M] (b : Module.Basis I R M) (w : I → ℕ)
/-- Literal PaperVerification.Fermion.BasisFiltered.Bound; precise source and scope recorded in the extraction map. -/ def Bound (d : ℕ) (x : M) : Prop := ∀ i, PalomarFermion.coordinates b x i ≠ 0 → w i ≤ d
/-- Literal PaperVerification.Fermion.BasisFiltered.Homogeneous; precise source and scope recorded in the extraction map. -/ def Homogeneous (d : ℕ) (x : M) : Prop := ∀ i, PalomarFermion.coordinates b x i ≠ 0 → w i = d
/-- Literal PaperVerification.Fermion.BasisFiltered.bound_zero; precise source and scope recorded in the extraction map. -/ theorem bound_zero (d : ℕ) : Bound b w d 0 := by sorry
/-- Literal PaperVerification.Fermion.BasisFiltered.bound_add; precise source and scope recorded in the extraction map. -/ theorem bound_add {d : ℕ} {x y : M} (hx : Bound b w d x) (hy : Bound b w d y) : Bound b w d (x+y) := by sorry
/-- Literal PaperVerification.Fermion.BasisFiltered.bound_smul; precise source and scope recorded in the extraction map. -/ theorem bound_smul {d : ℕ} {x : M} (hx : Bound b w d x) (a : R) : Bound b w d (a • x) := by sorry
/-- Literal PaperVerification.Fermion.BasisFiltered.homogeneous_bound; precise source and scope recorded in the extraction map. -/ theorem homogeneous_bound {d : ℕ} {x : M} (hx : Homogeneous b w d x) : Bound b w d x := by sorry
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion
open scoped BigOperators
open Polynomial
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {n : ℕ}
/-- Literal PaperVerification.Fermion.moment; precise source and scope recorded in the extraction map. -/ def moment (x : Fin n → R) (v : Fin n → M) (k : ℕ) : M :=
  ∑ i, x i ^ k • v i
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open scoped BigOperators
open Polynomial
variable {R : Type*} [CommRing R]
variable {n : ℕ}
variable {A : Type*} [Ring A] [Algebra R A]
/-- Literal PaperVerification.Fermion.momentIdeal; precise source and scope recorded in the extraction map. -/ def momentIdeal {κ : Type*} (x : Fin n → R) (v : κ → Fin n → A) : TwoSidedIdeal A :=
  TwoSidedIdeal.span (Set.range fun p : κ × ℕ ↦ moment x (v p.1) p.2)
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open scoped BigOperators _root_.TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
/-- Literal PaperVerification.Fermion.PolynomialRing; precise source and scope recorded in the extraction map. -/ abbrev PolynomialRing := MvPolynomial (Fin n) K
/-- Literal PaperVerification.Fermion.OddIndex; precise source and scope recorded in the extraction map. -/ abbrev OddIndex := Fin n ⊕ Fin n
/-- Literal PaperVerification.Fermion.OddModule; precise source and scope recorded in the extraction map. -/ abbrev OddModule := OddIndex n → K
/-- Exact polynomial-factor scalar commutation at primitive K,n. -/
theorem polynomialSelfCommute : SMulCommClass K (PolynomialRing K n) (PolynomialRing K n) := by sorry
/-- Exact polynomial-factor scalar tower at primitive K,n. -/
theorem polynomialSelfTower : IsScalarTower K (PolynomialRing K n) (PolynomialRing K n) := by sorry
/-- Exact exterior-factor scalar commutation at primitive K,n. -/
theorem exteriorSelfCommute : SMulCommClass K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by sorry
/-- Exact exterior-factor scalar tower at primitive K,n. -/
theorem exteriorSelfTower : IsScalarTower K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by sorry
attribute [instance 2100] polynomialSelfCommute polynomialSelfTower exteriorSelfCommute exteriorSelfTower

/-- Literal PaperVerification.Fermion.SuperRing; precise source and scope recorded in the extraction map. -/ abbrev SuperRing := PolynomialRing K n ⊗[K] ExteriorAlgebra K (OddModule K n)
/-- Literal PaperVerification.Fermion.superQuotientModule; precise source and scope recorded in the extraction map. -/ @[reducible] noncomputable instance superQuotientModule (I : TwoSidedIdeal (SuperRing K n)) :
    Module K I.ringCon.Quotient := by
  let q : SuperRing K n →+ I.ringCon.Quotient :=
    { toFun := fun x ↦ (x : I.ringCon.Quotient)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact Function.Surjective.module K q
    (fun x ↦ I.ringCon.mk'_surjective x) (fun _ _ ↦ rfl)
/-- Literal PaperVerification.Fermion.theta; precise source and scope recorded in the extraction map. -/ noncomputable def theta (i : Fin n) : SuperRing K n :=
  Algebra.TensorProduct.includeRight
    (ExteriorAlgebra.ι K (Pi.single (Sum.inl i) 1))
/-- Literal PaperVerification.Fermion.xi; precise source and scope recorded in the extraction map. -/ noncomputable def xi (i : Fin n) : SuperRing K n :=
  Algebra.TensorProduct.includeRight
    (ExteriorAlgebra.ι K (Pi.single (Sum.inr i) 1))
/-- Literal PaperVerification.Fermion.MomentKind; precise source and scope recorded in the extraction map. -/
inductive MomentKind
  | polynomial | theta | xi | mixed
  deriving DecidableEq
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open scoped BigOperators _root_.TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
variable {K n}
/-- Literal PaperVerification.Fermion.pairedCoefficients; precise source and scope recorded in the extraction map. -/ noncomputable def pairedCoefficients (β : Fin n → K)
    (a b : Fin n → PolynomialRing K n) : MomentKind → Fin n → SuperRing K n
  | .polynomial, i => (MvPolynomial.C (β i) * a i * b i) • (1 : SuperRing K n)
  | .theta, i => b i • theta K n i
  | .xi, i => (MvPolynomial.C (β i) * a i) • xi K n i
  | .mixed, i => theta K n i * xi K n i
/-- Literal PaperVerification.Fermion.pairedIdeal; precise source and scope recorded in the extraction map. -/ noncomputable abbrev pairedIdeal (β : Fin n → K) (φ a b : Fin n → PolynomialRing K n) : TwoSidedIdeal (SuperRing K n) :=
  momentIdeal φ (pairedCoefficients β a b)
/-- Literal PaperVerification.Fermion.PairedQuotient; precise source and scope recorded in the extraction map. -/ abbrev PairedQuotient (β : Fin n → K) (φ a b : Fin n → PolynomialRing K n) :=
  (pairedIdeal β φ a b).ringCon.Quotient
/-- Literal PaperVerification.Fermion.strictCoefficients; precise source and scope recorded in the extraction map. -/ noncomputable def strictCoefficients (β : Fin n → K)
    (φ : Fin n → PolynomialRing K n) : MomentKind → Fin n → SuperRing K n
  | .polynomial, i => (MvPolynomial.C (β i) * φ i) • (1 : SuperRing K n)
  | .theta, i => theta K n i
  | .xi, i => (MvPolynomial.C (β i) : PolynomialRing K n) • xi K n i
  | .mixed, i => theta K n i * xi K n i
/-- Literal PaperVerification.Fermion.strictIdeal; precise source and scope recorded in the extraction map. -/ noncomputable abbrev strictIdeal (β : Fin n → K) (φ : Fin n → PolynomialRing K n) : TwoSidedIdeal (SuperRing K n) :=
  momentIdeal φ (strictCoefficients β φ)
/-- Literal PaperVerification.Fermion.StrictQuotient; precise source and scope recorded in the extraction map. -/ abbrev StrictQuotient (β : Fin n → K) (φ : Fin n → PolynomialRing K n) :=
  (strictIdeal β φ).ringCon.Quotient
/-- Literal PaperVerification.Fermion.AllowedWeights; precise source and scope recorded in the extraction map. -/ def AllowedWeights (β : Fin n → K) : Prop :=
  IsUnit (n.factorial : K) ∧
    ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)
/-- Literal PaperVerification.Fermion.monomialWeight; precise source and scope recorded in the extraction map. -/ def monomialWeight (r : Fin n → ℕ) (e : Fin n →₀ ℕ) : ℚ :=
  ∑ i, (e i : ℚ) / (r i : ℚ)
/-- Literal PaperVerification.Fermion.HasHighestPower; precise source and scope recorded in the extraction map. -/ def HasHighestPower (r : Fin n → ℕ) (p : PolynomialRing K n) (i : Fin n) (d : ℕ) : Prop :=
  p.coeff (Finsupp.single i d) = 1 ∧
    ∀ e ∈ p.support, e ≠ Finsupp.single i d →
      monomialWeight r e < (d : ℚ) / (r i : ℚ)
/-- Literal PaperVerification.Fermion.PairedData; precise source and scope recorded in the extraction map. -/ structure PairedData where
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
/-- Literal PaperVerification.Fermion.StrictData; precise source and scope recorded in the extraction map. -/ structure StrictData where
  positive_n : 0 < n
  r : Fin n → ℕ
  positive_r : ∀ i, 0 < r i
  beta : Fin n → K
  allowed_weights : AllowedWeights beta
  phi : Fin n → PolynomialRing K n
  highest_phi : ∀ i, HasHighestPower r (phi i) i (r i)
/-- Literal PaperVerification.Fermion.marks; precise source and scope recorded in the extraction map. -/ def marks (T S : Finset (Fin n)) (i : Fin n) : ℕ :=
  (if i ∈ T then 1 else 0) + (if i ∈ S then 1 else 0)
/-- Literal PaperVerification.Fermion.height; precise source and scope recorded in the extraction map. -/ def height (T S : Finset (Fin n)) (i : Fin n) : ℤ :=
  (i.val : ℤ) + 1 - ∑ j ∈ Finset.univ.filter (fun j ↦ j ≤ i), (marks T S j : ℤ)
/-- Literal PaperVerification.Fermion.previousHeight; precise source and scope recorded in the extraction map. -/ def previousHeight (T S : Finset (Fin n)) (i : Fin n) : ℤ :=
  (i.val : ℤ) - ∑ j ∈ Finset.univ.filter (fun j ↦ j < i), (marks T S j : ℤ)
/-- Literal PaperVerification.Fermion.pairedBound; precise source and scope recorded in the extraction map. -/ def pairedBound (d : PairedData (K := K) (n := n)) (T S : Finset (Fin n)) (i : Fin n) : ℤ :=
  (d.r i : ℤ) * ((d.s : ℤ) + previousHeight T S i) -
    (if i ∈ T then (d.u i : ℤ) else 0) -
    (if i ∈ S then (d.v i : ℤ) else 0)
/-- Literal PaperVerification.Fermion.PairedIndex; precise source and scope recorded in the extraction map. -/ abbrev PairedIndex (d : PairedData (K := K) (n := n)) :=
  {z : (Finset (Fin n) × Finset (Fin n)) × (Fin n → ℕ) //
    (∀ i, 0 ≤ height z.1.1 z.1.2 i) ∧
    ∀ i, (z.2 i : ℤ) < pairedBound d z.1.1 z.1.2 i}
/-- Literal PaperVerification.Fermion.StrictIndex; precise source and scope recorded in the extraction map. -/ abbrev StrictIndex (d : StrictData (K := K) (n := n)) :=
  {z : (Finset (Fin n) × Finset (Fin n)) × (Fin n → ℕ) //
    (∀ i, 1 ≤ height z.1.1 z.1.2 i) ∧
    ∀ i, (z.2 i : ℤ) < (d.r i : ℤ) * height z.1.1 z.1.2 i}
/-- Literal PaperVerification.Fermion.boxMonomial; precise source and scope recorded in the extraction map. -/ noncomputable def boxMonomial (T S : Finset (Fin n)) (e : Fin n → ℕ) : SuperRing K n :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) (1 : K) •
    ((T.sort.map (theta K n)).prod * (S.sort.map (xi K n)).prod)
/-- Literal PaperVerification.Fermion.pairedClasses; precise source and scope recorded in the extraction map. -/ noncomputable def pairedClasses (d : PairedData (K := K) (n := n)) (z : PairedIndex d) : PairedQuotient d.beta d.phi d.a d.b :=
  (pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ K
    (boxMonomial z.1.1.1 z.1.1.2 z.1.2)
/-- Literal PaperVerification.Fermion.strictClasses; precise source and scope recorded in the extraction map. -/ noncomputable def strictClasses (d : StrictData (K := K) (n := n)) (z : StrictIndex d) : StrictQuotient d.beta d.phi :=
  (strictIdeal d.beta d.phi).ringCon.mkₐ K
    (boxMonomial z.1.1.1 z.1.1.2 z.1.2)
/-- Literal PaperVerification.Fermion.PairedBasisClaim; precise source and scope recorded in the extraction map. -/ def PairedBasisClaim (d : PairedData (K := K) (n := n)) : Prop :=
  LinearIndependent K (pairedClasses d) ∧
    Submodule.span K (Set.range (pairedClasses d)) = ⊤
/-- Literal PaperVerification.Fermion.StrictBasisClaim; precise source and scope recorded in the extraction map. -/ def StrictBasisClaim (d : StrictData (K := K) (n := n)) : Prop :=
  LinearIndependent K (strictClasses d) ∧
    Submodule.span K (Set.range (strictClasses d)) = ⊤
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Exterior
open scoped BigOperators
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
/-- Literal PaperVerification.Fermion.Exterior.modeRank; precise source and scope recorded in the extraction map. -/ def modeRank : Fin n ⊕ Fin n → ℕ
  | .inl i => i.val
  | .inr i => n + i.val
/-- Literal PaperVerification.Fermion.Exterior.modeRank_injective; precise source and scope recorded in the extraction map. -/ theorem modeRank_injective : Function.Injective (modeRank (n := n)) := by sorry
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion
open scoped BigOperators
open MvPolynomial
variable {K : Type*} [Field K] {n : ℕ}
/-- Literal PaperVerification.Fermion.coveringWeight; precise source and scope recorded in the extraction map. -/ def coveringWeight (r : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, r j
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Newton
open MvPolynomial
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
/-- Literal PaperVerification.Fermion.Newton.RectangleIndex; precise source and scope recorded in the extraction map. -/ abbrev RectangleIndex (h : Fin n → ℕ) :=
  {a : Fin n →₀ ℕ // ∀ i, a i < h i}
/-- Forward coordinates of the literal rectangular exponent box are in bounds. -/
theorem rectangleForwardBounds (h : Fin n → ℕ) (a : RectangleIndex h) : ∀ i, a.val i < h i := by sorry
/-- The unchanged inverse coordinate function lies in the literal rectangular box. -/
theorem rectangleBackwardBounds (h : Fin n → ℕ) (a : ∀ i, Fin (h i)) : ∀ i, Finsupp.equivFunOnFinite.symm (fun j => (a j).val) i < h i := by sorry
/-- Exact forward coordinate function, retaining the actual exponent values. -/
def rectangleForward (h : Fin n → ℕ) (a : RectangleIndex h) : ∀ i, Fin (h i) := fun i => ⟨a.val i,rectangleForwardBounds h a i⟩
/-- Exact inverse coordinate function, retaining the actual exponent values. -/
def rectangleBackward (h : Fin n → ℕ) (a : ∀ i, Fin (h i)) : RectangleIndex h := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val),rectangleBackwardBounds h a⟩
/-- The literal exponent coordinates recover the original rectangular index. -/
theorem rectangleLeftInverse (h : Fin n → ℕ) : Function.LeftInverse (rectangleBackward h) (rectangleForward h) := by sorry
/-- The literal rectangular index recovers its bounded coordinate function. -/
theorem rectangleRightInverse (h : Fin n → ℕ) : Function.RightInverse (rectangleBackward h) (rectangleForward h) := by sorry
/-- Literal PaperVerification.Fermion.Newton.rectangleIndexEquiv; precise source and scope recorded in the extraction map. -/ def rectangleIndexEquiv (h : Fin n → ℕ) : RectangleIndex h ≃ (∀ i : Fin n, Fin (h i)) where
  toFun := rectangleForward h
  invFun := rectangleBackward h
  left_inv := rectangleLeftInverse h
  right_inv := rectangleRightInverse h
/-- Literal PaperVerification.Fermion.Newton.rectangleIndex_fintype; precise source and scope recorded in the extraction map. -/
instance rectangleIndex_fintype (h : Fin n → ℕ) : Fintype (RectangleIndex h) :=
  Fintype.ofEquiv _ (rectangleIndexEquiv h).symm
end PaperVerification.Fermion.Newton
namespace PaperVerification.Fermion.Exterior
/-- Literal PaperVerification.Fermion.Exterior.interleavedOddRank; precise source and scope recorded in the extraction map. -/ def interleavedOddRank {n : ℕ} : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun i => 2 * i.val + 1) (fun i => 2 * i.val)
/-- Literal PaperVerification.Fermion.Exterior.interleavedOddRank_injective; precise source and scope recorded in the extraction map. -/ theorem interleavedOddRank_injective (n : ℕ) : Function.Injective (@interleavedOddRank n) := by sorry
/-- Literal PaperVerification.Fermion.Exterior.interleavedOddOrder; precise source and scope recorded in the extraction map. -/ def interleavedOddOrder (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' interleavedOddRank (interleavedOddRank_injective n)
/-- Literal PaperVerification.Fermion.Exterior.pairedPrefix; precise source and scope recorded in the extraction map. -/ def pairedPrefix (n i : ℕ) : Finset (Fin n ⊕ Fin n) :=
  (Finset.univ.filter (fun j : Fin n ↦ j.val < i)).disjSum
    (Finset.univ.filter (fun j : Fin n ↦ j.val < i))
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion.Endpoint
/-- Literal PaperVerification.Fermion.Endpoint.Mark; precise source and scope recorded in the extraction map. -/
inductive Mark
  | unmarked | theta | xi | double
  deriving DecidableEq
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion.Endpoint
open scoped BigOperators
open Polynomial
variable {R I : Type*} [CommRing R] [DecidableEq I]
/-- Literal PaperVerification.Fermion.Endpoint.wordMark; precise source and scope recorded in the extraction map. -/ def wordMark (T : Finset (I ⊕ I)) (i : I) : Mark :=
  if Sum.inl i ∈ T then
    if Sum.inr i ∈ T then .double else .theta
  else if Sum.inr i ∈ T then .xi else .unmarked
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion.Exterior
open scoped BigOperators
open Polynomial
open Colex
open Endpoint
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
local instance FermionHarmonicEndpoint_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionHarmonicEndpoint_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionHarmonicEndpoint_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionHarmonicEndpoint_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionHarmonicEndpoint_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionHarmonicEndpoint_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq
/-- Literal PaperVerification.Fermion.Exterior.wordHeight; precise source and scope recorded in the extraction map. -/ def wordHeight (T : Finset (Fin n ⊕ Fin n)) (i : ℕ) : ℕ :=
  i - (T ∩ pairedPrefix n i).card
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion.Endpoint
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
/-- Literal PaperVerification.Fermion.Endpoint.pairedBoxBound; precise source and scope recorded in the extraction map. -/ def pairedBoxBound (r u v s h : ℕ) : Mark → ℕ :=
  Mark.rec (r * (s + h)) (r * h + v) (r * h + u) (r * h)
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial Exterior Endpoint Colex
variable {K : Type*} [Field K] {n : ℕ}
local instance FermionPowerHarmonicBound_localInst_1 (m : ℕ) : LinearOrder (Fin m ⊕ Fin m) := interleavedOddOrder m
local instance FermionPowerHarmonicBound_localInst_2 (m : ℕ) : PartialOrder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPartialOrder
local instance FermionPowerHarmonicBound_localInst_3 (m : ℕ) : Preorder (Fin m ⊕ Fin m) := (interleavedOddOrder m).toPreorder
local instance FermionPowerHarmonicBound_localInst_4 (m : ℕ) : LE (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLE
local instance FermionPowerHarmonicBound_localInst_5 (m : ℕ) : LT (Fin m ⊕ Fin m) := (interleavedOddOrder m).toLT
local instance FermionPowerHarmonicBound_localInst_6 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) := (interleavedOddOrder m).toDecidableEq
/-- Literal PaperVerification.Fermion.ValidWord; precise source and scope recorded in the extraction map. -/ def ValidWord (T : Finset (Fin n ⊕ Fin n)) : Prop :=
  ∀ i ≤ n, (T ∩ pairedPrefix n i).card ≤ i
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionCreatorPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
/-- Literal PaperVerification.Fermion.wordBoxBounds; precise source and scope recorded in the extraction map. -/ def wordBoxBounds (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  pairedBoxBound (r i) (u i) (v i) s (wordHeight T i) (wordMark T i)
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open MvPolynomial
open scoped BigOperators _root_.TensorProduct
variable {K : Type*} [CommRing K] {n : ℕ} [LinearOrder (OddIndex n)]
/-- Literal PaperVerification.Fermion.SuperMonomialIndex; precise source and scope recorded in the extraction map. -/ abbrev SuperMonomialIndex (n : ℕ) := (Fin n →₀ ℕ) × Finset (OddIndex n)
/-- Literal PaperVerification.Fermion.superMonomialBasis; precise source and scope recorded in the extraction map. -/ def superMonomialBasis : Module.Basis (SuperMonomialIndex n) K (SuperRing K n) :=
  (basisMonomials (Fin n) K).tensorProduct (Pi.basisFun K (OddIndex n)).ExteriorAlgebra
/-- Literal PaperVerification.Fermion.wordPolynomialWeight; precise source and scope recorded in the extraction map. -/ def wordPolynomialWeight (ν : OddIndex n → ℕ) (T : Finset (OddIndex n)) : ℕ := ∑ j ∈ T, ν j
/-- Literal PaperVerification.Fermion.superMonomialWeight; precise source and scope recorded in the extraction map. -/ def superMonomialWeight (w : Fin n → ℕ) (ν : OddIndex n → ℕ) (z : SuperMonomialIndex n) : ℕ :=
  Finsupp.weight w z.1 + wordPolynomialWeight ν z.2
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open MvPolynomial
open scoped BigOperators _root_.TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
/-- Literal PaperVerification.Fermion.HasHighestPower.map; precise source and scope recorded in the extraction map. -/ theorem HasHighestPower.map (f : R →+* S) (r : Fin n → ℕ) (p : PolynomialRing R n) (i : Fin n) (d : ℕ) (hp : HasHighestPower r p i d) : HasHighestPower r
  (MvPolynomial.map f p) i d := by sorry
/-- Literal PaperVerification.Fermion.PairedData.map; precise source and scope recorded in the extraction map. -/ def PairedData.map (d : PairedData (K := R) (n := n)) (f : R →+* S) : PairedData (K := S) (n := n) where
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
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open MvPolynomial Exterior
open scoped BigOperators _root_.TensorProduct
variable {K : Type*} [CommRing K] {n : ℕ}
local instance FermionPairedMomentHighest_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance FermionPairedMomentHighest_localInst_2 : PartialOrder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPartialOrder
local instance FermionPairedMomentHighest_localInst_3 : Preorder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPreorder
local instance FermionPairedMomentHighest_localInst_4 : LE (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLE
local instance FermionPairedMomentHighest_localInst_5 : LT (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLT
local instance FermionPairedMomentHighest_localInst_6 : DecidableEq (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq
/-- Literal PaperVerification.Fermion.pairedOddWeight; precise source and scope recorded in the extraction map. -/ def pairedOddWeight (d : PairedData (K := K) (n := n)) : OddIndex n → ℕ :=
  Sum.elim (fun i => d.u i * coveringWeight d.r i) (fun i => d.v i * coveringWeight d.r i)
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators _root_.TensorProduct
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionPairedPowerBasis_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.PairedWordPolynomialIndex; precise source and scope recorded in the extraction map. -/ def PairedWordPolynomialIndex (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (OddIndex n)) :=
  {a : RectangleIndex (wordBoxBounds r u v s T) // ValidWord T}
/-- Literal PaperVerification.Fermion.pairedWordPolynomialIndex_fintype; precise source and scope recorded in the extraction map. -/
instance pairedWordPolynomialIndex_fintype
    (r u v : Fin n → ℕ) (s : ℕ) (T : Finset (OddIndex n)) :
    Fintype (PairedWordPolynomialIndex r u v s T) := by
  classical
  unfold PairedWordPolynomialIndex
  infer_instance
/-- Literal PaperVerification.Fermion.PairedPowerIndex; precise source and scope recorded in the extraction map. -/ abbrev PairedPowerIndex (r u v : Fin n → ℕ) (s : ℕ) :=
  Sigma (PairedWordPolynomialIndex r u v s)
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionPairedIndex_localInst_1 : DecidableEq (Fin n ⊕ Fin n) :=
  (interleavedOddOrder n).toDecidableEq
/-- Literal PaperVerification.Fermion.validWord_disjSum_iff; precise source and scope recorded in the extraction map. -/ theorem validWord_disjSum_iff (T S : Finset (Fin n)) : ValidWord (T.disjSum S) ↔ ∀ i, 0 ≤ height T S i := by sorry
/-- Literal PaperVerification.Fermion.wordBoxBounds_disjSum_cast; precise source and scope recorded in the extraction map. -/ theorem wordBoxBounds_disjSum_cast (d : PairedData (K := R) (n := n)) (T S : Finset (Fin n)) (h : ValidWord (T.disjSum S)) (i : Fin n) : (wordBoxBounds d.r d.u
  d.v d.s (T.disjSum S) i : ℤ) = pairedBound d T S i := by sorry
/-- Actual admissibility of the paired index's two exterior supports. -/
theorem pairedIndexValid (d : PairedData (K := R) (n := n)) (z : PairedIndex d) : ValidWord (z.val.1.1.disjSum z.val.1.2) := by sorry
/-- Exact paired power-box inequalities for the unchanged coordinate function. -/
theorem pairedIndexPowerBounds (d : PairedData (K := R) (n := n)) (z : PairedIndex d) : ∀ i, Finsupp.equivFunOnFinite.symm z.val.2 i < wordBoxBounds d.r d.u d.v d.s (z.val.1.1.disjSum z.val.1.2) i := by sorry
/-- Literal PaperVerification.Fermion.pairedIndexToPower; precise source and scope recorded in the extraction map. -/ def pairedIndexToPower (d : PairedData (K := R) (n := n)) (z : PairedIndex d) : PairedPowerIndex d.r d.u d.v d.s :=
  ⟨z.val.1.1.disjSum z.val.1.2,⟨⟨Finsupp.equivFunOnFinite.symm z.val.2,pairedIndexPowerBounds d z⟩,pairedIndexValid d z⟩⟩
/-- Literal PaperVerification.Fermion.pairedPowerToIndex; precise source and scope recorded in the extraction map. -/ def pairedPowerToIndex (d : PairedData (K := R) (n := n)) (z : PairedPowerIndex d.r d.u d.v d.s) : PairedIndex d := by
  have hW : ValidWord (z.1.toLeft.disjSum z.1.toRight) := by
    rw [Finset.toLeft_disjSum_toRight]
    exact z.2.property
  refine ⟨((z.1.toLeft,z.1.toRight),fun i ↦ z.2.val.val i),
    (validWord_disjSum_iff _ _).mp hW,?_⟩
  intro i
  rw [← wordBoxBounds_disjSum_cast d _ _ hW i,Finset.toLeft_disjSum_toRight]
  exact_mod_cast z.2.val.property i
/-- Literal PaperVerification.Fermion.pairedPowerIndex_ext; precise source and scope recorded in the extraction map. -/ theorem pairedPowerIndex_ext {r u v : Fin n → ℕ} {s : ℕ} {a b : PairedPowerIndex r u v s} (hW : a.1 = b.1) (he : a.2.val.val = b.2.val.val) : a = b :=
  by sorry
/-- Literal PaperVerification.Fermion.pairedIndexEquiv; precise source and scope recorded in the extraction map. -/ def pairedIndexEquiv (d : PairedData (K := R) (n := n)) : PairedIndex d ≃ PairedPowerIndex d.r d.u d.v d.s where
  toFun := pairedIndexToPower d
  invFun := pairedPowerToIndex d
  left_inv z := by
    apply Subtype.ext
    simp only [pairedIndexToPower,pairedPowerToIndex,Finset.toLeft_disjSum,
      Finset.toRight_disjSum,Finsupp.coe_equivFunOnFinite_symm]
  right_inv z := by
    rcases z with ⟨W,⟨⟨e,he⟩,hW⟩⟩
    apply pairedPowerIndex_ext
    · exact Finset.toLeft_disjSum_toRight
    · exact Finsupp.equivFunOnFinite_symm_coe e
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
attribute [local instance] PaperVerification.Fermion.FermionPairedIndex_localInst_1
local instance FermionPairedIndex_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance FermionPairedIndex_localInst_3 : PartialOrder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPartialOrder
local instance FermionPairedIndex_localInst_4 : Preorder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPreorder
local instance FermionPairedIndex_localInst_5 : LE (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLE
local instance FermionPairedIndex_localInst_6 : LT (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLT
local instance FermionPairedIndex_localInst_7 : DecidableEq (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq
/-- Literal PaperVerification.Fermion.paired_basis_claim; precise source and scope recorded in the extraction map. -/ theorem paired_basis_claim (d : PairedData (K := R) (n := n)) : PairedBasisClaim d := by sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open Exterior
open scoped _root_.TensorProduct
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
local instance FermionPairedAlgebraBaseChange_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.superQuotientTensorRing; precise source and scope recorded in the extraction map. -/
instance superQuotientTensorRing (I : TwoSidedIdeal (SuperRing R n)) :
    Ring (S ⊗[R] I.ringCon.Quotient) := by
  exact Algebra.TensorProduct.instRing (R := R) (A := S) (B := I.ringCon.Quotient)
/-- Literal PaperVerification.Fermion.superQuotientTensorAlgebra; precise source and scope recorded in the extraction map. -/
instance superQuotientTensorAlgebra (I : TwoSidedIdeal (SuperRing R n)) :
    Algebra S (S ⊗[R] I.ringCon.Quotient) := by
  exact Algebra.TensorProduct.leftAlgebra (R := R) (S := S) (A := S) (B := I.ringCon.Quotient)
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionHomogenizedFamily_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.weightedHomogenize; precise source and scope recorded in the extraction map. -/ def weightedHomogenize (w : Fin n → ℕ) (D : ℕ) (p : PolynomialRing R n) : PolynomialRing (Polynomial R) n :=
  ∑ a ∈ p.support, monomial a (Polynomial.C (p.coeff a) *
    Polynomial.X^(D-Finsupp.weight w a))
/-- Literal PaperVerification.Fermion.weightedHomogenize_hasHighestPower; precise source and scope recorded in the extraction map. -/ theorem weightedHomogenize_hasHighestPower (r : Fin n → ℕ) (p : PolynomialRing R n) (i : Fin n) (e : ℕ) (hp : HasHighestPower r p i e) : HasHighestPower r
  (weightedHomogenize (coveringWeight r) (e*coveringWeight r i) p) i e := by sorry
/-- Literal PaperVerification.Fermion.pairedHomogenizedData; precise source and scope recorded in the extraction map. -/ def pairedHomogenizedData (d : PairedData (K := R) (n := n)) : PairedData (K := Polynomial R) (n := n) where
  positive_n := d.positive_n
  s := d.s
  positive_s := d.positive_s
  r := d.r
  u := d.u
  v := d.v
  positive_r := d.positive_r
  degree_split := d.degree_split
  beta := Polynomial.C ∘ d.beta
  allowed_weights := (d.map Polynomial.C).allowed_weights
  phi := fun i ↦ weightedHomogenize (coveringWeight d.r) (d.r i*coveringWeight d.r i) (d.phi i)
  a := fun i ↦ weightedHomogenize (coveringWeight d.r) (d.u i*coveringWeight d.r i) (d.a i)
  b := fun i ↦ weightedHomogenize (coveringWeight d.r) (d.v i*coveringWeight d.r i) (d.b i)
  highest_phi := fun i ↦ weightedHomogenize_hasHighestPower d.r _ i _ (d.highest_phi i)
  highest_a := fun i ↦ weightedHomogenize_hasHighestPower d.r _ i _ (d.highest_a i)
  highest_b := fun i ↦ weightedHomogenize_hasHighestPower d.r _ i _ (d.highest_b i)
/-- Literal PaperVerification.Fermion.PairedHomogenizedQuotient; precise source and scope recorded in the extraction map. -/ abbrev PairedHomogenizedQuotient (d : PairedData (K := R) (n := n)) :=
  PairedQuotient (pairedHomogenizedData d).beta (pairedHomogenizedData d).phi
    (pairedHomogenizedData d).a (pairedHomogenizedData d).b
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators
variable {n : ℕ}
local instance FermionStrictPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
/-- Literal PaperVerification.Fermion.strictWordBoxBounds; precise source and scope recorded in the extraction map. -/ def strictWordBoxBounds (r : Fin n → ℕ) (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  r i*wordHeight T (i.val+1)
/-- Literal PaperVerification.Fermion.StrictWordPolynomialIndex; precise source and scope recorded in the extraction map. -/ def StrictWordPolynomialIndex (r : Fin n → ℕ) (T : Finset (OddIndex n)) :=
  {a : RectangleIndex (strictWordBoxBounds r T) // ValidWord T}
/-- Literal PaperVerification.Fermion.strictWordPolynomialIndex_fintype; precise source and scope recorded in the extraction map. -/
instance strictWordPolynomialIndex_fintype (r : Fin n → ℕ) (T : Finset (OddIndex n)) :
    Fintype (StrictWordPolynomialIndex r T) := by
  classical
  unfold StrictWordPolynomialIndex
  infer_instance
/-- Literal PaperVerification.Fermion.StrictPowerIndex; precise source and scope recorded in the extraction map. -/ abbrev StrictPowerIndex (r : Fin n → ℕ) := Sigma (StrictWordPolynomialIndex r)
/-- Literal PaperVerification.Fermion.StrictWord; precise source and scope recorded in the extraction map. -/ def StrictWord (T : Finset (OddIndex n)) : Prop :=
  ∀ j,0<j → j≤n → (T ∩ pairedPrefix n j).card<j
/-- Literal PaperVerification.Fermion.strictWord_of_polynomialIndex; precise source and scope recorded in the extraction map. -/ theorem strictWord_of_polynomialIndex (r : Fin n → ℕ) (T : Finset (OddIndex n)) (a : StrictWordPolynomialIndex r T) : StrictWord T := by sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open Exterior Endpoint
open scoped BigOperators
variable {A R : Type*} [CommSemiring A] [CommRing R] {n : ℕ}
/-- Literal PaperVerification.Fermion.pairedIndex_fintype; precise source and scope recorded in the extraction map. -/
instance pairedIndex_fintype (d : PairedData (K := R) (n := n)) : Fintype (PairedIndex d) :=
  Fintype.ofEquiv (PairedPowerIndex d.r d.u d.v d.s) (pairedIndexEquiv d).symm
end PaperVerification.Fermion
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M Q I E : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q] (b : Module.Basis I R M) (w : I → ℕ)
/-- Zero is homogeneous in every literal basis degree. -/
theorem homogeneousZero (d : ℕ) : Homogeneous b w d (0 : M) := by sorry
/-- Addition preserves the exact basis degree. -/
theorem homogeneousAdd {d : ℕ} {x y : M} (hx : Homogeneous b w d x) (hy : Homogeneous b w d y) : Homogeneous b w d (x+y) := by sorry
/-- Scalars preserve the exact basis degree. -/
theorem homogeneousSmul {d : ℕ} {x : M} (hx : Homogeneous b w d x) (c : R) : Homogeneous b w d (c • x) := by sorry
/-- Literal PaperVerification.Fermion.BasisFiltered.homogeneousPiece; precise source and scope recorded in the extraction map. -/ def homogeneousPiece (d : ℕ) : Submodule R M where
  carrier := {x | Homogeneous b w d x}
  zero_mem' := homogeneousZero b w d
  add_mem' := homogeneousAdd b w
  smul_mem' := fun c _ hx => homogeneousSmul b w hx c
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionStrictIndex_localInst_1 : DecidableEq (Fin n ⊕ Fin n) :=
  (interleavedOddOrder n).toDecidableEq
/-- Literal PaperVerification.Fermion.wordHeight_arrival_cast; precise source and scope recorded in the extraction map. -/ theorem wordHeight_arrival_cast (T S : Finset (Fin n)) (h : ValidWord (T.disjSum S)) (i : Fin n) : (wordHeight (T.disjSum S) (i.val+1) : ℤ)=height T S i := by
  sorry
/-- Literal PaperVerification.Fermion.strictWordBoxBounds_disjSum_cast; precise source and scope recorded in the extraction map. -/ theorem strictWordBoxBounds_disjSum_cast (r : Fin n → ℕ) (T S : Finset (Fin n)) (h : ValidWord (T.disjSum S)) (i : Fin n) : (strictWordBoxBounds r (T.disjSum S)
  i : ℤ)=(r i : ℤ)*height T S i := by sorry
/-- Actual admissibility of the strict index's two exterior supports. -/
theorem strictIndexValid (d : StrictData (K := R) (n := n)) (z : StrictIndex d) : ValidWord (z.val.1.1.disjSum z.val.1.2) := by sorry
/-- Exact strict power-box inequalities for the unchanged coordinate function. -/
theorem strictIndexPowerBounds (d : StrictData (K := R) (n := n)) (z : StrictIndex d) : ∀ i, Finsupp.equivFunOnFinite.symm z.val.2 i < strictWordBoxBounds d.r (z.val.1.1.disjSum z.val.1.2) i := by sorry
/-- Literal PaperVerification.Fermion.strictIndexToPower; precise source and scope recorded in the extraction map. -/ def strictIndexToPower (d : StrictData (K := R) (n := n)) (z : StrictIndex d) : StrictPowerIndex d.r :=
  ⟨z.val.1.1.disjSum z.val.1.2,⟨⟨Finsupp.equivFunOnFinite.symm z.val.2,strictIndexPowerBounds d z⟩,strictIndexValid d z⟩⟩
/-- Literal PaperVerification.Fermion.strictPowerToIndex; precise source and scope recorded in the extraction map. -/ def strictPowerToIndex (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) : StrictIndex d := by
  have hW : ValidWord (z.1.toLeft.disjSum z.1.toRight) := by
    rw [Finset.toLeft_disjSum_toRight]
    exact z.2.property
  have hstrict := strictWord_of_polynomialIndex d.r z.1 z.2
  refine ⟨((z.1.toLeft,z.1.toRight),fun i ↦ z.2.val.val i),?_,?_⟩
  · intro i
    rw [←wordHeight_arrival_cast _ _ hW i,Finset.toLeft_disjSum_toRight]
    have hh := hstrict (i.val+1) (Nat.succ_pos _) (Nat.succ_le_of_lt i.isLt)
    have hp : 1≤wordHeight z.1 (i.val+1) := by unfold wordHeight; omega
    exact_mod_cast hp
  · intro i
    rw [←strictWordBoxBounds_disjSum_cast d.r _ _ hW i,Finset.toLeft_disjSum_toRight]
    exact_mod_cast z.2.val.property i
/-- Literal PaperVerification.Fermion.strictPowerIndex_ext; precise source and scope recorded in the extraction map. -/ theorem strictPowerIndex_ext {r : Fin n → ℕ} {a b : StrictPowerIndex r} (hW : a.1 = b.1) (he : a.2.val.val = b.2.val.val) : a = b := by sorry
/-- Literal PaperVerification.Fermion.strictIndexEquiv; precise source and scope recorded in the extraction map. -/ def strictIndexEquiv (d : StrictData (K := R) (n := n)) : StrictIndex d ≃ StrictPowerIndex d.r where
  toFun := strictIndexToPower d
  invFun := strictPowerToIndex d
  left_inv z := by
    apply Subtype.ext
    simp only [strictIndexToPower,strictPowerToIndex,Finset.toLeft_disjSum,
      Finset.toRight_disjSum,Finsupp.coe_equivFunOnFinite_symm]
  right_inv z := by
    rcases z with ⟨W,⟨⟨e,he⟩,hW⟩⟩
    apply strictPowerIndex_ext
    · exact Finset.toLeft_disjSum_toRight
    · exact Finsupp.equivFunOnFinite_symm_coe e
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
attribute [local instance] PaperVerification.Fermion.FermionStrictIndex_localInst_1
local instance FermionStrictIndex_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
local instance FermionStrictIndex_localInst_3 : PartialOrder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPartialOrder
local instance FermionStrictIndex_localInst_4 : Preorder (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toPreorder
local instance FermionStrictIndex_localInst_5 : LE (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLE
local instance FermionStrictIndex_localInst_6 : LT (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toLT
local instance FermionStrictIndex_localInst_7 : DecidableEq (Fin n ⊕ Fin n) :=
  (LinearOrder.lift' modeRank modeRank_injective).toDecidableEq
/-- Literal PaperVerification.Fermion.strict_basis_claim; precise source and scope recorded in the extraction map. -/ theorem strict_basis_claim (d : StrictData (K := R) (n := n)) : StrictBasisClaim d := by sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionPairedExteriorPieces_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.pairedExteriorPiece; precise source and scope recorded in the extraction map. -/ def pairedExteriorPiece (d : PairedData (K := R) (n := n)) (j : ℕ) : Submodule R (PairedQuotient d.beta d.phi d.a d.b) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (fun i ↦ i.2.card) j).map
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R).toLinearMap
/-- Literal PaperVerification.Fermion.PairedExteriorIndex; precise source and scope recorded in the extraction map. -/ abbrev PairedExteriorIndex (d : PairedData (K := R) (n := n)) (j : ℕ) :=
  {z : PairedPowerIndex d.r d.u d.v d.s // z.1.card=j}
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open Exterior Endpoint
open scoped BigOperators
variable {A R : Type*} [CommSemiring A] [CommRing R] {n : ℕ}
/-- Literal PaperVerification.Fermion.strictIndex_fintype; precise source and scope recorded in the extraction map. -/
instance strictIndex_fintype (d : StrictData (K := R) (n := n)) : Fintype (StrictIndex d) :=
  Fintype.ofEquiv (StrictPowerIndex d.r) (strictIndexEquiv d).symm
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionStrictHighestForms_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.strictSuperWeight; precise source and scope recorded in the extraction map. -/ def strictSuperWeight (d : StrictData (K := R) (n := n)) : SuperMonomialIndex n → ℕ :=
  superMonomialWeight (coveringWeight d.r) (fun _ ↦ 0)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.FilteredAlgebra
open scoped DirectSum
universe u w
variable (R : Type u) (A : Type w) [CommRing R] [Ring A] [Algebra R A]
/-- Literal PaperVerification.Fermion.FilteredAlgebra.Filtration; precise source and scope recorded in the extraction map. -/ structure Filtration where
  piece : ℕ → Submodule R A
  mono : Monotone piece
  one_mem : (1 : A) ∈ piece 0
  mul_mem : ∀ {i j : ℕ} {x y : A}, x ∈ piece i → y ∈ piece j → x*y ∈ piece (i+j)
end PaperVerification.Fermion.FilteredAlgebra
namespace PaperVerification.Fermion.FilteredAlgebra
open scoped DirectSum
universe u w
variable (R : Type u) (A : Type w) [CommRing R] [Ring A] [Algebra R A]
variable {R A}
/-- Literal PaperVerification.Fermion.FilteredAlgebra.filtration; precise source and scope recorded in the extraction map. -/ abbrev filtration (f : Filtration R A) := f.piece
/-- Literal PaperVerification.Fermion.FilteredAlgebra.previous; precise source and scope recorded in the extraction map. -/ def previous (f : Filtration R A) : ℕ → Submodule R A
  | 0 => ⊥
  | k+1 => f.piece k
/-- Literal PaperVerification.Fermion.FilteredAlgebra.previousRestricted; precise source and scope recorded in the extraction map. -/ def previousRestricted (f : Filtration R A) (k : ℕ) : Submodule R (filtration f k) :=
  (previous f k).comap (filtration f k).subtype
/-- Literal PaperVerification.Fermion.FilteredAlgebra.mul_mem_filtration; precise source and scope recorded in the extraction map. -/ theorem mul_mem_filtration (f : Filtration R A) {i j : ℕ} {x y : A} (hx : x ∈ filtration f i) (hy : y ∈ filtration f j) : x*y ∈ filtration f (i+j) := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.one_mem_filtration; precise source and scope recorded in the extraction map. -/ theorem one_mem_filtration (f : Filtration R A) (k : ℕ) : (1 : A) ∈ filtration f k := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.algebraMap_mem_filtration; precise source and scope recorded in the extraction map. -/ theorem algebraMap_mem_filtration (f : Filtration R A) (r : R) (k : ℕ) : algebraMap R A r ∈ filtration f k := by sorry
/-- The original simp interface for the actual previous-piece restriction. -/
@[simp] theorem mem_previousRestricted_iff (f : Filtration R A) (k : ℕ)
    (x : filtration f k) : x ∈ previousRestricted f k ↔ (x : A) ∈ previous f k := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.GradedPiece; precise source and scope recorded in the extraction map. -/ abbrev GradedPiece (f : Filtration R A) (k : ℕ) : Type w :=
  filtration f k ⧸ previousRestricted f k
/-- Literal PaperVerification.Fermion.FilteredAlgebra.AssociatedGraded; precise source and scope recorded in the extraction map. -/ abbrev AssociatedGraded (f : Filtration R A) : Type w :=
  ⨁ k : ℕ, GradedPiece f k
/-- Literal PaperVerification.Fermion.FilteredAlgebra.filteredMul; precise source and scope recorded in the extraction map. -/ noncomputable def filteredMul (f : Filtration R A) (i j : ℕ) : filtration f i →ₗ[R] filtration f j →ₗ[R] filtration f (i + j) :=
  { toFun := fun x =>
      { toFun := fun y => ⟨(x : A)*y,mul_mem_filtration f x.property y.property⟩
        map_add' := fun y z => Subtype.ext (mul_add (x : A) y z)
        map_smul' := fun c y => Subtype.ext (mul_smul_comm c (x : A) (y : A)) }
    map_add' := fun x y => LinearMap.ext (fun z => Subtype.ext (add_mul (x : A) y z))
    map_smul' := fun c x => LinearMap.ext (fun y => Subtype.ext (smul_mul_assoc c (x : A) y)) }
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedPreMul; precise source and scope recorded in the extraction map. -/ noncomputable def gradedPreMul (f : Filtration R A) (i j : ℕ) : filtration f i →ₗ[R] filtration f j →ₗ[R] GradedPiece f (i + j) :=
  (filteredMul f i j).compr₂ (Submodule.mkQ _)
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedPreMul_mem_ker_left; precise source and scope recorded in the extraction map. -/ theorem gradedPreMul_mem_ker_left (f : Filtration R A) (i j : ℕ) : previousRestricted f i ≤ (gradedPreMul f i j).ker := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedPreMul_mem_ker_right; precise source and scope recorded in the extraction map. -/ theorem gradedPreMul_mem_ker_right (f : Filtration R A) (i j : ℕ) : previousRestricted f j ≤ (gradedPreMul f i j).flip.ker := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedMul; precise source and scope recorded in the extraction map. -/ noncomputable def gradedMul (f : Filtration R A) (i j : ℕ) : GradedPiece f i →ₗ[R] GradedPiece f j →ₗ[R] GradedPiece f (i + j) :=
  (gradedPreMul f i j).liftQ₂ _ _
    (gradedPreMul_mem_ker_left f i j)
    (gradedPreMul_mem_ker_right f i j)
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedMul_assoc; precise source and scope recorded in the extraction map. -/ theorem gradedMul_assoc (f : Filtration R A) (i j k : ℕ) (x : GradedPiece f i) (y : GradedPiece f j) (z : GradedPiece f k) : cast (congrArg (GradedPiece f)
  (Nat.add_assoc i j k)) (gradedMul f (i + j) k (gradedMul f i j x y) z) = gradedMul f i (j + k) x (gradedMul f j k y z) := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedOne; precise source and scope recorded in the extraction map. -/ noncomputable def gradedOne (f : Filtration R A) : GradedPiece f 0 :=
  Submodule.Quotient.mk ⟨1, one_mem_filtration f 0⟩
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedAlgebraMap₀; precise source and scope recorded in the extraction map. -/ noncomputable def gradedAlgebraMap₀ (f : Filtration R A) : R →+ GradedPiece f 0 where
  toFun r := Submodule.Quotient.mk
    ⟨algebraMap R (A) r, algebraMap_mem_filtration f r 0⟩
  map_zero' := by simp
  map_add' r s := by
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (map_add (algebraMap R (A)) r s)
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedAlgebraMap₀_one; precise source and scope recorded in the extraction map. -/ @[simp] theorem gradedAlgebraMap₀_one (f : Filtration R A) : gradedAlgebraMap₀ f 1 = gradedOne f := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedOne_mul; precise source and scope recorded in the extraction map. -/ @[simp] theorem gradedOne_mul (f : Filtration R A) (k : ℕ) (x : GradedPiece f k) : gradedMul f 0 k (gradedOne f) x = cast (congrArg (GradedPiece f)
  (Nat.zero_add k).symm) x := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedMul_one; precise source and scope recorded in the extraction map. -/ @[simp] theorem gradedMul_one (f : Filtration R A) (k : ℕ) (x : GradedPiece f k) : gradedMul f k 0 x (gradedOne f) = cast (congrArg (GradedPiece f)
  (Nat.add_zero k).symm) x := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedGOne; precise source and scope recorded in the extraction map. -/
noncomputable instance gradedGOne {f : Filtration R A} :
    GradedMonoid.GOne (GradedPiece f) where
  one := gradedOne f
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedGMul; precise source and scope recorded in the extraction map. -/
noncomputable instance gradedGMul {f : Filtration R A} :
    GradedMonoid.GMul (GradedPiece f) where
  mul {i j} := fun x y => gradedMul f i j x y
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedGMonoid; precise source and scope recorded in the extraction map. -/
noncomputable instance gradedGMonoid {f : Filtration R A} :
    GradedMonoid.GMonoid (GradedPiece f) :=
  { gradedGMul (f := f), gradedGOne (f := f) with
    one_mul := fun x => by
      rcases x with ⟨k, x⟩
      apply Sigma.ext (Nat.zero_add k)
      apply heq_of_cast_eq (congrArg (GradedPiece f) (Nat.zero_add k))
      -- The sigma equality is now a homogeneous equality after exposing the GOne and GMul fields.
      change cast (congrArg (GradedPiece f) (Nat.zero_add k))
        (gradedMul f 0 k (gradedOne f) x) = x
      rw [gradedOne_mul]
      simp
    mul_one := fun x => by
      rcases x with ⟨k, x⟩
      apply Sigma.ext (Nat.add_zero k)
      apply heq_of_cast_eq (congrArg (GradedPiece f) (Nat.add_zero k))
      -- The sigma equality is now a homogeneous equality after exposing the GOne and GMul fields.
      change cast (congrArg (GradedPiece f) (Nat.add_zero k))
        (gradedMul f k 0 x (gradedOne f)) = x
      rw [gradedMul_one]
      simp
    mul_assoc := fun x y z => by
      rcases x with ⟨i, x⟩
      rcases y with ⟨j, y⟩
      rcases z with ⟨k, z⟩
      apply Sigma.ext (Nat.add_assoc i j k)
      apply heq_of_cast_eq (congrArg (GradedPiece f) (Nat.add_assoc i j k))
      exact gradedMul_assoc f i j k x y z }
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedGRing; precise source and scope recorded in the extraction map. -/
noncomputable instance gradedGRing {f : Filtration R A} :
    DirectSum.GRing (GradedPiece f) where
  mul_zero := fun x => (gradedMul f _ _ x).map_zero
  zero_mul := fun x => by
    -- `DirectSum.GRing` states this through `GMul`; expose its declared homogeneous product.
    change gradedMul f _ _ 0 x = 0
    rw [LinearMap.map_zero]
    rfl
  mul_add := fun x y z => (gradedMul f _ _ x).map_add y z
  add_mul := fun x y z => by
    -- `DirectSum.GRing` states this through `GMul`; expose its declared homogeneous product.
    change gradedMul f _ _ (x + y) z =
      gradedMul f _ _ x z + gradedMul f _ _ y z
    rw [LinearMap.map_add]
    rfl
  natCast := fun n => gradedAlgebraMap₀ f n
  natCast_zero := by
    rw [Nat.cast_zero]
    exact map_zero (gradedAlgebraMap₀ f)
  natCast_succ := fun n => by
    -- The cast field is represented by the degree-zero scalar class chosen above.
    change gradedAlgebraMap₀ f ((n + 1 : ℕ) : R) =
      gradedAlgebraMap₀ f (n : R) + gradedOne f
    rw [Nat.cast_succ, map_add]
    rw [gradedAlgebraMap₀_one]
  intCast := fun z => gradedAlgebraMap₀ f z
  intCast_ofNat := fun n => by
    -- Integer casts use the same chosen degree-zero scalar representative.
    change gradedAlgebraMap₀ f ((n : ℤ) : R) = gradedAlgebraMap₀ f (n : R)
    norm_cast
  intCast_negSucc_ofNat := fun n => by
    -- Integer casts use the same chosen degree-zero scalar representative.
    change gradedAlgebraMap₀ f ((Int.negSucc n : ℤ) : R) =
      -gradedAlgebraMap₀ f ((n + 1 : ℕ) : R)
    rw [Int.cast_negSucc, map_neg]
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedAlgebraMap₀_mul; precise source and scope recorded in the extraction map. -/ @[simp] theorem gradedAlgebraMap₀_mul (f : Filtration R A) (r : R) (k : ℕ) (x : GradedPiece f k) : cast (congrArg (GradedPiece f) (Nat.zero_add k)) (gradedMul f
  0 k (gradedAlgebraMap₀ f r) x) = r • x := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedAlgebraMap₀_mul_algebraMap₀; precise source and scope recorded in the extraction map. -/ @[simp 1100] theorem gradedAlgebraMap₀_mul_algebraMap₀ (f : Filtration R A) (r s : R) : gradedMul f 0 0 (gradedAlgebraMap₀ f r) (gradedAlgebraMap₀ f s) =
  gradedAlgebraMap₀ f (r * s) := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedAlgebraMap₀_commutes; precise source and scope recorded in the extraction map. -/ theorem gradedAlgebraMap₀_commutes (f : Filtration R A) (r : R) (k : ℕ) (x : GradedPiece f k) : cast (congrArg (GradedPiece f) ((Nat.zero_add k).trans
  (Nat.add_zero k).symm)) (gradedMul f 0 k (gradedAlgebraMap₀ f r) x) = gradedMul f k 0 x (gradedAlgebraMap₀ f r) := by sorry
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedGSemiring; precise source and scope recorded in the extraction map. -/
noncomputable instance gradedGSemiring {f : Filtration R A} :
    DirectSum.GSemiring (GradedPiece f) := by
  exact @DirectSum.GRing.toGSemiring ℕ (GradedPiece f) _ _
    (gradedGRing (f := f))
/-- Literal PaperVerification.Fermion.FilteredAlgebra.gradedGAlgebra; precise source and scope recorded in the extraction map. -/
noncomputable instance gradedGAlgebra {f : Filtration R A} :
    DirectSum.GAlgebra R (GradedPiece f) where
  toFun := gradedAlgebraMap₀ f
  map_one := by
    -- `DirectSum.GAlgebra.map_one` is phrased through the degree-zero `GOne` field.
    change gradedAlgebraMap₀ f 1 = gradedOne f
    exact gradedAlgebraMap₀_one f
  map_mul r s := by
    apply Sigma.ext (Nat.zero_add 0).symm
    apply heq_of_cast_eq (congrArg (GradedPiece f) (Nat.zero_add 0).symm)
    -- The scalar product is a degree-zero homogeneous product after this reindexing.
    change cast (congrArg (GradedPiece f) (Nat.zero_add 0).symm)
      (gradedAlgebraMap₀ f (r * s)) =
      gradedMul f 0 0 (gradedAlgebraMap₀ f r)
        (gradedAlgebraMap₀ f s)
    rw [gradedAlgebraMap₀_mul_algebraMap₀]
    simp
  commutes r x := by
    rcases x with ⟨k, x⟩
    apply Sigma.ext ((Nat.zero_add k).trans (Nat.add_zero k).symm)
    apply heq_of_cast_eq
      (congrArg (GradedPiece f) ((Nat.zero_add k).trans (Nat.add_zero k).symm))
    exact gradedAlgebraMap₀_commutes f r k x
  smul_def r x := by
    rcases x with ⟨k, x⟩
    apply Sigma.ext (Nat.zero_add k).symm
    apply heq_of_cast_eq (congrArg (GradedPiece f) (Nat.zero_add k).symm)
    -- The sigma-level scalar law reduces to the degree-`k` homogeneous scalar equation.
    change cast (congrArg (GradedPiece f) (Nat.zero_add k).symm) (r • x) =
      gradedMul f 0 k (gradedAlgebraMap₀ f r) x
    symm
    simpa only [cast_cast, cast_eq] using
      congrArg (cast (congrArg (GradedPiece f) (Nat.zero_add k).symm))
        (gradedAlgebraMap₀_mul f r k x)
/-- Literal PaperVerification.Fermion.FilteredAlgebra.associatedGradedRing; precise source and scope recorded in the extraction map. -/
noncomputable instance associatedGradedRing {f : Filtration R A} :
    Ring (AssociatedGraded f) := by
  letI : ∀ k, AddCommGroup (GradedPiece f k) := fun _ => inferInstance
  infer_instance
end PaperVerification.Fermion.FilteredAlgebra
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R A Q I : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring Q] [Algebra R Q] (b : Module.Basis I R A) (w : I → ℕ)
/-- Literal PaperVerification.Fermion.BasisFiltered.bound_mul; precise source and scope recorded in the extraction map. -/ theorem bound_mul (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j)) {d e : ℕ} {x y : A} (hx : Bound b w d x) (hy : Bound b w e y) : Bound b w (d+e) (x*y) := by
  sorry
/-- Literal PaperVerification.Fermion.BasisFiltered.boundPiece; precise source and scope recorded in the extraction map. -/ def boundPiece (d : ℕ) : Submodule R A where
  carrier := {x | Bound b w d x}
  zero_mem' := bound_zero b w d
  add_mem' := bound_add b w
  smul_mem' := fun c x hx ↦ bound_smul b w hx c
/-- Literal PaperVerification.Fermion.BasisFiltered.boundPiece_mono; precise source and scope recorded in the extraction map. -/ theorem boundPiece_mono : Monotone (boundPiece b w) := by sorry
/-- Monotonicity of the actual quotient image pieces. -/
theorem quotientPieceMonotone (q : A →ₐ[R] Q) : Monotone (fun d => (boundPiece b w d).map q.toLinearMap) := by sorry
/-- The image filtration contains the unit in degree zero. -/
theorem quotientPieceUnit (q : A →ₐ[R] Q) (hone : Homogeneous b w 0 (1 : A)) : (1 : Q) ∈ (boundPiece b w 0).map q.toLinearMap := by sorry
/-- Products of actual quotient images have the sum of the filtration bounds. -/
theorem quotientPieceProduct (q : A →ₐ[R] Q) (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j)) {i j : ℕ} {x y : Q} (hx : x ∈ (boundPiece b w i).map q.toLinearMap) (hy : y ∈ (boundPiece b w j).map q.toLinearMap) : x*y ∈ (boundPiece b w (i+j)).map q.toLinearMap := by sorry
/-- Literal PaperVerification.Fermion.BasisFiltered.quotientFiltration; precise source and scope recorded in the extraction map. -/ def quotientFiltration (q : A →ₐ[R] Q) (hone : Homogeneous b w 0 (1 : A)) (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j)) : FilteredAlgebra.Filtration R Q where
  piece d := (boundPiece b w d).map q.toLinearMap
  mono := quotientPieceMonotone b w q
  one_mem := quotientPieceUnit b w q hone
  mul_mem := quotientPieceProduct b w q hmul
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators _root_.TensorProduct DirectSum
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionPairedAssociatedGraded_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.super_weighted_one_homogeneous; precise source and scope recorded in the extraction map. -/ theorem super_weighted_one_homogeneous (w : Fin n → ℕ) (ν : OddIndex n → ℕ) : BasisFiltered.Homogeneous (superMonomialBasis (K := R)) (superMonomialWeight w ν)
  0 1 := by sorry
/-- Literal PaperVerification.Fermion.super_weighted_basis_mul_homogeneous; precise source and scope recorded in the extraction map. -/ theorem super_weighted_basis_mul_homogeneous (w : Fin n → ℕ) (ν : OddIndex n → ℕ) (L T : SuperMonomialIndex n) : BasisFiltered.Homogeneous (superMonomialBasis
  (K := R)) (superMonomialWeight w ν) (superMonomialWeight w ν L+superMonomialWeight w ν T) (superMonomialBasis L*superMonomialBasis T) := by sorry
/-- Literal PaperVerification.Fermion.pairedSuperWeight; precise source and scope recorded in the extraction map. -/ def pairedSuperWeight (d : PairedData (K := R) (n := n)) : SuperMonomialIndex n → ℕ :=
  superMonomialWeight (coveringWeight d.r) (pairedOddWeight d)
/-- Literal PaperVerification.Fermion.pairedQuotientFiltration; precise source and scope recorded in the extraction map. -/ def pairedQuotientFiltration (d : PairedData (K := R) (n := n)) : FilteredAlgebra.Filtration R (PairedQuotient d.beta d.phi d.a d.b) :=
  BasisFiltered.quotientFiltration (superMonomialBasis (K := R)) (pairedSuperWeight d)
    ((pairedIdeal d.beta d.phi d.a d.b).ringCon.mkₐ R)
    (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
    (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (pairedOddWeight d))
/-- Literal PaperVerification.Fermion.PairedAssociatedGraded; precise source and scope recorded in the extraction map. -/ abbrev PairedAssociatedGraded (d : PairedData (K := R) (n := n)) :=
  FilteredAlgebra.AssociatedGraded (pairedQuotientFiltration d)
/-- Literal PaperVerification.Fermion.pairedPowerWeightedPiece; precise source and scope recorded in the extraction map. -/ def pairedPowerWeightedPiece (d : PairedData (K := R) (n := n)) (k : ℕ) : Submodule R (PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (pairedSuperWeight d) k).map
    ((pairedIdeal d.beta (fun i ↦ X i^d.r i)
      (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i)).ringCon.mkₐ R).toLinearMap
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped DirectSum
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionStrictAssociatedGraded_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.strictQuotientFiltration; precise source and scope recorded in the extraction map. -/ def strictQuotientFiltration (d : StrictData (K := R) (n := n)) : FilteredAlgebra.Filtration R (StrictQuotient d.beta d.phi) :=
  BasisFiltered.quotientFiltration (superMonomialBasis (K := R)) (strictSuperWeight d)
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R)
    (super_weighted_one_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
    (super_weighted_basis_mul_homogeneous (R := R) (coveringWeight d.r) (fun _ : OddIndex n ↦ 0))
/-- Literal PaperVerification.Fermion.StrictAssociatedGraded; precise source and scope recorded in the extraction map. -/ abbrev StrictAssociatedGraded (d : StrictData (K := R) (n := n)) :=
  FilteredAlgebra.AssociatedGraded (strictQuotientFiltration d)
/-- Literal PaperVerification.Fermion.strictPowerWeightedPiece; precise source and scope recorded in the extraction map. -/ def strictPowerWeightedPiece (d : StrictData (K := R) (n := n)) (k : ℕ) : Submodule R (StrictQuotient d.beta (fun i ↦ X i^d.r i)) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (strictSuperWeight d) k).map
    ((strictIdeal d.beta (fun i ↦ X i^d.r i)).ringCon.mkₐ R).toLinearMap
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open Exterior
open MvPolynomial
open scoped BigOperators _root_.TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionTheoremOneOne_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.theorem_1_1; precise source and scope recorded in the extraction map. -/ theorem theorem_1_1 (d : PairedData (K := R) (n := n)) :
    PairedBasisClaim d ∧
    Fintype.card (PairedIndex d)=2^n*(∏ i,d.r i)*d.s.ascFactorial n ∧
    (∀ j,Nonempty (Module.Basis (PairedExteriorIndex d j) R (pairedExteriorPiece d j)) ∧
      Fintype.card (PairedExteriorIndex d j)=
        (Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n : Polynomial ℕ).coeff j) ∧
    (∃ e : PairedAssociatedGraded d ≃ₐ[R]
      PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i),
      ∀ k,LinearMap.range (e.toLinearMap.comp
        (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (pairedQuotientFiltration d)) k)) =
        pairedPowerWeightedPiece d k) ∧
    PairedBasisClaim (pairedHomogenizedData d) ∧
    (Module.Finite (Polynomial R) (PairedHomogenizedQuotient d) ∧
      Module.Free (Polynomial R) (PairedHomogenizedQuotient d)) ∧
    Module.Flat (Polynomial R) (PairedHomogenizedQuotient d) ∧
    (letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (0 : R)).toAlgebra;
      Nonempty (R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
        PairedQuotient d.beta (fun i ↦ X i^d.r i) (fun i ↦ X i^d.u i) (fun i ↦ X i^d.v i))) ∧
    (letI : Algebra (Polynomial R) R := (Polynomial.evalRingHom (1 : R)).toAlgebra;
      Nonempty (R ⊗[Polynomial R] PairedHomogenizedQuotient d ≃ₐ[R]
        PairedQuotient d.beta d.phi d.a d.b)) := by sorry
/-- Literal PaperVerification.Fermion.theorem_1_1_rank; precise source and scope recorded in the extraction map. -/ theorem theorem_1_1_rank [Nontrivial R] (d : PairedData (K := R) (n := n)) : Module.finrank R (PairedQuotient d.beta d.phi d.a d.b)= 2^n*(∏ i,d.r
  i)*d.s.ascFactorial n ∧ ∀ j,Module.finrank R (pairedExteriorPiece d j)= (Polynomial.C ((∏ i,d.r i)*d.s.ascFactorial n)*(1+Polynomial.X)^n : Polynomial
  ℕ).coeff j := by sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionStrictExteriorPieces_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.strictExteriorPiece; precise source and scope recorded in the extraction map. -/ def strictExteriorPiece (d : StrictData (K := R) (n := n)) (j : ℕ) : Submodule R (StrictQuotient d.beta d.phi) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := R)) (fun i ↦ i.2.card) j).map
    ((strictIdeal d.beta d.phi).ringCon.mkₐ R).toLinearMap
/-- Literal PaperVerification.Fermion.StrictExteriorIndex; precise source and scope recorded in the extraction map. -/ abbrev StrictExteriorIndex (d : StrictData (K := R) (n := n)) (j : ℕ) :=
  {z : StrictPowerIndex d.r // z.1.card=j}
end PaperVerification.Fermion
namespace PaperVerification.Fermion
open Exterior
open MvPolynomial
open scoped BigOperators DirectSum
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionTheoremOneTwo_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
/-- Literal PaperVerification.Fermion.theorem_1_2; precise source and scope recorded in the extraction map. -/ theorem theorem_1_2 (d : StrictData (K := R) (n := n)) : StrictBasisClaim d ∧ Fintype.card (StrictIndex d)=2^(n-1)*(∏ i,d.r i)*n.factorial ∧ (∀ j,Nonempty
  (Module.Basis (StrictExteriorIndex d j) R (strictExteriorPiece d j)) ∧ Fintype.card (StrictExteriorIndex d j)= (Polynomial.C ((∏ i,d.r
  i)*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j) ∧ (∃ e : StrictAssociatedGraded d ≃ₐ[R] StrictQuotient d.beta (fun i ↦ X i^d.r i), ∀
  k,LinearMap.range (e.toLinearMap.comp (DirectSum.lof R ℕ (FilteredAlgebra.GradedPiece (strictQuotientFiltration d)) k))= strictPowerWeightedPiece d k) := by
  sorry
/-- Literal PaperVerification.Fermion.theorem_1_2_rank; precise source and scope recorded in the extraction map. -/ theorem theorem_1_2_rank [Nontrivial R] (d : StrictData (K := R) (n := n)) : Module.finrank R (StrictQuotient d.beta d.phi)=2^(n-1)*(∏ i,d.r i)*n.factorial ∧ ∀
  j,Module.finrank R (strictExteriorPiece d j)= (Polynomial.C ((∏ i,d.r i)*n.factorial)*(1+Polynomial.X)^(n-1) : Polynomial ℕ).coeff j := by sorry
end PaperVerification.Fermion

namespace PalomarFermion
open PaperVerification.Fermion
universe uPalomar

/-- The paired quotient is free of the printed finite rank over every ring. -/
theorem pairedFreeRank {R : Type uPalomar} [CommRing R] {n : ℕ}
    (d : PairedData (K := R) (n := n)) :
    Nonempty (PairedQuotient d.beta d.phi d.a d.b ≃ₗ[R]
      (Fin (2^n * (∏ i, d.r i) * d.s.ascFactorial n) → R)) := by sorry

/-- The strict quotient is free of the printed finite rank over every ring. -/
theorem strictFreeRank {R : Type uPalomar} [CommRing R] {n : ℕ}
    (d : StrictData (K := R) (n := n)) :
    Nonempty (StrictQuotient d.beta d.phi ≃ₗ[R]
      (Fin (2^(n-1) * (∏ i, d.r i) * n.factorial) → R)) := by sorry

end PalomarFermion
