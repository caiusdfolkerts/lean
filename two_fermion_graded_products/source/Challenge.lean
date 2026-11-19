module
public import Mathlib

/-! Theorem 8.1: initial ideals and an equivariant degeneration of the two-fermion quotient. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PaperVerification.Fermion.WeightRees
open scoped Classical BigOperators LaurentPolynomial
variable (K A : Type*) [CommRing K] [Ring A] [Algebra K A]
open scoped PaperVerification.Fermion.WeightRees
variable {K A}
variable {I : Type*} [Fintype I] (b : Module.Basis I K A) (weight : I → ℕ)
def Multiplicative : Prop := ∀ i j k,b.repr (b i*b j) k≠0 → weight i+weight j≤weight k
def multiplicationPolynomial (i j k : I) : Polynomial K := Polynomial.monomial (weight k-(weight i+weight j)) (b.repr (b i*b j) k)
end PaperVerification.Fermion.WeightRees
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ)
def component (d : ℕ) : M →ₗ[R] M where
  toFun x := b.repr.symm ((b.repr x).filter (fun i ↦ w i = d))
  map_add' x y := by rw [map_add,Finsupp.filter_add,map_add]
  map_smul' a x := by rw [map_smul,Finsupp.filter_smul,map_smul,RingHom.id_apply]
def Homogeneous (d : ℕ) (x : M) : Prop := ∀ i, b.repr x i ≠ 0 → w i = d
theorem homogeneous_component (d : ℕ) (x : M) : Homogeneous b w d (component b w d x) := by sorry
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion.BlockInitial
open scoped BigOperators
open BasisFiltered
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  (b : Module.Basis J P M) (weight : J → ℕ)
def LowerBound (r : ℕ) (x : M) : Prop := ∀ j,b.repr x j≠0 → r≤weight j
def initialMin (I : Submodule K M) : Submodule K M :=
  Submodule.span K {y | ∃ x∈I,∃ r,LowerBound b weight r x ∧ component b weight r x=y}
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
namespace PaperVerification.Fermion.BlockInitial.TriangularPresentation
open scoped BigOperators
open BasisFiltered
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  (b : Module.Basis J P M) (weight : J → ℕ)
variable (q : M →ₗ[K] Q) (D : J → Type*) [∀ j,Fintype (D j)]
variable {b weight q D}
variable (h : TriangularPresentation (N := N) b weight q D)
def representative (z : Sigma D) : M := h.polynomial z.1 z.2 • b z.1
end PaperVerification.Fermion.BlockInitial.TriangularPresentation
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
section
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
variable (b : Module.Basis (Fin n ⊕ Fin n) R V)
local notation "E" => ExteriorAlgebra R V
variable (φ β a c : Fin n → R)
def thetaCreatorVector (p : Polynomial R) : V := ∑ i, (β i * a i * p.eval (φ i)) • b (.inl i)
def xiCreatorVector (p : Polynomial R) : V := ∑ i, (c i * p.eval (φ i)) • b (.inr i)
def suffixPolynomial (j : Fin n) : Polynomial R := ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (Polynomial.X - Polynomial.C (φ i))
end
variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [LinearOrder I]
local notation "E" => ExteriorAlgebra R V
def coefficientPairing (b : Module.Basis I R V) : E →ₗ[R] E →ₗ[R] R := b.ExteriorAlgebra.toDual
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct BigOperators
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}
def oddScalarExtension : OddModule K n →ₗ[K] OddModule A n where
  toFun v i := algebraMap K A (v i)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp [Algebra.smul_def]
def oddExteriorSpecialization : ExteriorAlgebra K (OddModule K n) →ₐ[K] ExteriorAlgebra A (OddModule A n) := ExteriorAlgebra.lift K
  ⟨((ExteriorAlgebra.ι A).restrictScalars K).comp oddScalarExtension, fun v ↦ ExteriorAlgebra.ι_sq_zero _⟩
def superSpecialization (f : PolynomialRing K n →ₐ[K] A) : SuperRing K n →ₐ[K] ExteriorAlgebra A (OddModule A n) :=
  Algebra.TensorProduct.lift (R := K) (S := K) (((Algebra.ofId A (ExteriorAlgebra A (OddModule A n))).restrictScalars K).comp f)
  oddExteriorSpecialization (fun p z ↦ Algebra.commute_algebraMap_left (f p) _)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Exterior
open scoped BigOperators
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
def modeRank : Fin n ⊕ Fin n → ℕ
  | .inl i => i.val
  | .inr i => n + i.val
theorem modeRank_injective : Function.Injective (modeRank (n := n)) := by sorry
local instance FermionCreatorTriangularity_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
variable (b : Module.Basis (Fin n ⊕ Fin n) R V) (φ β a c : Fin n → R)
def prefixCreatorVector : Fin n ⊕ Fin n → V
  | .inl j => thetaCreatorVector b φ β a (suffixPolynomial φ j)
  | .inr j => xiCreatorVector b φ c (suffixPolynomial φ j)
def prefixCreatorMap : V →ₗ[R] V := b.constr R (prefixCreatorVector b φ β a c)
def prefixCreatorDiagonal : Fin n ⊕ Fin n → R
  | .inl j => β j * a j * ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (φ j - φ i)
  | .inr j => c j * ∏ i ∈ Finset.univ.filter (fun i ↦ j < i), (φ j - φ i)
def prefixCreatorWedge (k : ℕ) (t : Set.powersetCard (Fin n ⊕ Fin n) k) : ⋀[R]^k V := exteriorPower.map k (prefixCreatorMap b φ β a c)
  (b.exteriorPower k t)
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
abbrev RectangleIndex (h : Fin n → ℕ) :=
  {a : Fin n →₀ ℕ // ∀ i, a i < h i}
def rectangleIndexEquiv (h : Fin n → ℕ) :
    RectangleIndex h ≃ (∀ i : Fin n, Fin (h i)) where
  toFun a i := ⟨a.val i,a.property i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).val),fun i ↦ (a i).isLt⟩
  left_inv a := by apply Subtype.ext; ext i; rfl
  right_inv a := by funext i; apply Fin.ext; rfl
instance rectangleIndex_fintype (h : Fin n → ℕ) : Fintype (RectangleIndex h) :=
  Fintype.ofEquiv _ (rectangleIndexEquiv h).symm
end PaperVerification.Fermion.Newton
namespace PaperVerification.Fermion
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
def multiplyIntoQuotient (J : Ideal A) (g : A) : A →ₗ[K] A ⧸ J := (Ideal.Quotient.mkₐ K J).toLinearMap.comp (LinearMap.mul K A g)
theorem multiplyIntoQuotient_apply (J : Ideal A) (g a : A) : multiplyIntoQuotient (K := K) J g a = Ideal.Quotient.mk J (g * a) := by
  sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Exterior
def interleavedOddRank {n : ℕ} : Fin n ⊕ Fin n → ℕ
  | .inl i => 2 * i.val + 1
  | .inr i => 2 * i.val
theorem interleavedOddRank_injective (n : ℕ) : Function.Injective (@interleavedOddRank n) := by sorry
def interleavedOddOrder (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) := LinearOrder.lift' interleavedOddRank (interleavedOddRank_injective n)
def pairedPrefix (n i : ℕ) : Finset (Fin n ⊕ Fin n) := (Finset.univ.filter (fun j : Fin n ↦ j.val < i)).disjSum (Finset.univ.filter
  (fun j : Fin n ↦ j.val < i))
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion.Endpoint
inductive Mark
  | unmarked | theta | xi | double
  deriving DecidableEq
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion.Exterior
open scoped BigOperators
open Polynomial
open Endpoint
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
section
set_option backward.isDefEq.respectTransparency false
section
open scoped BigOperators
open MvPolynomial Exterior Endpoint
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
end
open MvPolynomial Exterior
open scoped BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}
def coupledOrdinaryMoment (d : PairedData (K := R) (n := n)) (k : ℕ) : PolynomialRing R n := moment d.phi (fun i ↦ C (d.beta i) * d.a i
  * d.b i) k
def coupledOrdinaryIdeal (d : PairedData (K := R) (n := n)) : Ideal (PolynomialRing R n) := Ideal.span (Set.range (fun k : Fin n ↦
  coupledOrdinaryMoment d k))
def creatorWordPolynomial (d : PairedData (K := R) (n := n)) (T : Finset (OddIndex n)) : PolynomialRing R n := ∏ j ∈ T,
  prefixCreatorDiagonal d.phi (fun i ↦ C (d.beta i)) d.a d.b j
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
def nonemptySubsets (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter Finset.Nonempty
def denominator (d : PairedData (K := K) (n := n)) : Coefficients d := (n.factorial : Coefficients d) * ∏ U ∈ nonemptySubsets n, ∑ i ∈
  U, beta d i
abbrev Ring (d : PairedData (K := K) (n := n)) := Localization.Away (denominator d)
def weight (d : PairedData (K := K) (n := n)) (i : Fin n) : Ring d := algebraMap (Coefficients d) (Ring d) (beta d i)
theorem allowed_weights (d : PairedData (K := K) (n := n)) : AllowedWeights (weight d) := by sorry
end PaperVerification.Fermion.Universal
namespace PaperVerification.Fermion
section
open MvPolynomial
variable {R : Type*} [CommRing R] {n : ℕ}
theorem highestPower_X_pow (r : Fin n → ℕ) (i : Fin n) (e : ℕ) : HasHighestPower r (X i^e : PolynomialRing R n) i e := by sorry
end
section
set_option backward.isDefEq.respectTransparency false
section
open MvPolynomial
open scoped BigOperators TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
def StrictData.pairedExtension (d : StrictData (K := R) (n := n)) :
    PairedData (K := R) (n := n) where
  positive_n := d.positive_n
  s := 1
  positive_s := Nat.zero_lt_one
  r := d.r
  u := d.r
  v := fun _ ↦ 0
  positive_r := d.positive_r
  degree_split := fun _ ↦ by simp only [add_zero,mul_one]
  beta := d.beta
  allowed_weights := d.allowed_weights
  phi := d.phi
  a := d.phi
  b := fun _ ↦ 1
  highest_phi := d.highest_phi
  highest_a := d.highest_phi
  highest_b := fun i ↦ by
    simpa only [pow_zero] using highestPower_X_pow d.r i 0
end
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators
variable {n : ℕ}
local instance FermionStrictPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
def strictWordBoxBounds (r : Fin n → ℕ) (T : Finset (OddIndex n)) (i : Fin n) : ℕ := r i*wordHeight T (i.val+1)
def StrictWordPolynomialIndex (r : Fin n → ℕ) (T : Finset (OddIndex n)) :=
  {a : RectangleIndex (strictWordBoxBounds r T) // ValidWord T}
instance strictWordPolynomialIndex_fintype (r : Fin n → ℕ) (T : Finset (OddIndex n)) :
    Fintype (StrictWordPolynomialIndex r T) := by
  classical
  unfold StrictWordPolynomialIndex
  infer_instance
abbrev StrictPowerIndex (r : Fin n → ℕ) := Sigma (StrictWordPolynomialIndex r)
end
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators TensorProduct
section
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionStrictCoupledIndependence_localInst_1 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
def StrictData.creatorData (d : StrictData (K := R) (n := n)) :
    PairedData (K := R) (n := n) where
  positive_n := d.positive_n
  s := 2
  positive_s := by decide
  r := d.r
  u := d.r
  v := d.r
  positive_r := d.positive_r
  degree_split := fun _ ↦ by omega
  beta := d.beta
  allowed_weights := d.allowed_weights
  phi := d.phi
  a := d.phi
  b := d.phi
  highest_phi := d.highest_phi
  highest_a := d.highest_phi
  highest_b := d.highest_phi
def strictCoupledClasses (d : StrictData (K := R) (n := n)) (z : StrictPowerIndex d.r) : StrictQuotient d.beta d.phi := (strictIdeal
  d.beta d.phi).ringCon.mkₐ R (monomial z.2.val.val 1 ⊗ₜ[R] (Pi.basisFun R (OddIndex n)).ExteriorAlgebra z.1)
end
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictCoupledIndependence_localInst_2 : LinearOrder (Fin n ⊕ Fin n) :=
  LinearOrder.lift' modeRank modeRank_injective
set_option maxHeartbeats 4000000
theorem strict_coupled_creator_diagonal_independent (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) (hT : ValidWord T) :
  LinearIndependent F (fun a : RectangleIndex (strictWordBoxBounds d.r T) ↦ Ideal.Quotient.mk (coupledOrdinaryIdeal d.pairedExtension)
  (monomial a.val 1*creatorWordPolynomial d.creatorData T)) := by sorry
attribute [local instance] FermionStrictCoupledIndependence_localInst_2
theorem strictCoupledClasses_linearIndependent (d : StrictData (K := F) (n := n)) : LinearIndependent F (strictCoupledClasses d) := by
  sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Paths
set_option backward.isDefEq.respectTransparency false
local instance FermionPathBoxes_localInst_1 (p : Prop) : Decidable p := Classical.propDecidable p
open Exterior Endpoint
open scoped BigOperators
variable {n : ℕ}
local instance FermionPathBoxes_localInst_2 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
def wordOfMarks (m : Fin n → Mark) : Finset (OddIndex n) := (Finset.univ.filter (fun i ↦ m i=.theta ∨ m i=.double)).disjSum
  (Finset.univ.filter (fun i ↦ m i=.xi ∨ m i=.double))
@[simp] theorem wordOfMarks_inl (m : Fin n → Mark) (i : Fin n) :
    Sum.inl i ∈ wordOfMarks m ↔ m i=.theta ∨ m i=.double := by sorry
@[simp] theorem wordOfMarks_inr (m : Fin n → Mark) (i : Fin n) :
    Sum.inr i ∈ wordOfMarks m ↔ m i=.xi ∨ m i=.double := by sorry
end PaperVerification.Fermion.Paths
namespace PaperVerification.Fermion
section
set_option backward.isDefEq.respectTransparency false
section
open Exterior Endpoint Newton
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
section
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
@[simp] theorem strictCoupledBasis_apply (d : StrictData (K := F) (n := n))
    (z : StrictPowerIndex d.r) : strictCoupledBasis d z=strictCoupledClasses d z := by sorry
end
section
open MvPolynomial Exterior
open scoped BigOperators TensorProduct
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictMultiplicityInitial_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
abbrev StrictCoefficientQuotient (d : StrictData (K := F) (n := n)) := PolynomialRing F n ⧸ coupledOrdinaryIdeal d.pairedExtension
def strictCoefficientProjection (d : StrictData (K := F) (n := n)) : PolynomialRing F n →ₐ[F] StrictCoefficientQuotient d :=
  Ideal.Quotient.mkₐ F (coupledOrdinaryIdeal d.pairedExtension)
theorem superPolynomialBasis_smul (p : PolynomialRing F n) (T : Finset (OddIndex n)) : p • superPolynomialBasis (K := F) T= p ⊗ₜ[F]
  (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T := by sorry
def strictMultiplicityCreator (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) : ExteriorAlgebra (StrictCoefficientQuotient
  d) (OddModule (StrictCoefficientQuotient d) n) := prefixCreatorWedge (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n)) (fun i
  ↦ strictCoefficientProjection d (d.phi i)) (fun i ↦ algebraMap F (StrictCoefficientQuotient d) (d.beta i)) (fun i ↦
  strictCoefficientProjection d (d.phi i)) (fun i ↦ strictCoefficientProjection d (d.phi i)) T.card ⟨T,rfl⟩
def strictMultiplicityTest (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) : SuperRing F n →ₗ[F] StrictCoefficientQuotient
  d := ((((coefficientPairing (Pi.basisFun (StrictCoefficientQuotient d) (OddIndex n))).flip (strictMultiplicityCreator d
  T)).restrictScalars F).comp (superSpecialization (strictCoefficientProjection d)).toLinearMap)
theorem strictMultiplicityTest_same (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) (p : PolynomialRing F n) :
  strictMultiplicityTest d T (p • superPolynomialBasis (K := F) T)= multiplyIntoQuotient (K := F) (coupledOrdinaryIdeal
  d.pairedExtension) (creatorWordPolynomial d.creatorData T) p := by sorry
theorem strictMultiplicityTest_higher (d : StrictData (K := F) (n := n)) (S T : Finset (OddIndex n)) (hST : S≠T) (hweight :
  multiplicityWordWeight S≤ multiplicityWordWeight T) (p : PolynomialRing F n) : strictMultiplicityTest d S (p • superPolynomialBasis (K
  := F) T)=0 := by sorry
theorem strictMultiplicityTest_kills (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) : (((strictIdeal d.beta
  d.phi).ringCon.mkₐ F).toLinearMap).ker≤ (strictMultiplicityTest d T).ker := by sorry
def strictMultiplicityPresentation (d : StrictData (K := F) (n := n)) :
    BlockInitial.TriangularPresentation (N := StrictCoefficientQuotient d)
      (superPolynomialBasis (K := F)) multiplicityWordWeight
      (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap)
      (StrictWordPolynomialIndex d.r) where
  polynomial := fun T a ↦ monomial a.val.val 1
  basis := strictCoupledBasis d
  basis_apply := by
    intro z
    rw [strictCoupledBasis_apply,strictCoupledClasses,superPolynomialBasis_smul]
    rfl
  test := strictMultiplicityTest d
  diagonal := fun T ↦ multiplyIntoQuotient (K := F) (coupledOrdinaryIdeal d.pairedExtension)
    (creatorWordPolynomial d.creatorData T)
  test_same := strictMultiplicityTest_same d
  test_higher := strictMultiplicityTest_higher d
  kill := strictMultiplicityTest_kills d
  independent := by
    intro T
    by_cases hT : ValidWord T
    · have hi := (strict_coupled_creator_diagonal_independent d T hT).comp
        (fun a : StrictWordPolynomialIndex d.r T ↦ a.val) Subtype.val_injective
      convert hi using 1
      funext a
      rw [multiplyIntoQuotient_apply,mul_comm]
      rfl
    · haveI : IsEmpty (StrictWordPolynomialIndex d.r T) := ⟨fun a ↦ hT a.property⟩
      exact linearIndependent_empty_type
def strictMultiplicityInitialGenerators (d : StrictData (K := F) (n := n)) :
    Set (SuperRing F n) :=
  {y | ∃ x∈strictIdeal d.beta d.phi,∃ r,
    BlockInitial.LowerBound (superPolynomialBasis (K := F)) multiplicityWordWeight r x ∧
      BasisFiltered.component (superPolynomialBasis (K := F)) multiplicityWordWeight r x=y}
end
open Exterior
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityInitialAlgebra_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictMultiplicityInitialIdeal (d : StrictData (K := F) (n := n)) : TwoSidedIdeal (SuperRing F n) := TwoSidedIdeal.span
  (strictMultiplicityInitialGenerators d)
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
    by_cases hxi : b.repr x i=0
    · apply hy i
      simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
    · exact hx i hxi
  smul_mem' := by
    intro c x hx i hi
    apply hx i
    intro hz
    exact hi (by simp only [map_smul,Finsupp.smul_apply,hz,smul_zero])
end PaperVerification.Fermion.BlockInitial
namespace PaperVerification.Fermion.BlockInitial.TriangularPresentation
open scoped BigOperators
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  {b : Module.Basis J P M} {weight : J → ℕ} {q : M →ₗ[K] Q}
  {D : J → Type*} [∀ j,Fintype (D j)]
  (h : TriangularPresentation (N := N) b weight q D)
theorem initial_quotient_linearIndependent : LinearIndependent K (fun z:Sigma D ↦ (initialMin b weight q.ker).mkQ (h.representative z))
  := by sorry
theorem initial_quotient_span : Submodule.span K (Set.range (fun z:Sigma D ↦ (initialMin b weight q.ker).mkQ (h.representative z)))=⊤
  := by sorry
def initialQuotientBasis : Module.Basis (Sigma D) K (M ⧸ initialMin b weight q.ker) := Module.Basis.mk
  h.initial_quotient_linearIndependent h.initial_quotient_span.ge
end PaperVerification.Fermion.BlockInitial.TriangularPresentation
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
section
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityBlocks_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
abbrev MultiplicityVector (n : ℕ) := Fin n → Fin 3
end
open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictWeightRees_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictBasisMultiplicityWeight (d : StrictData (K := F) (n := n)) (z : StrictPowerIndex d.r) : ℕ := multiplicityWordWeight z.1
theorem strictBasisMultiplicityWeight_multiplicative (d : StrictData (K := F) (n := n)) : WeightRees.Multiplicative (K := F) (A :=
  StrictQuotient d.beta d.phi) (I := StrictPowerIndex d.r) (strictCoupledBasis d) (strictBasisMultiplicityWeight d) := by sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion.WeightRees
open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype I]
  (b : Module.Basis I K A) (weight : I → ℕ) (hmul : Multiplicative b weight)
section
include hmul
theorem multiplicationPolynomial_eval_zero (i j k : I) :
    (multiplicationPolynomial b weight i j k).eval 0=
      if weight k=weight i+weight j then b.repr (b i*b j) k else 0 := by sorry
end
theorem unitPolynomial_eval_zero (i : I) :
    (Polynomial.monomial (weight i) (b.repr 1 i)).eval 0=
      if weight i=0 then b.repr 1 i else 0 := by sorry
end PaperVerification.Fermion.WeightRees
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior BasisFiltered
open scoped BigOperators TensorProduct PaperVerification.Fermion.WeightRees
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictWeightReesFibers_localInst_1 : LinearOrder (OddIndex n) := LinearOrder.lift' modeRank modeRank_injective
abbrev StrictMultiplicityInitialQuotient (d : StrictData (K := F) (n := n)) := (strictMultiplicityInitialIdeal d).ringCon.Quotient
def strictInitialProjection (d : StrictData (K := F) (n := n)) : SuperRing F n →ₐ[F] StrictMultiplicityInitialQuotient d :=
  (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
theorem strictInitialModule_eq_kernel (d : StrictData (K := F) (n := n)) : BlockInitial.initialMin (superPolynomialBasis (K := F))
  multiplicityWordWeight (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap).ker = (strictInitialProjection d).toLinearMap.ker :=
  by sorry
def strictInitialToRingEquiv (d : StrictData (K := F) (n := n)) : (SuperRing F n ⧸ BlockInitial.initialMin (superPolynomialBasis (K :=
  F)) multiplicityWordWeight (((strictIdeal d.beta d.phi).ringCon.mkₐ F).toLinearMap).ker) ≃ₗ[F] StrictMultiplicityInitialQuotient d :=
  (Submodule.quotEquivOfEq _ _ (strictInitialModule_eq_kernel d)).trans ((strictInitialProjection
  d).toLinearMap.quotKerEquivOfSurjective ((strictMultiplicityInitialIdeal d).ringCon.mkₐ_surjective (α := F)))
def strictMultiplicityInitialBasis (d : StrictData (K := F) (n := n)) : Module.Basis (StrictPowerIndex d.r) F
  (StrictMultiplicityInitialQuotient d) := (strictMultiplicityPresentation d).initialQuotientBasis.map (strictInitialToRingEquiv d)
theorem strictInitial_basis_mul (d : StrictData (K := F) (n := n)) (i j : StrictPowerIndex d.r) : strictMultiplicityInitialBasis d i *
  strictMultiplicityInitialBasis d j = ∑ k : StrictPowerIndex d.r, (WeightRees.multiplicationPolynomial (K := F) (A := StrictQuotient
  d.beta d.phi) (I := StrictPowerIndex d.r) (strictCoupledBasis d) (strictBasisMultiplicityWeight d) i j k).eval 0 •
  strictMultiplicityInitialBasis d k := by sorry
theorem strictInitial_basis_one (d : StrictData (K := F) (n := n)) : (1 : StrictMultiplicityInitialQuotient d) = ∑ k : StrictPowerIndex
  d.r, (Polynomial.monomial (strictBasisMultiplicityWeight d k) ((strictCoupledBasis d).repr 1 k)).eval 0 •
  strictMultiplicityInitialBasis d k := by sorry
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
variable {R A}
abbrev filtration (f : Filtration R A) := f.piece
def nextStep (f : Filtration R A) (k : ℕ) : Submodule R A := f.piece (k+1)
def nextRestricted (f : Filtration R A) (k : ℕ) : Submodule R (filtration f k) := (nextStep f k).comap (filtration f k).subtype
@[simp] theorem mem_nextRestricted_iff (f : Filtration R A) (k : ℕ)
    (x : filtration f k) : x ∈ nextRestricted f k ↔ (x : A) ∈ nextStep f k := by sorry
theorem mul_mem_filtration (f : Filtration R A) {i j : ℕ} {x y : A} (hx : x ∈ filtration f i) (hy : y ∈ filtration f j) : x*y ∈
  filtration f (i+j) := by sorry
theorem one_mem_filtration (f : Filtration R A) : (1 : A) ∈ filtration f 0 := by sorry
theorem algebraMap_mem_filtration (f : Filtration R A) (r : R) : algebraMap R A r ∈ filtration f 0 := by sorry
abbrev GradedPiece (f : Filtration R A) (k : ℕ) : Type w := filtration f k ⧸ nextRestricted f k
abbrev AssociatedGraded (f : Filtration R A) : Type w := ⨁ k : ℕ, GradedPiece f k
noncomputable def filteredMul (f : Filtration R A) (i j : ℕ) :
    filtration f i →ₗ[R] filtration f j →ₗ[R] filtration f (i + j) :=
  { toFun := fun x =>
      { toFun := fun y => ⟨(x : A)*y,mul_mem_filtration f x.property y.property⟩
        map_add' := fun y z => Subtype.ext (mul_add (x : A) y z)
        map_smul' := fun c y => Subtype.ext (mul_smul_comm c (x : A) (y : A)) }
    map_add' := fun x y => LinearMap.ext (fun z => Subtype.ext (add_mul (x : A) y z))
    map_smul' := fun c x => LinearMap.ext (fun y => Subtype.ext (smul_mul_assoc c (x : A) y)) }
noncomputable def gradedPreMul (f : Filtration R A) (i j : ℕ) : filtration f i →ₗ[R] filtration f j →ₗ[R] GradedPiece f (i + j) :=
  (filteredMul f i j).compr₂ (Submodule.mkQ _)
theorem gradedPreMul_mem_ker_left (f : Filtration R A) (i j : ℕ) : nextRestricted f i ≤ (gradedPreMul f i j).ker := by sorry
theorem gradedPreMul_mem_ker_right (f : Filtration R A) (i j : ℕ) : nextRestricted f j ≤ (gradedPreMul f i j).flip.ker := by sorry
noncomputable def gradedMul (f : Filtration R A) (i j : ℕ) : GradedPiece f i →ₗ[R] GradedPiece f j →ₗ[R] GradedPiece f (i + j) :=
  (gradedPreMul f i j).liftQ₂ _ _ (gradedPreMul_mem_ker_left f i j) (gradedPreMul_mem_ker_right f i j)
theorem gradedMul_assoc (f : Filtration R A) (i j k : ℕ) (x : GradedPiece f i) (y : GradedPiece f j) (z : GradedPiece f k) : cast
  (congrArg (GradedPiece f) (Nat.add_assoc i j k)) (gradedMul f (i + j) k (gradedMul f i j x y) z) = gradedMul f i (j + k) x (gradedMul
  f j k y z) := by sorry
noncomputable def gradedOne (f : Filtration R A) : GradedPiece f 0 := Submodule.Quotient.mk ⟨1, one_mem_filtration f⟩
noncomputable def gradedAlgebraMap₀ (f : Filtration R A) :
    R →+ GradedPiece f 0 where
  toFun r := Submodule.Quotient.mk
    ⟨algebraMap R (A) r, algebraMap_mem_filtration f r⟩
  map_zero' := by simp
  map_add' r s := by
    rw [← Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext (map_add (algebraMap R (A)) r s)
@[simp] theorem gradedAlgebraMap₀_one (f : Filtration R A) :
    gradedAlgebraMap₀ f 1 = gradedOne f := by sorry
@[simp] theorem gradedOne_mul (f : Filtration R A) (k : ℕ)
    (x : GradedPiece f k) :
    gradedMul f 0 k (gradedOne f) x =
      cast (congrArg (GradedPiece f) (Nat.zero_add k).symm) x := by sorry
@[simp] theorem gradedMul_one (f : Filtration R A) (k : ℕ)
    (x : GradedPiece f k) :
    gradedMul f k 0 x (gradedOne f) =
      cast (congrArg (GradedPiece f) (Nat.add_zero k).symm) x := by sorry
noncomputable instance gradedGOne {f : Filtration R A} :
    GradedMonoid.GOne (GradedPiece f) where
  one := gradedOne f
noncomputable instance gradedGMul {f : Filtration R A} :
    GradedMonoid.GMul (GradedPiece f) where
  mul {i j} := fun x y => gradedMul f i j x y
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
@[simp] theorem gradedAlgebraMap₀_mul (f : Filtration R A) (r : R) (k : ℕ)
    (x : GradedPiece f k) :
    cast (congrArg (GradedPiece f) (Nat.zero_add k))
      (gradedMul f 0 k (gradedAlgebraMap₀ f r) x) = r • x := by sorry
@[simp 1100] theorem gradedAlgebraMap₀_mul_algebraMap₀ (f : Filtration R A) (r s : R) :
    gradedMul f 0 0 (gradedAlgebraMap₀ f r)
      (gradedAlgebraMap₀ f s) = gradedAlgebraMap₀ f (r * s) := by sorry
theorem gradedAlgebraMap₀_commutes (f : Filtration R A) (r : R) (k : ℕ) (x : GradedPiece f k) : cast (congrArg (GradedPiece f)
  ((Nat.zero_add k).trans (Nat.add_zero k).symm)) (gradedMul f 0 k (gradedAlgebraMap₀ f r) x) = gradedMul f k 0 x (gradedAlgebraMap₀ f
  r) := by sorry
noncomputable instance gradedGSemiring {f : Filtration R A} :
    DirectSum.GSemiring (GradedPiece f) := by
  exact @DirectSum.GRing.toGSemiring ℕ (GradedPiece f) _ _
    (gradedGRing (f := f))
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
noncomputable instance associatedGradedRing {f : Filtration R A} :
    Ring (AssociatedGraded f) := by
  letI : ∀ k, AddCommGroup (GradedPiece f k) := fun _ => inferInstance
  infer_instance
end PaperVerification.Fermion.DescendingAlgebra
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M Q I E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]
  (b : Module.Basis I R M) (w : I → ℕ)
def homogeneousPiece (d : ℕ) : Submodule R M where
  carrier := {x | Homogeneous b w d x}
  zero_mem' := by intro i hi; exact (hi (by simp)).elim
  add_mem' := by
    intro x y hx hy i hi
    by_cases hxi : b.repr x i=0
    · apply hy i
      simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
    · exact hx i hxi
  smul_mem' := by
    intro c x hx i hi
    apply hx i
    intro hz
    exact hi (by simp only [map_smul,Finsupp.smul_apply,hz,smul_zero])
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion.DescendingBasis
open scoped Classical BigOperators DirectSum
open BasisFiltered DescendingAlgebra
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
def componentMap (d : ℕ) :
    (filtration b w hmul).piece d →ₗ[K] homogeneousPiece b w d where
  toFun x := ⟨component b w d x,homogeneous_component b w d x⟩
  map_add' x y := Subtype.ext ((component b w d).map_add x y)
  map_smul' r x := Subtype.ext ((component b w d).map_smul r x)
theorem componentMap_ker (d : ℕ) : LinearMap.ker (componentMap b w hmul d)= nextRestricted (filtration b w hmul) d := by sorry
theorem componentMap_surjective (d : ℕ) : Function.Surjective (componentMap b w hmul d) := by sorry
def pieceEquiv (d : ℕ) : GradedPiece (filtration b w hmul) d ≃ₗ[K] homogeneousPiece b w d := (Submodule.quotEquivOfEq _ _
  (componentMap_ker b w hmul d).symm).trans ((componentMap b w hmul d).quotKerEquivOfSurjective (componentMap_surjective b w hmul d))
theorem homogeneous_internal : DirectSum.IsInternal (homogeneousPiece b w) := by sorry
def totalEquiv : AssociatedGraded (filtration b w hmul) ≃ₗ[K] A := (DirectSum.congrLinearEquiv (pieceEquiv b w hmul)).trans
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (homogeneousPiece b w)) (homogeneous_internal b w))
variable {B : Type*} [Ring B] [Algebra K B] (c : Module.Basis I K B)
def comparison : AssociatedGraded (filtration b w hmul) ≃ₗ[K] B := (totalEquiv b w hmul).trans (b.equiv c (Equiv.refl I))
theorem comparison_one
    (hone : (1 : B)=∑ i,if w i=0 then b.repr 1 i • c i else 0) :
    comparison b w hmul c 1=1 := by sorry
theorem comparison_mul
    (hprod : ∀ i j,c i*c j=∑ k,
      if w k=w i+w j then b.repr (b i*b j) k • c k else 0)
    (x y : AssociatedGraded (filtration b w hmul)) :
    comparison b w hmul c (x*y)=comparison b w hmul c x*comparison b w hmul c y := by sorry
def comparisonAlgEquiv
    (hone : (1 : B)=∑ i,if w i=0 then b.repr 1 i • c i else 0)
    (hprod : ∀ i j,c i*c j=∑ k,
      if w k=w i+w j then b.repr (b i*b j) k • c k else 0) :
    AssociatedGraded (filtration b w hmul) ≃ₐ[K] B :=
  AlgEquiv.ofLinearEquiv (comparison b w hmul c)
    (comparison_one b w hmul c hone) (comparison_mul b w hmul c hprod)
end PaperVerification.Fermion.DescendingBasis
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators DirectSum
open MvPolynomial Exterior
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityAssociatedGraded_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
abbrev strictMultiplicityDescendingFiltration (d : StrictData (K := F) (n := n)) : DescendingAlgebra.Filtration F (StrictQuotient
  d.beta d.phi) := DescendingBasis.filtration (K := F) (A := StrictQuotient d.beta d.phi) (strictCoupledBasis d)
  (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d)
abbrev StrictMultiplicityAssociatedGraded (d : StrictData (K := F) (n := n)) := DescendingAlgebra.AssociatedGraded
  (strictMultiplicityDescendingFiltration d)
attribute [local instance] FermionMultiplicityAssociatedGraded_localInst_1
set_option maxHeartbeats 1000000
def strictMultiplicityAssociatedGradedEquiv (d : StrictData (K := F) (n := n)) :
    StrictMultiplicityAssociatedGraded d ≃ₐ[F] StrictMultiplicityInitialQuotient d := by
  let b := strictCoupledBasis d
  let w := strictBasisMultiplicityWeight d
  have hweight := strictBasisMultiplicityWeight_multiplicative d
  let c := strictMultiplicityInitialBasis d
  let makeEquiv := DescendingBasis.comparisonAlgEquiv
    (K := F) (A := StrictQuotient d.beta d.phi) (I := StrictPowerIndex d.r)
    (B := StrictMultiplicityInitialQuotient d)
    (b := b) (w := w) (hmul := hweight) (c := c)
  let e := makeEquiv
    (by
      dsimp only [b,w,c]
      rw [strictInitial_basis_one d]
      apply Finset.sum_congr rfl
      intro i hi
      rw [WeightRees.unitPolynomial_eval_zero (K := F)
        (A := StrictQuotient d.beta d.phi) (strictCoupledBasis d)
        (strictBasisMultiplicityWeight d) i]
      split_ifs <;> simp only [zero_smul])
    (by
      dsimp only [b,w,c]
      intro i j
      rw [strictInitial_basis_mul d i j]
      apply Finset.sum_congr rfl
      intro k hk
      rw [WeightRees.multiplicationPolynomial_eval_zero (K := F)
        (A := StrictQuotient d.beta d.phi) (strictCoupledBasis d)
        (strictBasisMultiplicityWeight d) (strictBasisMultiplicityWeight_multiplicative d) i j k]
      split_ifs <;> simp only [zero_smul])
  exact e
end PaperVerification.Fermion
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
namespace PaperVerification.Fermion.NaturalExteriorTensor
open scoped TensorProduct
variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] {n : ℕ}
def assemble (d : Fin n → ℕ) (e : Fin n → V →ₗ[R] W) : (⨂[R] i : Fin n, (⋀[R]^(d i) V)) →ₗ[R] ExteriorAlgebra R W :=
  PiTensorProduct.lift <| (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R W)).compLinearMap (fun i ↦ (ExteriorAlgebra.map (e
  i)).toLinearMap.comp (Submodule.subtype _))
end PaperVerification.Fermion.NaturalExteriorTensor
namespace PaperVerification.Fermion.NaturalColor
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
def embedding (i : Fin n) : (Fin 2 → R) →ₗ[R] OddModule R n where
  toFun v := Sum.elim (fun j ↦ if j=i then v 0 else 0)
    (fun j ↦ if j=i then v 1 else 0)
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.add_apply] <;>
      split_ifs <;> simp
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,
      smul_eq_mul,RingHom.id_apply] <;> split_ifs <;> simp
def assemble (d : Fin n → ℕ) : (⨂[R] i : Fin n, (⋀[R]^(d i) (Fin 2 → R))) →ₗ[R] ExteriorAlgebra R (OddModule R n) :=
  NaturalExteriorTensor.assemble (R := R) (V := Fin 2 → R) (W := OddModule R n) d (embedding (R := R))
end PaperVerification.Fermion.NaturalColor
namespace PaperVerification.Fermion.ColorPaths
open scoped DirectSum
open scoped Classical BigOperators TensorProduct
open Endpoint Paths
def markSubset : Mark → Finset (Fin 2)
  | .unmarked => ∅
  | .theta => {0}
  | .xi => {1}
  | .double => {0,1}
def subsetMark (s : Finset (Fin 2)) : Mark :=
  if (0 : Fin 2)∈s then if (1 : Fin 2)∈s then .double else .theta
  else if (1 : Fin 2)∈s then .xi else .unmarked
@[simp] theorem subsetMark_markSubset (a : Mark) : subsetMark (markSubset a)=a := by sorry
@[simp] theorem markSubset_subsetMark (s : Finset (Fin 2)) : markSubset (subsetMark s)=s := by sorry
def markSubsetEquiv : Mark ≃ Finset (Fin 2) := ⟨markSubset,subsetMark,subsetMark_markSubset,markSubset_subsetMark⟩
variable {n : ℕ}
variable (R : Type*) [CommRing R]
abbrev ExteriorColorTensor (m : MultiplicityVector n) := ⨂[R] i : Fin n, (⋀[R]^((m i).val) (Fin 2 → R))
end PaperVerification.Fermion.ColorPaths
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct DirectSum
  PaperVerification.Fermion.WeightRees
open MvPolynomial Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance theoremEightOneOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
set_option maxHeartbeats 1000000
theorem palomarColorProducts (hn : 0<n) :
    let pure := fun (m : MultiplicityVector n) (p : PolynomialRing F n)
          (x : ColorPaths.ExteriorColorTensor F m) ↦
        (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
          (strictInitialProjection (data (F := F) hn)
            (p ⊗ₜ[F] NaturalColor.assemble (fun i ↦ (m i).val) x))
    (Submodule.span F (Set.range (fun z :
    Σ m : MultiplicityVector n,PolynomialRing F n × ColorPaths.ExteriorColorTensor F m ↦
      pure z.1 z.2.1 z.2.2))=⊤) ∧
    (∀ (m l : MultiplicityVector n) (p q : PolynomialRing F n)
      (x : ColorPaths.ExteriorColorTensor F m) (y : ColorPaths.ExteriorColorTensor F l),
    pure m p x*pure l q y=
      (strictMultiplicityAssociatedGradedEquiv (data (F := F) hn)).symm
        (strictInitialProjection (data (F := F) hn)
          ((p*q) ⊗ₜ[F] (NaturalColor.assemble (fun i ↦ (m i).val) x*
            NaturalColor.assemble (fun i ↦ (l i).val) y)))) := by sorry
end PaperVerification.Fermion.TypeA
