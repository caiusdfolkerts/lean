module
public import Mathlib

/-! Initial coefficient ideals, their Hilbert functions, and the graded and total characters of two-fermion coinvariants. -/
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
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ)
def component (d : ℕ) : M →ₗ[R] M where
  toFun x := b.repr.symm ((b.repr x).filter (fun i ↦ w i = d))
  map_add' x y := by rw [map_add,Finsupp.filter_add,map_add]
  map_smul' a x := by rw [map_smul,Finsupp.filter_smul,map_smul,RingHom.id_apply]
def Homogeneous (d : ℕ) (x : M) : Prop := ∀ i, PalomarFermion.coordinates b x i ≠ 0 → w i = d
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion.BlockInitial
open scoped BigOperators
open BasisFiltered
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  (b : Module.Basis J P M) (weight : J → ℕ)
def LowerBound (r : ℕ) (x : M) : Prop := ∀ j,PalomarFermion.coordinates b x j≠0 → r≤weight j
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
namespace PaperVerification.Fermion
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
def principalColon (J : Ideal A) (g : A) : Ideal A := J.colon ({g} : Set A)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Exterior
def interleavedOddRank {n : ℕ} : Fin n ⊕ Fin n → ℕ :=
  Sum.elim (fun i => 2 * i.val + 1) (fun i => 2 * i.val)
theorem interleavedOddRank_injective (n : ℕ) : Function.Injective (@interleavedOddRank n) := by sorry
def interleavedOddOrder (n : ℕ) : LinearOrder (Fin n ⊕ Fin n) := LinearOrder.lift' interleavedOddRank (interleavedOddRank_injective n)
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion
section
set_option backward.isDefEq.respectTransparency false
section
open scoped TensorProduct BigOperators
variable {K : Type*} [CommRing K] {n : ℕ}
variable [LinearOrder (OddIndex n)]
def superPolynomialBasis : Module.Basis (Finset (OddIndex n)) (PolynomialRing K n) (SuperRing K n) := ((Pi.basisFun K (OddIndex
  n)).ExteriorAlgebra).baseChange (PolynomialRing K n)
end
open MvPolynomial Exterior
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionCreatorPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
def wordMultiplicity (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  (if Sum.inl i ∈ T then 1 else 0) + (if Sum.inr i ∈ T then 1 else 0)
end
open MvPolynomial
open scoped BigOperators TensorProduct
variable {K : Type*} [CommRing K] {n : ℕ} [LinearOrder (OddIndex n)]
abbrev SuperMonomialIndex (n : ℕ) := (Fin n →₀ ℕ) × Finset (OddIndex n)
def superMonomialBasis : Module.Basis (SuperMonomialIndex n) K (SuperRing K n) := (basisMonomials (Fin n) K).tensorProduct (Pi.basisFun
  K (OddIndex n)).ExteriorAlgebra
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
open MvPolynomial Exterior
open scoped BigOperators TensorProduct
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictMultiplicityInitial_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictMultiplicityInitialGenerators (d : StrictData (K := F) (n := n)) :
    Set (SuperRing F n) :=
  {y | ∃ x∈strictIdeal d.beta d.phi,∃ r,
    BlockInitial.LowerBound (superPolynomialBasis (K := F)) multiplicityWordWeight r x ∧
      BasisFiltered.component (superPolynomialBasis (K := F)) multiplicityWordWeight r x=y}
end
section
open Exterior
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityInitialAlgebra_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def strictMultiplicityInitialIdeal (d : StrictData (K := F) (n := n)) : TwoSidedIdeal (SuperRing F n) := TwoSidedIdeal.span
  (strictMultiplicityInitialGenerators d)
end
set_option backward.isDefEq.respectTransparency false
open MvPolynomial Exterior
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityBlocks_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
abbrev MultiplicityVector (n : ℕ) := Fin n → Fin 3
theorem wordMultiplicity_lt_three (T : Finset (OddIndex n)) (i : Fin n) :
    wordMultiplicity T i < 3 := by
  classical
  by_cases hθ : Sum.inl i ∈ T <;> by_cases hξ : Sum.inr i ∈ T <;>
    simp only [wordMultiplicity, hθ, hξ, if_true, if_false] <;> omega
def wordMultiplicityVector (T : Finset (OddIndex n)) : MultiplicityVector n :=
  fun i => ⟨wordMultiplicity T i, wordMultiplicity_lt_three T i⟩
end PaperVerification.Fermion
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M Q I E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]
  (b : Module.Basis I R M) (w : I → ℕ)
theorem homogeneousZero (d : ℕ) : Homogeneous b w d (0 : M) := by sorry
theorem homogeneousAdd {d : ℕ} {x y : M} (hx : Homogeneous b w d x) (hy : Homogeneous b w d y) : Homogeneous b w d (x+y) := by sorry
theorem homogeneousSmul {d : ℕ} {x : M} (hx : Homogeneous b w d x) (c : R) : Homogeneous b w d (c • x) := by sorry
def homogeneousPiece (d : ℕ) : Submodule R M where
  carrier := {x | Homogeneous b w d x}
  zero_mem' := homogeneousZero b w d
  add_mem' := homogeneousAdd b w
  smul_mem' := fun c _ hx => homogeneousSmul b w hx c
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion
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
def powerSum (k : ℕ) : PolynomialRing F n := ∑ i,(X i)^(k+1)
def ordinaryIdeal : Ideal (PolynomialRing F n) := Ideal.span (Set.range (fun k : Fin n ↦ powerSum (F := F) k.val))
def factor (m : MultiplicityVector n) : PolynomialRing F n := ∏ i,(X i*∏ j∈Finset.Ioi i,(X i-X j))^(m i).val
def coefficientIdeal (m : MultiplicityVector n) : Ideal (PolynomialRing F n) := principalColon ordinaryIdeal (factor m)
def arrival (m : MultiplicityVector n) (i : Fin n) : ℤ := ((i.val+1 : ℕ) : ℤ)-((∑ j∈Finset.Iic i,(m j).val : ℕ) : ℤ)
def Admissible (m : MultiplicityVector n) : Prop := ∀ i,(1 : ℤ)≤arrival m i
def initialIdeal (hn : 0<n) : TwoSidedIdeal (SuperRing F n) := strictMultiplicityInitialIdeal (data hn)
end PaperVerification.Fermion.TypeA
namespace List
variable {α β : Type*} [LinearOrder α] [LinearOrder β]
def isDescent (l : List α) (i : ℕ) : Bool :=
  if h : i + 1 < l.length then
    decide (l[i + 1]'h < l[i]'(Nat.lt_of_succ_lt h))
  else false
def isAscent (l : List α) (i : ℕ) : Bool :=
  if h : i + 1 < l.length then
    decide (l[i]'(Nat.lt_of_succ_lt h) < l[i + 1]'h)
  else false
def descentSet (l : List α) : Finset ℕ := (Finset.range l.length).filter (fun i => isDescent l i)
def ascentSet (l : List α) : Finset ℕ := (Finset.range l.length).filter (fun i => isAscent l i)
end List
namespace Equiv.Perm
def descentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ := (List.ofFn σ).descentSet
def ascentSet {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset ℕ := (List.ofFn σ).ascentSet
def descentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.descentSet.card
def ascentCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := σ.ascentSet.card
end Equiv.Perm
namespace PaperVerification.Fermion.Eulerian
open scoped Classical BigOperators Polynomial
open Polynomial Equiv.Perm
variable {R : Type*} [CommSemiring R]
def permutationPolynomial (n : ℕ) (a b : R) : R := ∑ σ : Equiv.Perm (Fin n), a^σ.ascentCount*b^σ.descentCount
end PaperVerification.Fermion.Eulerian
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
theorem diagonal_trace_eq_eulerian (hn : 0<n) (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
  LinearMap.trace F (StrictQuotient (fun _ ↦ (1 : F)) (fun i : Fin n ↦ MvPolynomial.X i)) (ColorAction.quotientEquiv g (fun i : Fin n ↦
  MvPolynomial.X i)).toLinearMap = Eulerian.permutationPolynomial n (1+g.val 0 0) (1+g.val 1 1) := by sorry
end PaperVerification.Fermion.TypeA
namespace PaperVerification.Fermion.ColorPaths
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open Exterior
variable {R : Type*} [CommSemiring R] {n : ℕ}
local instance colorMultiplicityEnumerationDecidableEq (n : ℕ) : DecidableEq (OddIndex n) :=
  (interleavedOddOrder n).toDecidableEq
def singleCount (m : MultiplicityVector n) : ℕ := (Finset.univ.filter (fun i ↦ (m i).val=1)).card
def doubleCount (m : MultiplicityVector n) : ℕ := (Finset.univ.filter (fun i ↦ (m i).val=2)).card
def qNumber (q : R) (d : ℕ) : R := ∑ k : Fin d,q^k.val
def arrivalBound (m : MultiplicityVector n) (i : Fin n) : ℕ := (TypeA.arrival m i).toNat
def multiplicityBoxPolynomial (q : R) (m : MultiplicityVector n) : R := ∏ i,qNumber q (arrivalBound m i)
end PaperVerification.Fermion.ColorPaths
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
section
open scoped BigOperators DirectSum
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance FermionMultiplicityQuotientDecomposition_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective
abbrev CoefficientQuotient (m : MultiplicityVector n) := PolynomialRing F n ⧸ coefficientIdeal (F := F) m
end
section
open scoped Classical BigOperators
open MvPolynomial BasisFiltered
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
def coefficientPolynomialPiece (m : MultiplicityVector n) (k : ℕ) : Submodule F (CoefficientQuotient (F := F) m) :=
  (homogeneousSubmodule (Fin n) F k).map (Ideal.Quotient.mkₐ F (coefficientIdeal m)).toLinearMap
end
section
open scoped Classical BigOperators TensorProduct DirectSum
open MvPolynomial Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance theoremEightOneOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
set_option maxHeartbeats 1000000
theorem palomarColorCoefficients (hn : 0<n) : (∀ z : SuperRing F n,z∈initialIdeal hn ↔ ∀ T,(superPolynomialBasis (K := F)).repr z
  T∈coefficientIdeal (wordMultiplicityVector T)) ∧ (∀ m : MultiplicityVector n,¬Admissible m → coefficientIdeal (F := F) m=⊤) ∧ (∀ (m :
  MultiplicityVector n),Admissible m → ∀ k : ℕ, (Module.finrank F (coefficientPolynomialPiece (F := F) m k) : F)=
  (ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m).coeff k) := by sorry
end
section
open scoped Classical BigOperators
open Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance colorGradedTraceOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def polynomialDegree (z : SuperMonomialIndex n) : ℕ := ∑ i,z.1 i
def polynomialPiece (hn : 0<n) (k : ℕ) : Submodule F (StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi) :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F)) polynomialDegree k).map ((strictIdeal (data (F := F) hn).beta (data (F
  := F) hn).phi).ringCon.mkₐ F).toLinearMap
theorem diagonal_preserves_polynomialPiece (hn : 0<n) (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 :
  g.val 1 0=0) (x : StrictQuotient (data (F := F) hn).beta (data (F := F) hn).phi) (hx : x∈polynomialPiece (F := F) hn k) :
  ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i) x ∈ polynomialPiece (F := F) hn k := by sorry
def diagonalPolynomialPieceMap (hn : 0<n) (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
  polynomialPiece (F := F) hn k →ₗ[F] polynomialPiece (F := F) hn k := (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X
  i)).toLinearMap.restrict (diagonal_preserves_polynomialPiece (F := F) hn k g h01 h10)
theorem equation_22_diagonal_trace (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    LinearMap.trace F (polynomialPiece (F := F) hn k) (diagonalPolynomialPieceMap (F := F) hn k g h01 h10)=
      (∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m*
          (Polynomial.C (g.val 0 0)+Polynomial.C (g.val 1 1))^ColorPaths.singleCount m*
          (Polynomial.C (g.val 0 0)*Polynomial.C (g.val 1 1))^ColorPaths.doubleCount m else 0).coeff k := by sorry
end
open scoped Classical BigOperators TensorProduct
open Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
def quotientColorRepresentation :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F)
      (StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i)) where
  toFun g := (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap
  map_one' := by
    rw [ColorAction.quotientEquiv_one]
    rfl
  map_mul' g h := by
    rw [ColorAction.quotientEquiv_mul]
    rfl
theorem equation_23_character (hn : 0<n) (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
  Representation.character (V := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i)) (quotientColorRepresentation (F
  := F) (n := n)) g= Eulerian.permutationPolynomial n (1+g.val 0 0) (1+g.val 1 1) := by sorry
local instance colorPolynomialActionOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
theorem color_preserves_polynomialPiece (hn : 0<n) (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) F) (x : StrictQuotient (data (F := F)
  hn).beta (data (F := F) hn).phi) (hx : x∈polynomialPiece (F := F) hn k) : ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X
  i) x∈ polynomialPiece (F := F) hn k := by sorry
def polynomialPieceColorRepresentation (hn : 0<n) (k : ℕ) :
    Representation F (Matrix.GeneralLinearGroup (Fin 2) F) (polynomialPiece (F := F) hn k) where
  toFun g := (ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)).toLinearMap.restrict
    (color_preserves_polynomialPiece (F := F) hn k g)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ColorAction.quotientEquiv 1 (fun i : Fin n ↦ MvPolynomial.X i)
      (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))=
        (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))
    rw [ColorAction.quotientEquiv_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ColorAction.quotientEquiv (g*h) (fun i : Fin n ↦ MvPolynomial.X i)
      (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i))=
      ColorAction.quotientEquiv g (fun i : Fin n ↦ MvPolynomial.X i)
        (ColorAction.quotientEquiv h (fun i : Fin n ↦ MvPolynomial.X i)
          (x : StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ MvPolynomial.X i)))
    rw [ColorAction.quotientEquiv_mul,AlgEquiv.mul_apply]
theorem equation_22_character (hn : 0<n) (k : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) F) (h01 : g.val 0 1=0) (h10 : g.val 1 0=0) :
    Representation.character (V := polynomialPiece (F := F) hn k)
      (polynomialPieceColorRepresentation (F := F) hn k) g=
      (∑ m : MultiplicityVector n,if Admissible m then
        ColorPaths.multiplicityBoxPolynomial (Polynomial.X : Polynomial F) m*
          (Polynomial.C (g.val 0 0)+Polynomial.C (g.val 1 1))^ColorPaths.singleCount m*
          (Polynomial.C (g.val 0 0)*Polynomial.C (g.val 1 1))^ColorPaths.doubleCount m else 0).coeff k := by sorry
end PaperVerification.Fermion.TypeA
