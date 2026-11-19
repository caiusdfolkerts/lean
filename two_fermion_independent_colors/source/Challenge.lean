module
public import Mathlib

/-! Theorem 8.1: initial ideals and an equivariant degeneration of the two-fermion quotient. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PaperVerification.Fermion.BasisFiltered
open scoped BigOperators
variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ)
def component (d : ℕ) : M →ₗ[R] M where
  toFun x := b.repr.symm ((b.repr x).filter (fun i ↦ w i = d))
  map_add' x y := by rw [map_add,Finsupp.filter_add,map_add]
  map_smul' a x := by rw [map_smul,Finsupp.filter_smul,map_smul,RingHom.id_apply]
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion.BlockInitial
open scoped BigOperators
open BasisFiltered
variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  (b : Module.Basis J P M) (weight : J → ℕ)
def LowerBound (r : ℕ) (x : M) : Prop := ∀ j,b.repr x j≠0 → r≤weight j
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
def principalColon (J : Ideal A) (g : A) : Ideal A := J.colon ({g} : Set A)
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
namespace PaperVerification.Fermion.Paths
open Endpoint
open scoped BigOperators
def markDegree : Mark → ℕ
  | .unmarked => 0
  | .theta => 1
  | .xi => 1
  | .double => 2
end PaperVerification.Fermion.Paths
namespace PaperVerification.Fermion.Endpoint
open scoped BigOperators
open Polynomial
variable {R I : Type*} [CommRing R] [DecidableEq I]
def wordMark (T : Finset (I ⊕ I)) (i : I) : Mark :=
  if Sum.inl i ∈ T then
    if Sum.inr i ∈ T then .double else .theta
  else if Sum.inr i ∈ T then .xi else .unmarked
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
section
open scoped TensorProduct BigOperators
variable {K : Type*} [CommRing K] {n : ℕ}
variable [LinearOrder (OddIndex n)]
def superPolynomialBasis : Module.Basis (Finset (OddIndex n)) (PolynomialRing K n) (SuperRing K n) := ((Pi.basisFun K (OddIndex
  n)).ExteriorAlgebra).baseChange (PolynomialRing K n)
end
open MvPolynomial Exterior Endpoint Newton
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionCreatorPolynomialBoxes_localInst_1 (m : ℕ) : DecidableEq (Fin m ⊕ Fin m) :=
  (interleavedOddOrder m).toDecidableEq
def wordMultiplicity (T : Finset (OddIndex n)) (i : Fin n) : ℕ :=
  (if Sum.inl i ∈ T then 1 else 0) + (if Sum.inr i ∈ T then 1 else 0)
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
set_option backward.isDefEq.respectTransparency false
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
@[simp] theorem wordMark_wordOfMarks (m : Fin n → Mark) (i : Fin n) :
    wordMark (wordOfMarks m) i=m i := by sorry
def marksWordEquiv (n : ℕ) : (Fin n → Mark) ≃ Finset (OddIndex n) where
  toFun := wordOfMarks
  invFun := wordMark
  left_inv m := funext (wordMark_wordOfMarks m)
  right_inv W := by
    ext a
    cases a with
    | inl i =>
        by_cases hθ : Sum.inl i ∈ W <;> by_cases hξ : Sum.inr i ∈ W <;>
          simp [wordMark,hθ,hξ]
    | inr i =>
        by_cases hθ : Sum.inl i ∈ W <;> by_cases hξ : Sum.inr i ∈ W <;>
          simp [wordMark,hθ,hξ]
@[simp] theorem wordMultiplicity_wordOfMarks (m : Fin n → Mark) (i : Fin n) :
    wordMultiplicity (wordOfMarks m) i=markDegree (m i) := by sorry
end PaperVerification.Fermion.Paths
namespace PaperVerification.Fermion
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
section
set_option backward.isDefEq.respectTransparency false
section
open MvPolynomial Exterior
open scoped BigOperators
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionMultiplicityBlocks_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
abbrev MultiplicityVector (n : ℕ) := Fin n → Fin 3
def wordMultiplicityVector (T : Finset (OddIndex n)) : MultiplicityVector n :=
  fun i ↦ ⟨wordMultiplicity T i,by
    classical
    by_cases hθ : Sum.inl i∈T <;> by_cases hξ : Sum.inr i∈T <;>
      simp only [wordMultiplicity,hθ,hξ,if_true,if_false] <;> omega⟩
abbrev MultiplicityColoring (m : MultiplicityVector n) :=
  {T : Finset (OddIndex n) // wordMultiplicityVector T=m}
end
open MvPolynomial Exterior BasisFiltered
open scoped BigOperators TensorProduct
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionStrictWeightReesFibers_localInst_1 : LinearOrder (OddIndex n) := LinearOrder.lift' modeRank modeRank_injective
abbrev StrictMultiplicityInitialQuotient (d : StrictData (K := F) (n := n)) := (strictMultiplicityInitialIdeal d).ringCon.Quotient
def strictInitialProjection (d : StrictData (K := F) (n := n)) : SuperRing F n →ₐ[F] StrictMultiplicityInitialQuotient d :=
  (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
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
open scoped BigOperators TensorProduct
variable {R : Type*} [CommRing R] {n : ℕ}
abbrev ColorMatrix (R : Type*) := Matrix (Fin 2) (Fin 2) R
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
end PaperVerification.Fermion.TypeA
namespace PaperVerification.Fermion.ColorAction
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct
open Exterior
variable {R : Type*} [CommRing R] {n : ℕ}
local instance FermionIndependentColorAction_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def indexLinear (A : Fin n → ColorMatrix R) : OddModule R n →ₗ[R] OddModule R n where
  toFun v := Sum.elim
    (fun i ↦ A i 0 0*v (.inl i)+A i 0 1*v (.inr i))
    (fun i ↦ A i 1 0*v (.inl i)+A i 1 1*v (.inr i))
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.add_apply] <;> ring
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,
      smul_eq_mul,RingHom.id_apply] <;> ring
def indexAmbient (A : Fin n → ColorMatrix R) : SuperRing R n →ₐ[PolynomialRing R n] SuperRing R n := Algebra.TensorProduct.map
  (AlgHom.id (PolynomialRing R n) (PolynomialRing R n)) (ExteriorAlgebra.map (indexLinear A))
@[simp] theorem indexAmbient_one :
    indexAmbient (fun _ : Fin n ↦ (1 : ColorMatrix R))=AlgHom.id (PolynomialRing R n) _ := by sorry
theorem indexAmbient_mul (A B : Fin n → ColorMatrix R) : indexAmbient (fun i ↦ A i*B i)=(indexAmbient A).comp (indexAmbient B) := by
  sorry
def indexAmbientEquiv (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) R) :
    SuperRing R n ≃ₐ[PolynomialRing R n] SuperRing R n :=
  AlgEquiv.ofAlgHom (indexAmbient (fun i ↦ (g i).val))
    (indexAmbient (fun i ↦ (g i).inv))
    (by
      rw [←indexAmbient_mul]
      simp only [Units.val_inv,indexAmbient_one])
    (by
      rw [←indexAmbient_mul]
      simp only [Units.inv_val,indexAmbient_one])
attribute [local instance] FermionIndependentColorAction_localInst_1
variable {F : Type*} [Field F]
theorem indexAmbient_preserves_initialIdeal (A : Fin n → ColorMatrix F) (d : StrictData (K := F) (n := n)) {z : SuperRing F n} (hz :
  z∈strictMultiplicityInitialIdeal d) : indexAmbient A z∈strictMultiplicityInitialIdeal d := by sorry
def initialQuotientEquiv (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F) (d : StrictData (K := F) (n := n)) :
  (strictMultiplicityInitialIdeal d).ringCon.Quotient ≃ₐ[F] (strictMultiplicityInitialIdeal d).ringCon.Quotient :=
  twoSidedQuotientEquiv ((indexAmbientEquiv g).restrictScalars F) (strictMultiplicityInitialIdeal d) (strictMultiplicityInitialIdeal d)
  (fun _ hz ↦ indexAmbient_preserves_initialIdeal (fun i ↦ (g i).val) d hz) (fun _ hz ↦ indexAmbient_preserves_initialIdeal (fun i ↦ (g
  i).inv) d hz)
@[simp] theorem initialQuotientEquiv_mk
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (d : StrictData (K := F) (n := n)) (z : SuperRing F n) :
    initialQuotientEquiv g d ((strictMultiplicityInitialIdeal d).ringCon.mkₐ F z)=
      (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
        (indexAmbient (fun i ↦ (g i).val) z) := by sorry
def initialQuotientAction (d : StrictData (K := F) (n := n)) :
    (Fin n → Matrix.GeneralLinearGroup (Fin 2) F) →*
      ((strictMultiplicityInitialIdeal d).ringCon.Quotient ≃ₐ[F]
        (strictMultiplicityInitialIdeal d).ringCon.Quotient) where
  toFun g := initialQuotientEquiv g d
  map_one' := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := (strictMultiplicityInitialIdeal d).ringCon.mkₐ_surjective (α := F) z
    change (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
      (indexAmbient (fun _ ↦ (1 : ColorMatrix F)) x)=_
    rw [indexAmbient_one]
    rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := (strictMultiplicityInitialIdeal d).ringCon.mkₐ_surjective (α := F) z
    simp only [AlgEquiv.mul_apply,initialQuotientEquiv_mk]
    change (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
      (indexAmbient (fun i ↦ (g i).val*(h i).val) x)=_
    rw [indexAmbient_mul]
    rfl
end PaperVerification.Fermion.ColorAction
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
def colorLinear (A : Matrix (Fin 2) (Fin 2) R) : (Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v c := A c 0*v 0+A c 1*v 1
  map_add' v w := by funext c; simp only [Pi.add_apply]; ring
  map_smul' r v := by
    funext c
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring
@[simp] theorem colorLinear_one :
    colorLinear (1 : Matrix (Fin 2) (Fin 2) R)=LinearMap.id := by sorry
theorem colorLinear_mul (A B : Matrix (Fin 2) (Fin 2) R) : colorLinear (A*B)=(colorLinear A).comp (colorLinear B) := by sorry
def assemble (d : Fin n → ℕ) : (⨂[R] i : Fin n, (⋀[R]^(d i) (Fin 2 → R))) →ₗ[R] ExteriorAlgebra R (OddModule R n) :=
  NaturalExteriorTensor.assemble (R := R) (V := Fin 2 → R) (W := OddModule R n) d (embedding (R := R))
end PaperVerification.Fermion.NaturalColor
namespace PaperVerification.Fermion.ColorPaths
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open Exterior Endpoint Paths Newton
variable {R : Type*} [CommSemiring R] {n : ℕ}
local instance colorMultiplicityEnumerationDecidableEq (n : ℕ) : DecidableEq (OddIndex n) :=
  (interleavedOddOrder n).toDecidableEq
abbrev LocalColorFiber (m : Fin 3) := {a : Mark // markDegree a=m.val}
theorem markDegree_wordMark (T : Finset (OddIndex n)) (i : Fin n) : markDegree (wordMark T i)=wordMultiplicity T i := by sorry
def coloringLocalEquiv (m : MultiplicityVector n) :
    MultiplicityColoring m ≃ (∀ i,LocalColorFiber (m i)) where
  toFun T i := ⟨wordMark T.val i,by
    rw [markDegree_wordMark]
    exact congrArg (fun f : MultiplicityVector n ↦ (f i).val) T.property⟩
  invFun a := ⟨wordOfMarks (fun i ↦ (a i).val),by
    funext i
    apply Fin.ext
    change wordMultiplicity (wordOfMarks (fun i ↦ (a i).val)) i=(m i).val
    rw [wordMultiplicity_wordOfMarks]
    exact (a i).property⟩
  left_inv T := by
    apply Subtype.ext
    exact (marksWordEquiv n).right_inv T.val
  right_inv a := by
    funext i
    apply Subtype.ext
    exact wordMark_wordOfMarks (fun i ↦ (a i).val) i
end PaperVerification.Fermion.ColorPaths
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators DirectSum
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance FermionMultiplicityQuotientDecomposition_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective
abbrev CoefficientQuotient (m : MultiplicityVector n) := PolynomialRing F n ⧸ coefficientIdeal (F := F) m
def coefficientProjection : SuperRing F n →ₗ[F] ((T : Finset (OddIndex n)) → CoefficientQuotient (F := F) (wordMultiplicityVector T))
  := LinearMap.pi fun T ↦ ((Ideal.Quotient.mkₐ F (coefficientIdeal (wordMultiplicityVector T))).toLinearMap).comp
  (((superPolynomialBasis (K := F)).coord T).restrictScalars F)
theorem coefficientProjection_surjective : Function.Surjective (coefficientProjection (F := F) (n := n)) := by sorry
theorem coefficientProjection_kernel (hn : 0<n) : (coefficientProjection (F := F) (n := n)).ker = (strictInitialProjection (data (F :=
  F) hn)).toLinearMap.ker := by sorry
def initialCoefficientEquiv (hn : 0<n) : StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F] ((T : Finset (OddIndex n)) →
  CoefficientQuotient (F := F) (wordMultiplicityVector T)) := ((strictInitialProjection (data (F := F)
  hn)).toLinearMap.quotKerEquivOfSurjective ((strictMultiplicityInitialIdeal (data (F := F) hn)).ringCon.mkₐ_surjective (α := F))).symm
  |>.trans ((Submodule.quotEquivOfEq _ _ (coefficientProjection_kernel (F := F) hn).symm).trans ((coefficientProjection (F := F) (n :=
  n)).quotKerEquivOfSurjective coefficientProjection_surjective))
def regroupCoefficientEquiv :
    ((T : Finset (OddIndex n)) → CoefficientQuotient (F := F) (wordMultiplicityVector T))
      ≃ₗ[F] ((m : MultiplicityVector n) → MultiplicityColoring m → CoefficientQuotient (F := F) m) where
  toFun y m T :=
    Ideal.quotientEquivAlgOfEq F (congrArg (coefficientIdeal (F := F)) T.property) (y T.val)
  invFun y T := y (wordMultiplicityVector T) ⟨T,rfl⟩
  left_inv y := by
    funext T
    change Ideal.quotientEquivAlgOfEq F rfl (y T)=y T
    obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (y T)
    rw [←hp,Ideal.quotientEquivAlgOfEq_mk]
  right_inv y := by
    funext m T
    rcases T with ⟨T,hT⟩
    subst m
    change Ideal.quotientEquivAlgOfEq F rfl
      (y (wordMultiplicityVector T) ⟨T,rfl⟩)=y (wordMultiplicityVector T) ⟨T,rfl⟩
    obtain ⟨p,hp⟩ := Ideal.Quotient.mk_surjective (y (wordMultiplicityVector T) ⟨T,rfl⟩)
    rw [←hp,Ideal.quotientEquivAlgOfEq_mk]
  map_add' x y := by
    funext m T
    exact map_add (Ideal.quotientEquivAlgOfEq F
      (congrArg (coefficientIdeal (F := F)) T.property)) (x T.val) (y T.val)
  map_smul' a y := by
    funext m T
    exact map_smul (Ideal.quotientEquivAlgOfEq F
      (congrArg (coefficientIdeal (F := F)) T.property)) a (y T.val)
end PaperVerification.Fermion.TypeA
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
@[simp] theorem markSubset_card (a : Mark) : (markSubset a).card=markDegree a := by sorry
def localColorExteriorIndexEquiv (m : Fin 3) :
    LocalColorFiber m ≃ Set.powersetCard (Fin 2) m.val :=
  markSubsetEquiv.subtypeEquiv (fun a ↦ by
    change markDegree a=m.val ↔ (markSubset a).card=m.val
    rw [markSubset_card])
variable {n : ℕ}
def coloringExteriorIndexEquiv (m : MultiplicityVector n) : MultiplicityColoring m ≃ (∀ i,Set.powersetCard (Fin 2) (m i).val) :=
  (coloringLocalEquiv m).trans (Equiv.piCongrRight fun i ↦ localColorExteriorIndexEquiv (m i))
variable (R : Type*) [CommRing R]
abbrev ExteriorColorTensor (m : MultiplicityVector n) := ⨂[R] i : Fin n, (⋀[R]^((m i).val) (Fin 2 → R))
def exteriorColorTensorBasis (m : MultiplicityVector n) : Module.Basis (MultiplicityColoring m) R (ExteriorColorTensor R m) :=
  (_root_.Basis.piTensorProduct (fun i ↦ (Pi.basisFun R (Fin 2)).exteriorPower (m i).val)).reindex (coloringExteriorIndexEquiv m).symm
end PaperVerification.Fermion.ColorPaths
namespace PaperVerification.Fermion.NaturalColor
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct BigOperators
open ColorPaths
variable {F : Type*} [Field F] {n : ℕ}
local instance fieldPaperOddOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective
theorem assemble_basis_unit (m : MultiplicityVector n) (T : MultiplicityColoring m) : ∃ ε : F,ε≠0 ∧ assemble (fun i ↦ (m i).val)
  (exteriorColorTensorBasis F m T)= ε • (Pi.basisFun F (OddIndex n)).ExteriorAlgebra T.val := by sorry
end PaperVerification.Fermion.NaturalColor
namespace PaperVerification.Fermion.TypeA
open scoped DirectSum
open scoped Classical BigOperators TensorProduct
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
abbrev ExteriorCoefficientBlock (m : MultiplicityVector n) := CoefficientQuotient (F := F) m ⊗[F] ColorPaths.ExteriorColorTensor F m
theorem exteriorCoefficientBlock_eq_zero_of_inadmissible (hn : 0<n) (m : MultiplicityVector n) (hm : ¬Admissible m) (x :
  ExteriorCoefficientBlock (F := F) m) : x=0 := by sorry
def restrictAdmissibleColorBlocksEquiv (hn : 0<n) :
    ((m : MultiplicityVector n) → ExteriorCoefficientBlock (F := F) m) ≃ₗ[F]
      ((m : {m : MultiplicityVector n // Admissible m}) →
        ExteriorCoefficientBlock (F := F) m.val) where
  toFun x m := x m.val
  invFun y m := if h : Admissible m then y ⟨m,h⟩ else 0
  left_inv x := by
    funext m
    by_cases h : Admissible m
    · simp only [h,dite_true]
    · simp only [h,dite_false]
      exact (exteriorCoefficientBlock_eq_zero_of_inadmissible hn m h (x m)).symm
  right_inv y := by
    funext m
    simp only [m.property,dite_true]
  map_add' x y := rfl
  map_smul' c x := rfl
end PaperVerification.Fermion.TypeA
namespace PaperVerification.Fermion.NaturalColor
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct DirectSum
open Exterior
variable {F : Type*} [Field F] {n : ℕ}
local instance FermionNaturalColorBlocks_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
def assemblyScalar (m : MultiplicityVector n) (T : MultiplicityColoring m) : F := Classical.choose (assemble_basis_unit (F := F) m T)
theorem assemblyScalar_ne_zero (m : MultiplicityVector n) (T : MultiplicityColoring m) : assemblyScalar (F := F) m T≠0 := by sorry
def normalizedTensorBasis (m : MultiplicityVector n) : Module.Basis (MultiplicityColoring m) F (ColorPaths.ExteriorColorTensor F m) :=
  (ColorPaths.exteriorColorTensorBasis F m).unitsSMul (fun T ↦ (Units.mk0 (assemblyScalar m T) (assemblyScalar_ne_zero m T))⁻¹)
attribute [local instance] FermionNaturalColorBlocks_localInst_1
variable (C : Type*) [AddCommGroup C] [Module F C]
def coefficientEquiv (m : MultiplicityVector n) : (MultiplicityColoring m → C) ≃ₗ[F] C ⊗[F] ColorPaths.ExteriorColorTensor F m :=
  (Finsupp.linearEquivFunOnFinite F C (MultiplicityColoring m)).symm |>.trans ((TensorProduct.finsuppScalarRight F F C
  (MultiplicityColoring m)).symm.trans (TensorProduct.congr (LinearEquiv.refl F C) (normalizedTensorBasis m).repr.symm))
def exteriorRepresentation (m : MultiplicityVector n) :
    Representation F (Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
      (ColorPaths.ExteriorColorTensor F m) where
  toFun g := PiTensorProduct.map
    (fun i ↦ exteriorPower.map (m i).val (colorLinear (g i).val))
  map_one' := by
    simp only [Pi.one_apply,Units.val_one,colorLinear_one,exteriorPower.map_id,
      PiTensorProduct.map_id,Module.End.one_eq_id]
  map_mul' g h := by
    change PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val
      (colorLinear ((g i).val*(h i).val)))=
      (PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val (colorLinear (g i).val))).comp
        (PiTensorProduct.map (fun i ↦ exteriorPower.map (m i).val (colorLinear (h i).val)))
    rw [←PiTensorProduct.map_comp]
    congr 1
    funext i
    rw [colorLinear_mul,exteriorPower.map_comp]
end PaperVerification.Fermion.NaturalColor
namespace PaperVerification.Fermion.TypeA
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct DirectSum
section
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance FermionNaturalColorBlocks_localInst_2 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective
def naturalInitialFunctionEquiv (hn : 0<n) : StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F] ((m : MultiplicityVector n) →
  ExteriorCoefficientBlock (F := F) m) := ((initialCoefficientEquiv hn).trans regroupCoefficientEquiv).trans (LinearEquiv.piCongrRight
  fun m ↦ NaturalColor.coefficientEquiv (CoefficientQuotient (F := F) m) m)
def naturalInitialAdmissibleEquiv (hn : 0<n) : StrictMultiplicityInitialQuotient (data (F := F) hn) ≃ₗ[F] ⨁ m : {m : MultiplicityVector
  n // Admissible m}, ExteriorCoefficientBlock (F := F) m.val := (naturalInitialFunctionEquiv hn).trans
  ((restrictAdmissibleColorBlocksEquiv hn).trans (DirectSum.linearEquivFunOnFintype F {m : MultiplicityVector n // Admissible m} (fun m
  ↦ ExteriorCoefficientBlock (F := F) m.val)).symm)
def naturalAdmissibleRepresentation : Representation F (Fin n → Matrix.GeneralLinearGroup (Fin 2) F) (⨁ m : {m : MultiplicityVector n
  // Admissible m}, ExteriorCoefficientBlock (F := F) m.val) := Representation.directSum fun m ↦ (Representation.trivial F (Fin n →
  Matrix.GeneralLinearGroup (Fin 2) F) (CoefficientQuotient (F := F) m.val)).tprod (NaturalColor.exteriorRepresentation m.val)
end
open MvPolynomial Exterior
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
local instance theoremEightOneOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective
set_option maxHeartbeats 1000000
theorem palomarColorIndependent (hn : 0<n) : (∀ (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F) (z : SuperRing F n),
  ColorAction.initialQuotientAction (data (F := F) hn) g (strictInitialProjection (data (F := F) hn) z)= strictInitialProjection (data
  (F := F) hn) (ColorAction.indexAmbient (fun i ↦ (g i).val) z)) ∧ (∀ (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F) (x :
  StrictMultiplicityInitialQuotient (data (F := F) hn)), naturalInitialAdmissibleEquiv hn (ColorAction.initialQuotientAction (data (F
  := F) hn) g x)= naturalAdmissibleRepresentation g (naturalInitialAdmissibleEquiv hn x)) := by sorry
end PaperVerification.Fermion.TypeA
