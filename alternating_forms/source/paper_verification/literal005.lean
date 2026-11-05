module

public import paper_verification.literal004
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import paper_verification.literal000
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import paper_verification.literal001
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Lean.Elab.Tactic.Omega
public import paper_verification.literal003
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Order.Zorn
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Sym
import paper_verification.literal000

set_option Elab.async false

section TAF_LiteralSource_0288
/- Original module: PaperVerification.AlternatingFormsPolynomialKoszul -/


/-!
# The polynomial boundary case: actual Koszul exactness

The one-plane Plucker ring is a polynomial ring.  Its variables form a
regular sequence because every earlier coordinate ideal is prime and does
not contain the next variable.  This gives exactness of the actual
exterior-power Koszul complex in every positive degree.  No regularity or
exactness assertion is assumed.  The ordinary Tor grading comparison is a
separate subsequent obligation.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.PolynomialKoszul

open MvPolynomial RingTheory.Sequence CategoryTheory

universe u v
variable {K : Type u} [Field K] {ι : Type v}

theorem variable_not_mem_coordinateIdeal (S : Set ι) (i : ι) (hi : i∉S) :
    (X i : MvPolynomial ι K)∉Ideal.span (X '' S) := by
  rw [span_X_image_eq_ker_aeval_ite_mem,RingHom.mem_ker,aeval_X]
  simpa only [Set.mem_compl_iff,hi,not_false_eq_true,if_true] using
    (X_ne_zero (R := K) i)

theorem variable_regular_mod_coordinateIdeal (S : Set ι) (i : ι) (hi : i∉S) :
    IsSMulRegular (MvPolynomial ι K⧸Ideal.span ((X : ι → MvPolynomial ι K) '' S))
      (X (R := K) i) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro p hp
  change X i*p∈Ideal.span (X '' S) at hp
  exact ((span_X_image_isPrime (R := K) S).mem_or_mem hp).resolve_left
    (variable_not_mem_coordinateIdeal S i hi)

/-- Every finite injective list of distinct polynomial variables is
weakly regular, with no upper bound on its length. -/
theorem variables_weaklyRegular {n : ℕ} (f : Fin n → ι) (hf : Function.Injective f) :
    IsWeaklyRegular (MvPolynomial ι K)
      (List.ofFn (fun i ↦ (X (f i) : MvPolynomial ι K))) := by
  refine ⟨?_⟩
  intro j hj
  have hjn : j<n := by simpa only [List.length_ofFn] using hj
  let hle : j≤n := Nat.le_of_lt hjn
  let g : Fin j → ι := fun a ↦ f (a.castLE hle)
  have hs : Ideal.ofList ((List.ofFn (fun i : Fin n ↦ (X (f i) : MvPolynomial ι K))).take j)=
      Ideal.span (X '' Set.range g) := by
    rw [←Fin.ofFn_take_eq_take_ofFn hle]
    unfold Ideal.ofList
    congr 1
    ext p
    constructor
    · intro hp
      obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hp
      exact ⟨g a,⟨a,rfl⟩,rfl⟩
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact List.mem_ofFn.mpr ⟨a,rfl⟩
  have hnot : f ⟨j,hjn⟩∉Set.range g := by
    rintro ⟨a,ha⟩
    have he := congrArg Fin.val (hf ha)
    change a.val=j at he
    exact (Nat.ne_of_lt a.isLt) he
  have hr := variable_regular_mod_coordinateIdeal (K := K) (Set.range g) (f ⟨j,hjn⟩) hnot
  have htop :
      (Ideal.ofList ((List.ofFn (fun i : Fin n =>
        (X (f i) : MvPolynomial ι K))).take j) •
          (⊤ : Submodule (MvPolynomial ι K) (MvPolynomial ι K)))=
        Ideal.span ((X : ι → MvPolynomial ι K) '' Set.range g) := by
    rw [Ideal.smul_eq_mul,Ideal.mul_top,hs]
  simp only [List.getElem_ofFn]
  change IsSMulRegular
    (MvPolynomial ι K ⧸ (Ideal.ofList
      ((List.ofFn (fun i : Fin n => (X (f i) : MvPolynomial ι K))).take j) •
        (⊤ : Submodule (MvPolynomial ι K) (MvPolynomial ι K))))
    (X (R := K) (f ⟨j,hjn⟩))
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem
    (R := MvPolynomial ι K) (M := MvPolynomial ι K) _
    (X (R := K) (f ⟨j,hjn⟩))).mpr
  intro p hp
  have hp' : X (R := K) (f ⟨j,hjn⟩) • p∈
      Ideal.span ((X : ι → MvPolynomial ι K) '' Set.range g) :=
    (congrArg (fun U : Submodule (MvPolynomial ι K) (MvPolynomial ι K) =>
      X (R := K) (f ⟨j,hjn⟩) • p∈U) htop).mp hp
  have hreg : p∈Ideal.span ((X : ι → MvPolynomial ι K) '' Set.range g) :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem
      (Ideal.span ((X : ι → MvPolynomial ι K) '' Set.range g))
      (X (R := K) (f ⟨j,hjn⟩))).mp hr p hp'
  exact (congrArg (fun U : Submodule (MvPolynomial ι K) (MvPolynomial ι K) =>
    p∈U) htop).mpr hreg

variable (K) (n : ℕ)

abbrev PolynomialRing := MvPolynomial (Fin n) K

def variableFunctional : Module.Dual (PolynomialRing K n) (Fin n → PolynomialRing K n) :=
  Fintype.linearCombination (PolynomialRing K n) (fun i ↦ X i)

def complex : ChainComplex (ModuleCat (PolynomialRing K n)) ℕ :=
  TauCeti.koszulComplex (variableFunctional K n)

/-- Positive-degree exactness of the literal polynomial Koszul complex. -/
theorem complex_exactAt_succ (r : ℕ) : (complex K n).ExactAt (r+1) :=
  TauCeti.koszulComplex.exactAt_of_isWeaklyRegular (fun i : Fin n ↦ X (R := K) i)
    (variables_weaklyRegular id Function.injective_id) r

/-- Its actual zeroth homology is the polynomial quotient by the variables. -/
def homologyZeroEquiv : (complex K n).homology 0 ≃ₗ[PolynomialRing K n]
    (PolynomialRing K n⧸Ideal.span (Set.range (X : Fin n → PolynomialRing K n))) :=
  TauCeti.koszulComplex.homologyZeroEquivSpan (fun i : Fin n ↦ X (R := K) i)

abbrev Residue := PolynomialRing K n⧸Ideal.span (Set.range (X : Fin n → PolynomialRing K n))

def augmentation : (complex K n).X 0 ⟶ ModuleCat.of (PolynomialRing K n) (Residue K n) :=
  ModuleCat.ofHom ((Ideal.span (Set.range (X : Fin n → PolynomialRing K n))).mkQ.comp
    (exteriorPower.zeroEquiv (PolynomialRing K n) (Fin n → PolynomialRing K n)).toLinearMap)

theorem range_d_zero_map :
    ((complex K n).d 1 0).hom.range.map
        (exteriorPower.zeroEquiv (PolynomialRing K n) (Fin n → PolynomialRing K n)).toLinearMap=
      Ideal.span (Set.range (X : Fin n → PolynomialRing K n)) := by
  change (TauCeti.koszulDifferential (variableFunctional K n) 0).range.map _=_
  rw [TauCeti.map_zeroEquiv_range_koszulDifferential_zero]
  exact Fintype.range_linearCombination _ _

theorem range_d_zero_eq_ker_augmentation :
    ((complex K n).d 1 0).hom.range=(augmentation K n).hom.ker := by
  let e := exteriorPower.zeroEquiv (PolynomialRing K n) (Fin n → PolynomialRing K n)
  ext z
  constructor
  · intro hz
    have he : e z∈Ideal.span (Set.range (X : Fin n → PolynomialRing K n)) := by
      rw [←range_d_zero_map K n]
      exact Submodule.mem_map_of_mem hz
    exact LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero
      (Ideal.span (Set.range (X : Fin n → PolynomialRing K n)))).mpr he)
  · intro hz
    have he : e z∈Ideal.span (Set.range (X : Fin n → PolynomialRing K n)) :=
      (Submodule.Quotient.mk_eq_zero
        (Ideal.span (Set.range (X : Fin n → PolynomialRing K n)))).mp
        (LinearMap.mem_ker.mp hz)
    rw [←range_d_zero_map K n] at he
    obtain ⟨y,hy,hye⟩ := he
    exact e.injective hye ▸ hy

theorem d_augmentation : (complex K n).d 1 0 ≫ augmentation K n=0 := by
  apply ModuleCat.hom_ext
  exact LinearMap.range_le_ker_iff.mp (le_of_eq (range_d_zero_eq_ker_augmentation K n))

theorem augmentation_exact : (ShortComplex.mk _ _ (d_augmentation K n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact range_d_zero_eq_ker_augmentation K n

instance augmentation_epi : Epi (augmentation K n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact (Submodule.mkQ_surjective _).comp
    (exteriorPower.zeroEquiv (PolynomialRing K n) (Fin n → PolynomialRing K n)).surjective

/-- The full actual free resolution of the polynomial augmentation
residue, in every number of variables. -/
def resolution : ProjectiveResolution (ModuleCat.of (PolynomialRing K n) (Residue K n)) where
  complex := complex K n
  projective r := by
    change Projective (ModuleCat.of (PolynomialRing K n)
      (⋀[PolynomialRing K n]^r (Fin n → PolynomialRing K n)))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation K n,d_augmentation K n⟩
  quasiIso := ⟨fun r ↦ by
    cases r with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (d_augmentation K n)).Exact ∧ Epi (augmentation K n)
        exact ⟨augmentation_exact K n,inferInstance⟩
      all_goals rfl
    | succ r =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ K n r
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- Ordinary derived tensor is computed by this explicit polynomial
Koszul resolution.  This is an isomorphism of actual module objects. -/
def torIso (E : ModuleCat (PolynomialRing K n)) (r : ℕ) :
    (((Tor (ModuleCat (PolynomialRing K n)) r).obj E).obj
      (ModuleCat.of (PolynomialRing K n) (Residue K n))) ≅
      ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PolynomialRing K n))).obj E).mapHomologicalComplex (ComplexShape.down ℕ)).obj (resolution K n).complex).homology r :=
  (resolution K n).isoLeftDerivedObj _ r

end PaperVerification.AlternatingForms.PolynomialKoszul
end
end
end TAF_LiteralSource_0288

section TAF_LiteralSource_0289
/- Original module: PaperVerification.AlternatingFormsOnePlaneKoszul -/


/-!
# The variable resolution on the actual one-plane Plucker quotient

This file uses the literal quotient by the generic-minor kernel.  Its
variables are the classes of the one-entry Plucker coordinates.  Their
weak regularity is transported through the explicit polynomial-ring
isomorphism, and the actual exterior-power Koszul complex resolves its
actual augmentation quotient.  Thus the coefficient ring of this
resolution is the original one-plane Plucker ring, not a replacement
polynomial presentation with an unproved identification.

This reconstructed source still requires a fresh compiler pass.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial RingTheory.Sequence CategoryTheory

universe u
variable (K : Type u) [Field K] (n : ℕ)

abbrev Ring := MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal

def indexEquiv : PluckerIndex 1 n ≃ Fin n where
  toFun I := I.val 0
  invFun := onePlaneIndex
  left_inv := onePlaneIndex_eta
  right_inv _ := rfl

def polynomialEquiv : Ring K n ≃ₐ[K] MvPolynomial (Fin n) K :=
  (Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    ((AlgEquiv.quotientBot K _).trans (MvPolynomial.renameEquiv K (indexEquiv n)))

def generator (i : Fin n) : Ring K n :=
  Ideal.Quotient.mk _ (X (onePlaneIndex i))

@[simp]
theorem polynomialEquiv_generator (i : Fin n) :
    polynomialEquiv K n (generator K n i)=X i := by
  simp [polynomialEquiv,generator,indexEquiv]
  rfl

@[simp]
theorem polynomialEquiv_symm_X (i : Fin n) :
    (polynomialEquiv K n).symm (X i)=generator K n i := by
  apply (polynomialEquiv K n).injective
  simp

set_option backward.isDefEq.respectTransparency false in
theorem variables_weaklyRegular :
    IsWeaklyRegular (Ring K n) (List.ofFn (generator K n)) := by
  let e := (polynomialEquiv K n).symm
  have hrel : List.Forall₂
      (fun (x : MvPolynomial (Fin n) K) (y : Ring K n) =>
        ∀ z, e (x • z) = y • e z)
      (List.ofFn (fun i : Fin n => X (R := K) i))
      ((List.ofFn (fun i : Fin n => X (R := K) i)).map e) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro x hx y
    change e (x*y)=e x*e y
    exact e.map_mul x y
  have h := (e.toRingEquiv.toAddEquiv.isWeaklyRegular_congr
      (R := MvPolynomial (Fin n) K) (S := Ring K n) hrel).mp
      (PolynomialKoszul.variables_weaklyRegular (K := K) id Function.injective_id)
  dsimp only [e] at h
  simpa only [List.map_ofFn,Function.comp_def,polynomialEquiv_symm_X] using h

def functional : Module.Dual (Ring K n) (Fin n → Ring K n) :=
  Fintype.linearCombination (Ring K n) (generator K n)

def complex : ChainComplex (ModuleCat (Ring K n)) ℕ :=
  TauCeti.koszulComplex (functional K n)

theorem complex_exactAt_succ (r : ℕ) : (complex K n).ExactAt (r+1) :=
  TauCeti.koszulComplex.exactAt_of_isWeaklyRegular (generator K n)
    (variables_weaklyRegular K n) r

def augmentationIdeal : Ideal (Ring K n) := Ideal.span (Set.range (generator K n))

abbrev Residue := Ring K n ⧸ augmentationIdeal K n

def augmentation : (complex K n).X 0 ⟶ ModuleCat.of (Ring K n) (Residue K n) :=
  ModuleCat.ofHom ((augmentationIdeal K n).mkQ.comp
    (exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)).toLinearMap)

theorem range_d_zero_map :
    ((complex K n).d 1 0).hom.range.map
      (exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)).toLinearMap=
        augmentationIdeal K n := by
  change (TauCeti.koszulDifferential (functional K n) 0).range.map _=_
  rw [TauCeti.map_zeroEquiv_range_koszulDifferential_zero]
  exact Fintype.range_linearCombination _ _

theorem range_d_zero_eq_ker_augmentation :
    ((complex K n).d 1 0).hom.range=(augmentation K n).hom.ker := by
  let e := exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)
  ext z
  constructor
  · intro hz
    have he : e z∈augmentationIdeal K n := by
      rw [←range_d_zero_map K n]
      exact Submodule.mem_map_of_mem hz
    exact LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero (augmentationIdeal K n)).mpr he)
  · intro hz
    have he : e z∈augmentationIdeal K n :=
      (Submodule.Quotient.mk_eq_zero (augmentationIdeal K n)).mp (LinearMap.mem_ker.mp hz)
    rw [←range_d_zero_map K n] at he
    obtain ⟨y,hy,hye⟩ := he
    rwa [←e.injective hye]

theorem d_augmentation : (complex K n).d 1 0 ≫ augmentation K n=0 := by
  apply ModuleCat.hom_ext
  exact LinearMap.range_le_ker_iff.mp (le_of_eq (range_d_zero_eq_ker_augmentation K n))

theorem augmentation_exact : (ShortComplex.mk _ _ (d_augmentation K n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact range_d_zero_eq_ker_augmentation K n

instance augmentation_epi : Epi (augmentation K n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact (Submodule.mkQ_surjective _).comp
    (exteriorPower.zeroEquiv (Ring K n) (Fin n → Ring K n)).surjective

/-- The literal one-plane quotient has its actual free variable
resolution, in all homological degrees and for every number of variables. -/
def resolution : ProjectiveResolution (ModuleCat.of (Ring K n) (Residue K n)) where
  complex := complex K n
  projective r := by
    change Projective (ModuleCat.of (Ring K n) (⋀[Ring K n]^r (Fin n → Ring K n)))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation K n,d_augmentation K n⟩
  quasiIso := ⟨fun r ↦ by
    cases r with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (d_augmentation K n)).Exact ∧ Epi (augmentation K n)
        exact ⟨augmentation_exact K n,inferInstance⟩
      all_goals rfl
    | succ r =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ K n r
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

def torIso (E : ModuleCat (Ring K n)) (r : ℕ) :
    (((Tor (ModuleCat (Ring K n)) r).obj E).obj
      (ModuleCat.of (Ring K n) (Residue K n))) ≅
      ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (Ring K n))).obj E).mapHomologicalComplex (ComplexShape.down ℕ)).obj (resolution K n).complex).homology r :=
  (resolution K n).isoLeftDerivedObj _ r

end PaperVerification.AlternatingForms.OnePlaneKoszul
end
end
end TAF_LiteralSource_0289

section TAF_LiteralSource_0290
/- Original module: PaperVerification.AlternatingFormsOnePlaneTor -/


/-!
# Tor on the literal one-plane Plucker quotient

Tensoring the actual variable resolution over the original quotient
with its actual augmentation quotient makes every differential zero.
Each contraction coefficient lies in the ideal generated by the
original degree-one Plucker classes.  This identifies ordinary Tor
with the corresponding tensor of the actual exterior-power term.

Reconstructed source; fresh compilation and the internal-degree
comparison are required before this is a verification certificate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial CategoryTheory CategoryTheory.Limits

universe u
variable (K : Type u) [Field K] (n : ℕ)

local notation "P" => Ring K n
local notation "Q" => Residue K n
local notation "J" => augmentationIdeal K n

theorem residue_smul_eq_zero (p : P) (hp : p∈J) (a : Q) : p • a=0 := by
  change Ideal.Quotient.mk J p*a=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
  exact zero_mul a

theorem functional_mem_augmentationIdeal (v : Fin n → P) :
    functional K n v∈J := by
  change functional K n v ∈ Submodule.span P (Set.range (generator K n))
  rw [←Fintype.range_linearCombination P (generator K n)]
  exact LinearMap.mem_range_self _ v

def residueTensorComplex : ChainComplex (ModuleCat P) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat P)).obj
    (ModuleCat.of P Q)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resolution K n).complex)

theorem residue_tmul_differential_zero (r : ℕ) (a : Q)
    (z : ⋀[P]^(r+1) (Fin n → P)) :
    a ⊗ₜ[P] TauCeti.koszulDifferential (functional K n) r z=0 := by
  let T : (⋀[P]^r (Fin n → P)) →ₗ[P] Q ⊗[P] (⋀[P]^r (Fin n → P)) :=
    TensorProduct.mk P Q _ a
  have he : T.comp (TauCeti.koszulDifferential (functional K n) r)=0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change T (TauCeti.koszulDifferential (functional K n) r
      (exteriorPower.ιMulti P (r+1) v))=0
    rw [TauCeti.koszulDifferential_ιMulti,map_sum]
    simp only [map_smul]
    apply Finset.sum_eq_zero
    intro i hi
    change ((-1 : P)^i.val*functional K n (v i)) •
      (a ⊗ₜ[P] exteriorPower.ιMulti P r (i.removeNth v))=0
    rw [TensorProduct.smul_tmul',residue_smul_eq_zero K n _
      (Ideal.mul_mem_left _ _ (functional_mem_augmentationIdeal K n (v i))),
      TensorProduct.zero_tmul]
  exact LinearMap.congr_fun he z

set_option backward.isDefEq.respectTransparency false in
theorem residueTensorComplex_d_succ (r : ℕ) :
    (residueTensorComplex K n).d (r+1) r=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [ModuleCat.hom_zero,LinearMap.zero_apply]
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a w
    change (CategoryTheory.MonoidalCategory.whiskerLeft (ModuleCat.of P Q)
      ((complex K n).d (r+1) r)) (a ⊗ₜ[P] w)=0
    rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
    change a ⊗ₜ[P] ((TauCeti.koszulComplex (functional K n)).d
      (r+1) r).hom w=0
    rw [TauCeti.koszulComplex_d_apply]
    exact residue_tmul_differential_zero K n r a w
  · intro x y hx hy
    rw [map_add,hx,hy,add_zero]

theorem residueTensorComplex_d (i j : ℕ) :
    (residueTensorComplex K n).d i j=0 := by
  by_cases h : j+1=i
  · subst i
    exact residueTensorComplex_d_succ K n j
  · exact (residueTensorComplex K n).shape i j h

/-- Every ordinary homology group is its actual exterior-power tensor
term because both adjacent maps were proved zero. -/
def residueTensorHomologyIso (r : ℕ) :
    (residueTensorComplex K n).homology r ≅ (residueTensorComplex K n).X r :=
  (ShortComplex.HomologyData.ofZeros ((residueTensorComplex K n).sc r)
    (residueTensorComplex_d K n _ _) (residueTensorComplex_d K n _ _)).left.homologyIso

/-- The actual one-plane Plucker-ring Tor group, in every homological degree. -/
def residueTorIso (r : ℕ) :
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q)) ≅
      ModuleCat.of P (Q ⊗[P] (⋀[P]^r (Fin n → P))) :=
  torIso K n (ModuleCat.of P Q) r ≪≫ residueTensorHomologyIso K n r

end PaperVerification.AlternatingForms.OnePlaneKoszul
end
end
end TAF_LiteralSource_0290

section TAF_LiteralSource_0291
/- Original module: PaperVerification.AlternatingFormsPolynomialTor -/


/-!
# Ordinary polynomial Tor from the full variable Koszul resolution

Tensoring the actual variable resolution with the actual augmentation
residue makes every differential zero, because each contraction
coefficient lies in the coordinate ideal.  Thus ordinary Tor is the
corresponding tensor of the actual exterior-power term.  This is not yet
the internal-degree comparison needed for the one-plane Koszul clause.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.PolynomialKoszul

open MvPolynomial CategoryTheory CategoryTheory.Limits

universe u
variable (K : Type u) [Field K] (n : ℕ)

local notation "P" => PolynomialRing K n
local notation "Q" => Residue K n
local notation "J" => Ideal.span (Set.range (X : Fin n → P))

theorem residue_smul_eq_zero (p : P) (hp : p∈J) (a : Q) : p • a=0 := by
  change Ideal.Quotient.mk J p*a=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,zero_mul]

theorem variableFunctional_mem_coordinateIdeal (v : Fin n → P) :
    variableFunctional K n v∈J := by
  change variableFunctional K n v∈
    Submodule.span P (Set.range (fun i : Fin n ↦ X (R := K) i))
  rw [←Fintype.range_linearCombination P (fun i : Fin n ↦ X (R := K) i)]
  exact LinearMap.mem_range_self _ v

def residueTensorComplex : ChainComplex (ModuleCat P) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat P)).obj
    (ModuleCat.of P Q)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (resolution K n).complex)

theorem residue_tmul_differential_zero (r : ℕ) (a : Q)
    (z : ⋀[P]^(r+1) (Fin n → P)) :
    a ⊗ₜ[P] TauCeti.koszulDifferential (variableFunctional K n) r z=0 := by
  let T : (⋀[P]^r (Fin n → P)) →ₗ[P] Q ⊗[P] (⋀[P]^r (Fin n → P)) :=
    TensorProduct.mk P Q _ a
  have he : T.comp (TauCeti.koszulDifferential (variableFunctional K n) r)=0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change T (TauCeti.koszulDifferential (variableFunctional K n) r
      (exteriorPower.ιMulti P (r+1) v))=0
    rw [TauCeti.koszulDifferential_ιMulti,map_sum]
    simp only [map_smul]
    apply Finset.sum_eq_zero
    intro i hi
    change ((-1 : P)^i.val*variableFunctional K n (v i)) •
      (a ⊗ₜ[P] exteriorPower.ιMulti P r (i.removeNth v))=0
    rw [TensorProduct.smul_tmul',residue_smul_eq_zero K n _
      (Ideal.mul_mem_left _ _ (variableFunctional_mem_coordinateIdeal K n (v i))),
      TensorProduct.zero_tmul]
  exact LinearMap.congr_fun he z

set_option backward.isDefEq.respectTransparency false in
theorem residueTensorComplex_d_succ (r : ℕ) :
    (residueTensorComplex K n).d (r+1) r=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [ModuleCat.hom_zero,LinearMap.zero_apply]
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a w
    change (CategoryTheory.MonoidalCategory.whiskerLeft (ModuleCat.of P Q)
      ((complex K n).d (r+1) r)) (a ⊗ₜ[P] w)=0
    rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
    change a ⊗ₜ[P] ((TauCeti.koszulComplex (variableFunctional K n)).d
      (r+1) r).hom w=0
    rw [TauCeti.koszulComplex_d_apply]
    exact residue_tmul_differential_zero K n r a w
  · intro x y hx hy
    rw [map_add,hx,hy,add_zero]

theorem residueTensorComplex_d (i j : ℕ) :
    (residueTensorComplex K n).d i j=0 := by
  by_cases h : j+1=i
  · subst i
    exact residueTensorComplex_d_succ K n j
  · exact (residueTensorComplex K n).shape i j h

/-- Every ordinary homology group is its actual exterior-power tensor
term because both adjacent maps were proved zero. -/
def residueTensorHomologyIso (r : ℕ) :
    (residueTensorComplex K n).homology r ≅ (residueTensorComplex K n).X r :=
  (ShortComplex.HomologyData.ofZeros ((residueTensorComplex K n).sc r)
    (residueTensorComplex_d K n _ _) (residueTensorComplex_d K n _ _)).left.homologyIso

/-- The actual polynomial Tor group, in every homological degree. -/
def residueTorIso (r : ℕ) :
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q)) ≅
      ModuleCat.of P (Q ⊗[P] (⋀[P]^r (Fin n → P))) :=
  torIso K n (ModuleCat.of P Q) r ≪≫ residueTensorHomologyIso K n r

end PaperVerification.AlternatingForms.PolynomialKoszul
end
end
end TAF_LiteralSource_0291

section TAF_LiteralSource_0292
/- Original module: PaperVerification.AlternatingFormsBasisDegree -/


/-!
# The genuine internal grading determined by degrees of basis vectors

The pieces are defined by literal coordinate support.  Their direct-sum
property and their equality with spans of the corresponding basis vectors
are proved; no decomposition assumption is supplied by an application.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BasisDegree

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  (B : Module.Basis I R V) (δ : I → ℕ)

def piece (N : ℕ) : Submodule R V :=
  (Finsupp.supported R R {i | δ i=N}).comap B.repr.toLinearMap

theorem mem_piece (N : ℕ) (x : V) :
    x∈piece B δ N ↔ ∀ i,δ i≠N → B.repr x i=0 :=
  Finsupp.mem_supported' R (B.repr x)

theorem basis_mem_piece (i : I) : B i∈piece B δ (δ i) := by
  rw [mem_piece]
  intro j hj
  rw [Module.Basis.repr_self]
  exact Finsupp.single_eq_of_ne (fun hji ↦ hj (congrArg δ hji))

theorem piece_iSupIndep : iSupIndep (piece B δ) := by
  intro N
  rw [Submodule.disjoint_def]
  intro x hx hother
  apply B.repr.injective
  rw [map_zero]
  apply Finsupp.ext
  intro i
  change B.repr x i=0
  by_cases hi : δ i=N
  · have hle : (⨆ M≠N,piece B δ M)≤(B.coord i).ker := by
      apply iSup_le
      intro M
      apply iSup_le
      intro hMN
      intro y hy
      exact LinearMap.mem_ker.mpr ((mem_piece B δ M y).mp hy i
        (by rw [hi]; exact Ne.symm hMN))
    exact LinearMap.mem_ker.mp (hle hother)
  · exact (mem_piece B δ N x).mp hx i hi

theorem piece_iSup : (⨆ N,piece B δ N)=⊤ := by
  apply top_unique
  rw [←B.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  exact (le_iSup (piece B δ) (δ i)) (basis_mem_piece B δ i)

def grading : TauCeti.InternalGrading R V ℕ where
  piece := piece B δ
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (piece_iSupIndep B δ) (piece_iSup B δ)

theorem piece_eq_span (N : ℕ) :
    piece B δ N=Submodule.span R (B '' {i | δ i=N}) := by
  apply le_antisymm
  · intro x hx
    rw [←B.linearCombination_repr x,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    by_cases h : δ i=N
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,h,rfl⟩)
    · rw [(mem_piece B δ N x).mp hx i h,zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    rw [←hi]
    exact basis_mem_piece B δ i

end PaperVerification.AlternatingForms.BasisDegree
end
end
end TAF_LiteralSource_0292

section TAF_LiteralSource_0293
/- Original module: PaperVerification.AlternatingFormsPolynomialTorGrading -/


/-!
# Internal degrees of actual polynomial Tor

The free term is given its genuine monomial-times-exterior-basis grading:
the internal degree of `X^d e_I` is `degree d + card I`.  The degree pieces
after tensoring are defined as the images of those actual subspaces.
Positive monomial coefficients vanish in the augmentation residue; the
degree-r images exhaust the r-th tensor term.  The resulting grading is
transported through the actual ordinary Tor comparison, rather than
defined by the desired concentration formula.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.PolynomialKoszul

open MvPolynomial CategoryTheory CategoryTheory.Limits

universe u
variable (K : Type u) [Field K] (n : ℕ)

local notation "P" => PolynomialRing K n
local notation "Q" => Residue K n
local notation "J" => Ideal.span (Set.range (X : Fin n → P))

abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((complex K n).X r)

abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((residueTensorComplex K n).X r)

instance freeTerm_isScalarTower (r : ℕ) : IsScalarTower K P (freeTermOverK K n r) :=
  IsScalarTower.of_compHom K P ((complex K n).X r)

def freeBasis (r : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) r) P (freeTermOverK K n r) :=
  (Pi.basisFun P (Fin n)).exteriorPower r

def freeMonomialBasis (r : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Set.powersetCard (Fin n) r) K (freeTermOverK K n r) :=
  (MvPolynomial.basisMonomials (Fin n) K).smulTower (freeBasis K n r)

theorem freeMonomialBasis_apply (r : ℕ)
    (d : Fin n →₀ ℕ) (I : Set.powersetCard (Fin n) r) :
    freeMonomialBasis K n r (d,I)=monomial d (1 : K) • freeBasis K n r I := by
  rw [freeMonomialBasis,Module.Basis.smulTower_apply,MvPolynomial.coe_basisMonomials]

def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK K n r) ℕ :=
  BasisDegree.grading (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r)

def specializeFree (r : ℕ) : freeTermOverK K n r →ₗ[K] tensorTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map
    (ModuleCat.ofHom (TensorProduct.mk P Q (⋀[P]^r (Fin n → P)) 1))).hom

theorem specializeFree_apply (r : ℕ) (z : freeTermOverK K n r) :
    specializeFree K n r z=1 ⊗ₜ[P] z := rfl

theorem coordinateIdeal_eq_ker_constantCoeff :
    J=RingHom.ker (MvPolynomial.constantCoeff : P →+* K) := by
  rw [←Set.image_univ,span_X_image_eq_ker_aeval_ite_mem]
  ext p
  simp only [RingHom.mem_ker,Set.compl_univ,Set.mem_empty_iff_false,if_false,
    MvPolynomial.aeval_zero',MvPolynomial.algebraMap_eq,MvPolynomial.C_eq_zero]

def constantCoefficient : P →ₐ[K] K :=
  { MvPolynomial.constantCoeff with
    commutes' := fun c ↦ MvPolynomial.constantCoeff_C _ c }

theorem constantCoefficient_surjective : Function.Surjective (constantCoefficient K n) := by
  intro c
  exact ⟨MvPolynomial.C c,by simp [constantCoefficient]⟩

theorem coordinateIdeal_eq_ker_augmentation :
    J=RingHom.ker (constantCoefficient K n).toRingHom :=
  coordinateIdeal_eq_ker_constantCoeff K n

/-- The augmentation quotient used in the actual derived tensor is
the coefficient field, with every polynomial variable acting as zero. -/
def residueEquivField : Q ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (coordinateIdeal_eq_ker_augmentation K n)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := constantCoefficient K n) (constantCoefficient_surjective K n))

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem residueEquivField_mk (p : P) :
    residueEquivField K n (Ideal.Quotient.mk J p)=MvPolynomial.constantCoeff p := by
  rfl

theorem monomial_mem_coordinateIdeal {d : Fin n →₀ ℕ} (hd : d≠0) :
    (monomial d (1 : K) : P)∈J := by
  rw [coordinateIdeal_eq_ker_constantCoeff,RingHom.mem_ker,
    constantCoeff_monomial,if_neg hd]

theorem specializeFree_monomial_ne_zero (r : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) r) (hd : d≠0) :
    specializeFree K n r (freeMonomialBasis K n r (d,I))=0 := by
  rw [freeMonomialBasis_apply,specializeFree_apply,TensorProduct.tmul_smul,
    TensorProduct.smul_tmul',residue_smul_eq_zero K n _
      (monomial_mem_coordinateIdeal K n hd),TensorProduct.zero_tmul]
  rfl

def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK K n r) :=
  ((freeGrading K n r).piece N).map (specializeFree K n r)

theorem tensorDegreePiece_eq_bot (r N : ℕ) (hNr : N≠r) :
    tensorDegreePiece K n r N=⊥ := by
  apply le_antisymm ?_ bot_le
  rintro z ⟨w,hw,rfl⟩
  change specializeFree K n r w=0
  change w∈BasisDegree.piece (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r) N at hw
  rw [BasisDegree.piece_eq_span] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨d,I⟩,hd,rfl⟩ := hw
    apply specializeFree_monomial_ne_zero K n r d I
    intro hz
    subst d
    simp only [map_zero,zero_add,Set.mem_setOf_eq] at hd
    exact hNr hd.symm
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem specializeFree_surjective (r : ℕ) : Function.Surjective (specializeFree K n r) := by
  intro z
  change Q ⊗[P] (⋀[P]^r (Fin n → P)) at z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a w
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨(p • w : ⋀[P]^r (Fin n → P)),?_⟩
    change (1 : Q) ⊗ₜ[P] (p • w)=Ideal.Quotient.mk J p ⊗ₜ[P] w
    calc
      _ = (p • (1 : Q)) ⊗ₜ[P] w := (TensorProduct.smul_tmul p (1 : Q) w).symm
      _ = _ := congrArg (fun a : Q => a ⊗ₜ[P] w)
        (show p • (1 : Q)=Ideal.Quotient.mk J p from by
          change Ideal.Quotient.mk J p * (1 : Q)=Ideal.Quotient.mk J p
          exact mul_one _)
  · intro x y hx hy
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u+v,map_add _ _ _⟩

theorem tensorDegreePieces_iSup (r : ℕ) : (⨆ N,tensorDegreePiece K n r N)=⊤ := by
  simp only [tensorDegreePiece]
  rw [←Submodule.map_iSup,(freeGrading K n r).isInternal.submodule_iSup_eq_top,
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (specializeFree_surjective K n r)

theorem tensorDegreePiece_diagonal (r : ℕ) : tensorDegreePiece K n r r=⊤ := by
  have hle : (⨆ N,tensorDegreePiece K n r N)≤tensorDegreePiece K n r r := by
    apply iSup_le
    intro N
    by_cases h : N=r
    · subst N; exact le_rfl
    · rw [tensorDegreePiece_eq_bot K n r N h]
      exact bot_le
  rw [tensorDegreePieces_iSup] at hle
  exact top_unique hle

theorem tensorDegreePiece_eq (r N : ℕ) :
    tensorDegreePiece K n r N=if N=r then ⊤ else ⊥ := by
  by_cases h : N=r
  · subst N; rw [if_pos rfl,tensorDegreePiece_diagonal]
  · rw [if_neg h,tensorDegreePiece_eq_bot K n r N h]

/-- These are the images of the original free internal-degree pieces,
with their genuine direct-sum property proved from those images. -/
def tensorGrading (r : ℕ) : TauCeti.InternalGrading K (tensorTermOverK K n r) ℕ where
  piece := tensorDegreePiece K n r
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro N
      by_cases h : N=r
      · subst N
        have hz : (⨆ M≠r,tensorDegreePiece K n r M)=⊥ := by
          apply le_antisymm ?_ bot_le
          apply iSup_le
          intro M
          apply iSup_le
          intro hM
          rw [tensorDegreePiece_eq_bot K n r M hM]
        rw [hz]
        exact disjoint_bot_right
      · rw [tensorDegreePiece_eq_bot K n r N h]
        exact disjoint_bot_left
    · exact tensorDegreePieces_iSup K n r

def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q))

def torTermIsoOverK (r : ℕ) : TorOverK K n r ≅ tensorTermOverK K n r :=
  (ModuleCat.restrictScalars (algebraMap K P)).mapIso (residueTorIso K n r)

def torGrading (r : ℕ) : TauCeti.InternalGrading K (TorOverK K n r) ℕ :=
  (tensorGrading K n r).map (torTermIsoOverK K n r).toLinearEquiv.symm

/-- Concentration of the actual polynomial Tor, with degree pieces
obtained from actual homogeneous monomial terms of the actual resolution. -/
theorem actual_polynomial_Tor_degree (r N : ℕ) :
    (torGrading K n r).piece N=if N=r then ⊤ else ⊥ := by
  rw [torGrading,TauCeti.InternalGrading.map_piece]
  change (tensorDegreePiece K n r N).map _=_
  rw [tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (torTermIsoOverK K n r).toLinearEquiv.symm.surjective
  · simp only [if_neg h,Submodule.map_bot]

end PaperVerification.AlternatingForms.PolynomialKoszul
end
end
end TAF_LiteralSource_0293

section TAF_LiteralSource_0294
/- Original module: PaperVerification.AlternatingFormsOnePlaneTorGrading -/


/-!
# Internal degrees on ordinary Tor of the one-plane quotient

The original degree-one Plucker classes are the variables under the
explicit polynomial isomorphism.  The free-term basis consists of their
literal monomials times exterior basis vectors, with degree `degree d+r`.
After tensoring the actual projective resolution, the degree pieces are
images of those original subspaces.  Positive coefficient monomials
vanish in the actual augmentation quotient, while the diagonal images
exhaust the term.  Transport through the actual derived-tensor
comparison then gives the usual internal-degree concentration.

All proof bodies in this reconstructed file are uncompiled in this run.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial CategoryTheory CategoryTheory.Limits

universe u
variable (K : Type u) [Field K] (n : ℕ)

local notation "P" => Ring K n
local notation "Q" => Residue K n
local notation "J" => augmentationIdeal K n

abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((complex K n).X r)

abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj ((residueTensorComplex K n).X r)

instance freeTerm_isScalarTower (r : ℕ) : IsScalarTower K P (freeTermOverK K n r) :=
  IsScalarTower.of_compHom K P ((complex K n).X r)

def freeBasis (r : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) r) P (freeTermOverK K n r) :=
  (Pi.basisFun P (Fin n)).exteriorPower r

def coordinateMonomial (d : Fin n →₀ ℕ) : P :=
  (polynomialEquiv K n).symm (monomial d (1 : K))

theorem polynomialEquiv_symm_eq_coordinate_evaluation :
    (polynomialEquiv K n).symm.toAlgHom=aeval (generator K n) := by
  ext i
  change (polynomialEquiv K n).symm (X i)=aeval (generator K n) (X i)
  rw [polynomialEquiv_symm_X,aeval_X]

/-- The coefficient basis consists of literal monomials in the
original Plucker-coordinate classes. -/
theorem coordinateMonomial_eq_evaluation (d : Fin n →₀ ℕ) :
    coordinateMonomial K n d=aeval (generator K n) (monomial d (1 : K)) := by
  exact AlgHom.congr_fun (polynomialEquiv_symm_eq_coordinate_evaluation K n) _

def coordinateBasis : Module.Basis (Fin n →₀ ℕ) K P :=
  (MvPolynomial.basisMonomials (Fin n) K).map (polynomialEquiv K n).symm.toLinearEquiv

@[simp] theorem coordinateBasis_apply (d : Fin n →₀ ℕ) :
    coordinateBasis K n d=coordinateMonomial K n d := by
  rw [coordinateBasis,Module.Basis.map_apply,MvPolynomial.coe_basisMonomials]
  rfl

def freeMonomialBasis (r : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Set.powersetCard (Fin n) r) K (freeTermOverK K n r) :=
  (coordinateBasis K n).smulTower (freeBasis K n r)

theorem freeMonomialBasis_apply (r : ℕ)
    (d : Fin n →₀ ℕ) (I : Set.powersetCard (Fin n) r) :
    freeMonomialBasis K n r (d,I)=coordinateMonomial K n d • freeBasis K n r I := by
  rw [freeMonomialBasis,Module.Basis.smulTower_apply,coordinateBasis_apply]

def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK K n r) ℕ :=
  BasisDegree.grading (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r)

def specializeFree (r : ℕ) : freeTermOverK K n r →ₗ[K] tensorTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map
    (ModuleCat.ofHom (TensorProduct.mk P Q (⋀[P]^r (Fin n → P)) 1))).hom

theorem specializeFree_apply (r : ℕ) (z : freeTermOverK K n r) :
    specializeFree K n r z=1 ⊗ₜ[P] z := rfl

theorem augmentationIdeal_map :
    (augmentationIdeal K n).map (polynomialEquiv K n).toRingHom=
      Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) K)) := by
  rw [augmentationIdeal,Ideal.map_span,←Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact polynomialEquiv_generator K n i

def polynomialResidueEquiv : Q ≃ₐ[K] PolynomialKoszul.Residue K n :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv K n) (augmentationIdeal_map K n).symm

/-- The residue of the original one-plane quotient is explicitly the
coefficient field, with all original degree-one coordinates acting as zero. -/
def residueEquivField : Q ≃ₐ[K] K :=
  (polynomialResidueEquiv K n).trans (PolynomialKoszul.residueEquivField K n)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem residueEquivField_mk (p : P) :
    residueEquivField K n (Ideal.Quotient.mk J p)=
      MvPolynomial.constantCoeff (polynomialEquiv K n p) := by
  rw [residueEquivField,AlgEquiv.trans_apply,polynomialResidueEquiv,
    Ideal.quotientEquivAlg_mk,PolynomialKoszul.residueEquivField_mk]

theorem monomial_mem_augmentationIdeal {d : Fin n →₀ ℕ} (hd : d≠0) :
    coordinateMonomial K n d∈J := by
  change (polynomialEquiv K n).symm (monomial d (1 : K))∈J
  change (polynomialEquiv K n).toRingEquiv.symm (monomial d (1 : K))∈J
  rw [Ideal.symm_apply_mem_of_equiv_iff]
  change (monomial d (1 : K) : MvPolynomial (Fin n) K) ∈
    Ideal.map (polynomialEquiv K n).toRingHom (augmentationIdeal K n)
  rw [augmentationIdeal_map]
  exact PolynomialKoszul.monomial_mem_coordinateIdeal K n hd

theorem specializeFree_monomial_ne_zero (r : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) r) (hd : d≠0) :
    specializeFree K n r (freeMonomialBasis K n r (d,I))=0 := by
  rw [freeMonomialBasis_apply,specializeFree_apply,TensorProduct.tmul_smul,
    TensorProduct.smul_tmul',residue_smul_eq_zero K n _
      (monomial_mem_augmentationIdeal K n hd),TensorProduct.zero_tmul]
  rfl

def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK K n r) :=
  ((freeGrading K n r).piece N).map (specializeFree K n r)

theorem tensorDegreePiece_eq_bot (r N : ℕ) (hNr : N≠r) :
    tensorDegreePiece K n r N=⊥ := by
  apply le_antisymm ?_ bot_le
  rintro z ⟨w,hw,rfl⟩
  change specializeFree K n r w=0
  change w∈BasisDegree.piece (freeMonomialBasis K n r) (fun a ↦ a.1.degree+r) N at hw
  rw [BasisDegree.piece_eq_span] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨d,I⟩,hd,rfl⟩ := hw
    apply specializeFree_monomial_ne_zero K n r d I
    intro hz
    subst d
    simp only [map_zero,zero_add,Set.mem_setOf_eq] at hd
    exact hNr hd.symm
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem specializeFree_surjective (r : ℕ) : Function.Surjective (specializeFree K n r) := by
  intro z
  change Q ⊗[P] (⋀[P]^r (Fin n → P)) at z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a w
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨(p • w : ⋀[P]^r (Fin n → P)),?_⟩
    change (1 : Q) ⊗ₜ[P] (p • w)=Ideal.Quotient.mk J p ⊗ₜ[P] w
    calc
      _ = (p • (1 : Q)) ⊗ₜ[P] w := (TensorProduct.smul_tmul p (1 : Q) w).symm
      _ = _ := congrArg (fun a : Q => a ⊗ₜ[P] w)
        (show p • (1 : Q)=Ideal.Quotient.mk J p from by
          change Ideal.Quotient.mk J p * (1 : Q)=Ideal.Quotient.mk J p
          exact mul_one (Ideal.Quotient.mk J p))
  · intro x y hx hy
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact ⟨u+v,map_add _ _ _⟩

theorem tensorDegreePieces_iSup (r : ℕ) : (⨆ N,tensorDegreePiece K n r N)=⊤ := by
  simp only [tensorDegreePiece]
  rw [←Submodule.map_iSup,(freeGrading K n r).isInternal.submodule_iSup_eq_top,
    Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (specializeFree_surjective K n r)

theorem tensorDegreePiece_diagonal (r : ℕ) : tensorDegreePiece K n r r=⊤ := by
  have hle : (⨆ N,tensorDegreePiece K n r N)≤tensorDegreePiece K n r r := by
    apply iSup_le
    intro N
    by_cases h : N=r
    · subst N; exact le_rfl
    · rw [tensorDegreePiece_eq_bot K n r N h]
      exact bot_le
  rw [tensorDegreePieces_iSup] at hle
  exact top_unique hle

theorem tensorDegreePiece_eq (r N : ℕ) :
    tensorDegreePiece K n r N=if N=r then ⊤ else ⊥ := by
  by_cases h : N=r
  · subst N; rw [if_pos rfl,tensorDegreePiece_diagonal]
  · rw [if_neg h,tensorDegreePiece_eq_bot K n r N h]

/-- These are the images of the original free internal-degree pieces,
with their genuine direct-sum property proved from those images. -/
def tensorGrading (r : ℕ) : TauCeti.InternalGrading K (tensorTermOverK K n r) ℕ where
  piece := tensorDegreePiece K n r
  isInternal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro N
      by_cases h : N=r
      · subst N
        have hz : (⨆ M≠r,tensorDegreePiece K n r M)=⊥ := by
          apply le_antisymm ?_ bot_le
          apply iSup_le
          intro M
          apply iSup_le
          intro hM
          rw [tensorDegreePiece_eq_bot K n r M hM]
        rw [hz]
        exact disjoint_bot_right
      · rw [tensorDegreePiece_eq_bot K n r N h]
        exact disjoint_bot_left
    · exact tensorDegreePieces_iSup K n r

def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K P)).obj
    (((Tor (ModuleCat P) r).obj (ModuleCat.of P Q)).obj (ModuleCat.of P Q))

def torTermIsoOverK (r : ℕ) : TorOverK K n r ≅ tensorTermOverK K n r :=
  (ModuleCat.restrictScalars (algebraMap K P)).mapIso (residueTorIso K n r)

def torGrading (r : ℕ) : TauCeti.InternalGrading K (TorOverK K n r) ℕ :=
  (tensorGrading K n r).map (torTermIsoOverK K n r).toLinearEquiv.symm

/-- Concentration of the actual polynomial Tor, with degree pieces
obtained from actual homogeneous monomial terms of the actual resolution. -/
theorem actual_onePlane_Tor_degree (r N : ℕ) :
    (torGrading K n r).piece N=if N=r then ⊤ else ⊥ := by
  rw [torGrading,TauCeti.InternalGrading.map_piece]
  change (tensorDegreePiece K n r N).map _=_
  rw [tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (torTermIsoOverK K n r).toLinearEquiv.symm.surjective
  · simp only [if_neg h,Submodule.map_bot]

end PaperVerification.AlternatingForms.OnePlaneKoszul
end
end
end TAF_LiteralSource_0294

section TAF_LiteralSource_0295
/- Original module: PaperVerification.AlternatingFormsPolynomialDegreeCompatibility -/


/-!
# Compatibility of the actual polynomial differential with internal degree

This proves preservation of the monomial-plus-exterior degree by the
original contraction differential.  The coordinate-contraction identities
are proved from the actual exterior-basis formula.  Their short proofs
follow the corresponding identities in TauCeti's KoszulComplex/Basis
development (commit 8428d6217f74afa72531df0bc85d7b57ab72810f); the present
file imports only the already vendored pinned contraction infrastructure.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.PolynomialKoszul

open MvPolynomial CategoryTheory TauCeti

section CoordinateContraction

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I] (b : Module.Basis I R M)

theorem differential_eq_coordinate_sum [Fintype I] (φ : Module.Dual R M)
    (r : ℕ) (z : ⋀[R]^(r+1) M) :
    koszulDifferential φ r z=∑ i,φ (b i) • koszulDifferential (b.coord i) r z := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply,Submodule.coe_sum]
  conv_lhs => rw [←b.sum_dual_apply_smul_coord φ]
  rw [map_sum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul,LinearMap.smul_apply,Submodule.coe_smul,coe_koszulDifferential_apply]

theorem coordinate_contraction_mem {r : ℕ} {i : I}
    {s : Set.powersetCard I (r+1)} (hi : i∈s.val) :
    koszulDifferential (b.coord i) r (b.exteriorPower (r+1) s)=
      ExteriorAlgebra.basisEraseSign i s.val • b.exteriorPower r
        (Set.powersetCard.ofCard (s := s.val.erase i)
          (by simp [Finset.card_erase_of_mem hi,Set.powersetCard.card_eq])) := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply,←ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp only [hi,if_true,Submodule.coe_smul_of_tower]
  rw [←ExteriorAlgebra.basis_eq_coe_basis,Set.powersetCard.val_ofCard]

theorem coordinate_contraction_not_mem {r : ℕ} {i : I}
    {s : Set.powersetCard I (r+1)} (hi : i∉s.val) :
    koszulDifferential (b.coord i) r (b.exteriorPower (r+1) s)=0 := by
  apply Subtype.ext
  rw [coe_koszulDifferential_apply,←ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.contractLeft_coord_basis]
  simp [hi]

end CoordinateContraction

universe u
variable (K : Type u) [Field K] (n : ℕ)
local notation "P" => PolynomialRing K n

theorem variableFunctional_basis (i : Fin n) :
    variableFunctional K n (Pi.basisFun P (Fin n) i)=X i := by
  rw [Pi.basisFun_apply]
  exact (Fintype.linearCombination_apply_single P (fun i : Fin n ↦ X (R := K) i) i 1).trans
    (one_smul _ _)

def differentialOverK (r : ℕ) : freeTermOverK K n (r+1) →ₗ[K] freeTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map ((complex K n).d (r+1) r)).hom

set_option backward.isDefEq.respectTransparency false in
theorem differentialOverK_apply (r : ℕ) (z : freeTermOverK K n (r+1)) :
    differentialOverK K n r z=koszulDifferential (variableFunctional K n) r z := by
  change ((TauCeti.koszulComplex (variableFunctional K n)).d (r+1) r).hom z=_
  rw [TauCeti.koszulComplex_d_apply]

theorem differentialOverK_monomial_mem (r N : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) (r+1)) (hdeg : d.degree+(r+1)=N) :
    differentialOverK K n r (freeMonomialBasis K n (r+1) (d,I))∈
      (freeGrading K n r).piece N := by
  rw [freeMonomialBasis_apply,differentialOverK_apply]
  change koszulDifferential (variableFunctional K n) r
    (monomial d (1 : K) • (Pi.basisFun P (Fin n)).exteriorPower (r+1) I)∈(freeGrading K n r).piece N
  rw [map_smul,differential_eq_coordinate_sum (Pi.basisFun P (Fin n))]
  simp only [variableFunctional_basis,Finset.smul_sum]
  apply Submodule.sum_mem
  intro i hi
  by_cases hI : i∈I.val
  · rw [coordinate_contraction_mem _ hI,←mul_smul,smul_comm]
    have hm : (monomial d (1 : K) : P)*X i=monomial (d+Finsupp.single i 1) 1 := by
      rw [X,monomial_mul_monomial,mul_one]
    rw [hm]
    let I' : Set.powersetCard (Fin n) r :=
      Set.powersetCard.ofCard (s := I.val.erase i)
        (by simp [Finset.card_erase_of_mem hI,Set.powersetCard.card_eq])
    have hd' : (d+Finsupp.single i 1).degree+r=N := by
      rw [map_add,Finsupp.degree_single]
      omega
    have hmem := BasisDegree.basis_mem_piece (freeMonomialBasis K n r)
      (fun a ↦ a.1.degree+r) (d+Finsupp.single i 1,I')
    change freeMonomialBasis K n r (d+Finsupp.single i 1,I')∈
      (freeGrading K n r).piece ((d+Finsupp.single i 1).degree+r) at hmem
    rw [hd',freeMonomialBasis_apply] at hmem
    rw [Units.smul_def]
    exact ((freeGrading K n r).piece N).toAddSubgroup.zsmul_mem hmem _
  · rw [coordinate_contraction_not_mem _ hI,smul_zero,smul_zero]
    exact Submodule.zero_mem _

/-- The genuine differential of the full polynomial free resolution
preserves the original internal degree in every homological degree. -/
theorem differentialOverK_homogeneous (r N : ℕ) (z : freeTermOverK K n (r+1))
    (hz : z∈(freeGrading K n (r+1)).piece N) :
    differentialOverK K n r z∈(freeGrading K n r).piece N := by
  change z∈BasisDegree.piece (freeMonomialBasis K n (r+1))
    (fun a ↦ a.1.degree+(r+1)) N at hz
  rw [BasisDegree.piece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨d,I⟩,hd,rfl⟩ := hz
    exact differentialOverK_monomial_mem K n r N d I hd
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

end PaperVerification.AlternatingForms.PolynomialKoszul
end
end
end TAF_LiteralSource_0295

section TAF_LiteralSource_0296
/- Original module: PaperVerification.ModuleCatRingEquivTor -/


/-!
# Actual tensor products and projective resolutions under a ring isomorphism

Restriction by the inverse ring isomorphism changes the coefficient ring
of every actual module and resolution.  The balanced tensor products are
compared by the map that keeps every pure tensor unchanged.  Applying this
comparison to an actual projective resolution gives a comparison of the
ordinary derived functor Tor.  The formulas on tensor terms are retained
so that internal gradings of specific resolutions can also be compared.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.ModuleCatRingEquivTor

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

universe u
variable {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)

/-- Modules with their actual scalar action changed through the inverse
ring isomorphism.  Their underlying additive groups are unchanged. -/
abbrev scalarChange : ModuleCat.{u} A ⥤ ModuleCat.{u} D :=
  ModuleCat.restrictScalars e.symm.toRingHom

local instance originalModule (X : ModuleCat.{u} A) :
    Module A ((scalarChange e).obj X) := inferInstanceAs (Module A X)

local instance originalChangedCommute (X : ModuleCat.{u} A) :
    SMulCommClass A D ((scalarChange e).obj X) where
  smul_comm a d x := by
    change a • (e.symm d • x)=e.symm d • (a • x)
    exact smul_comm _ _ _

local instance compatibleOriginalChanged (X Y : ModuleCat.{u} A) :
    TensorProduct.CompatibleSMul A D ((scalarChange e).obj X) ((scalarChange e).obj Y) where
  smul_tmul d x y := by
    change (e.symm d • x) ⊗ₜ[A] y=x ⊗ₜ[A] (e.symm d • y)
    exact TensorProduct.smul_tmul _ _ _

local instance compatibleChangedOriginal (X Y : ModuleCat.{u} A) :
    TensorProduct.CompatibleSMul D A ((scalarChange e).obj X) ((scalarChange e).obj Y) where
  smul_tmul a x y := by
    have h := TensorProduct.smul_tmul (R := D) (e a)
      (x : (scalarChange e).obj X) (y : (scalarChange e).obj Y)
    change (e.symm (e a) • x) ⊗ₜ[D] y=x ⊗ₜ[D] (e.symm (e a) • y) at h
    simpa only [e.symm_apply_apply] using h

/-- The literal identity on pure tensors gives the actual change-of-ring
tensor equivalence. -/
def tensorEquiv (X Y : ModuleCat.{u} A) :
    ((scalarChange e).obj X ⊗[D] (scalarChange e).obj Y) ≃ₗ[D]
      (scalarChange e).obj (X ⊗ Y) :=
  TensorProduct.equivOfCompatibleSMul A D D
    ((scalarChange e).obj X) ((scalarChange e).obj Y)

@[simp] theorem tensorEquiv_tmul (X Y : ModuleCat.{u} A)
    (x : X) (y : Y) : tensorEquiv e X Y (x ⊗ₜ[D] y)=x ⊗ₜ[A] y := rfl

def tensorIso (X Y : ModuleCat.{u} A) :
    (scalarChange e).obj X ⊗ (scalarChange e).obj Y ≅
      (scalarChange e).obj (X ⊗ Y) :=
  (tensorEquiv e X Y).toModuleIso

/-- Naturality in the actual second tensor factor. -/
theorem tensorIso_naturality (X : ModuleCat.{u} A) {Y Z : ModuleCat.{u} A}
    (f : Y ⟶ Z) :
    ((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).map
        ((scalarChange e).map f) ≫ (tensorIso e X Z).hom=
      (tensorIso e X Y).hom ≫ (scalarChange e).map
        (((tensoringLeft (ModuleCat A)).obj X).map f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.inductionOn z ?_ ?_
  · intro x y
    rfl
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The tensor comparison is an isomorphism of actual complexes, with
the actual differentials coming from the original resolution. -/
def tensorComplexIso (X : ModuleCat.{u} A) (C : ChainComplex (ModuleCat.{u} A) ℕ) :
    ((((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      (((scalarChange e).mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) ≅
    (((scalarChange e).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C)) :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ tensorIso e X (C.X i)) (by
    intro i j hij
    exact (tensorIso_naturality e X (C.d i j)).symm)

/-- Actual projective resolutions remain projective resolutions after
changing scalars by a ring isomorphism. -/
def resolution {Y : ModuleCat.{u} A} (P : ProjectiveResolution Y) :
    ProjectiveResolution ((scalarChange e).obj Y) :=
  (scalarChange e).mapProjectiveResolution P

/-- The actual ordinary Tor objects, compared through an actual supplied
projective resolution.  The resolution is data with verified exactness,
not a premise asserting the desired Tor conclusion. -/
def torIso (X Y : ModuleCat.{u} A) (P : ProjectiveResolution Y) (r : ℕ) :
    (((Tor (ModuleCat D) r).obj ((scalarChange e).obj X)).obj ((scalarChange e).obj Y)) ≅
      (scalarChange e).obj (((Tor (ModuleCat A) r).obj X).obj Y) :=
  (resolution e P).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)) r ≪≫
    HomologicalComplex.homologyMapIso (tensorComplexIso e X P.complex) r ≪≫
    (((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).sc r).mapHomologyIso (scalarChange e) ≪≫
    (scalarChange e).mapIso
      (P.isoLeftDerivedObj ((tensoringLeft (ModuleCat A)).obj X) r).symm

section Coefficients

variable {K : Type u} [CommRing K] [Algebra K A] [Algebra K D]
  (f : A ≃ₐ[K] D)

/-- The two actual scalar-restriction functors agree over the original
coefficient ring, with the identity underlying additive map. -/
def coefficientsIso (X : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap K A)).obj X ≅
      (ModuleCat.restrictScalars (algebraMap K D)).obj
        ((scalarChange f.toRingEquiv).obj X) :=
  ModuleCat.restrictScalarsComp'App (algebraMap K D) f.symm.toRingHom
    (algebraMap K A) (by
      apply RingHom.ext
      intro c
      exact (f.symm.commutes c).symm) X

@[simp] theorem coefficientsIso_hom_apply (X : ModuleCat.{u} A) (x : X) :
    (coefficientsIso f X).hom x=x := rfl

@[simp] theorem coefficientsIso_inv_apply (X : ModuleCat.{u} A) (x : X) :
    (coefficientsIso f X).inv x=x := rfl

/-- The tensor comparison over the original coefficient ring keeps
every actual pure tensor unchanged. -/
def tensorIsoOverCoefficients (X Y : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap K D)).obj
        ((scalarChange f.toRingEquiv).obj X ⊗ (scalarChange f.toRingEquiv).obj Y) ≅
      (ModuleCat.restrictScalars (algebraMap K A)).obj (X ⊗ Y) :=
  (ModuleCat.restrictScalars (algebraMap K D)).mapIso
      (tensorIso f.toRingEquiv X Y) ≪≫ (coefficientsIso f (X ⊗ Y)).symm

@[simp] theorem tensorIsoOverCoefficients_hom_tmul (X Y : ModuleCat.{u} A)
    (x : X) (y : Y) :
    (tensorIsoOverCoefficients f X Y).hom (x ⊗ₜ[D] y)=x ⊗ₜ[A] y := rfl

/-- The actual derived tensor comparison, also preserving the original
coefficient-field linear structure. -/
def torIsoOverCoefficients (X Y : ModuleCat.{u} A)
    (P : ProjectiveResolution Y) (r : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K D)).obj
      (((Tor (ModuleCat D) r).obj ((scalarChange f.toRingEquiv).obj X)).obj
        ((scalarChange f.toRingEquiv).obj Y)) ≅
      (ModuleCat.restrictScalars (algebraMap K A)).obj
        (((Tor (ModuleCat A) r).obj X).obj Y) :=
  (ModuleCat.restrictScalars (algebraMap K D)).mapIso
      (torIso f.toRingEquiv X Y P r) ≪≫
    (coefficientsIso f (((Tor (ModuleCat A) r).obj X).obj Y)).symm

end Coefficients

end PaperVerification.ModuleCatRingEquivTor
end
end
end TAF_LiteralSource_0296

section TAF_LiteralSource_0297
/- Original module: PaperVerification.ModuleCatRingEquivTorElementary -/


/-! # Concrete scalar and tensor formulas with opaque coefficient rings

These elementary identities avoid expanding a large algebra equivalence when
specializing actual projective resolutions. All maps are the existing scalar
restriction and balanced tensor maps, and every displayed formula is on the
original underlying elements.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.ModuleCatRingEquivTor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

/-- The native ground-ring action agrees with restriction of scalars. -/
def nativeScalarsEquiv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (B : Type u) [AddCommGroup B] [Module T B] [Module R B] [IsScalarTower R T B] :
    ((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T B)) ≃ₗ[R] B :=
  (show B ≃ₗ[R] ((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T B)) from
    { toFun x := x
      invFun x := x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' c x := by
        change c • x=(algebraMap R T c) • x
        exact (IsScalarTower.algebraMap_smul T c x).symm }).symm

/-- Tensoring with a specified vector, using the actual balanced product. -/
def tensorWithVector {R : Type u} [CommRing R]
    (U V : ModuleCat.{u} R) (x : U) : V ⟶ U ⊗ V :=
  ModuleCat.ofHom (TensorProduct.mk R U V x)

/-- Actual homology of a complex whose differentials are proved zero. -/
def homologyIsoOfZeroDifferentials {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (hd : ∀ i j, C.d i j=0) (r : ℕ) :
    C.homology r ≅ C.X r :=
  (ShortComplex.HomologyData.ofZeros (C.sc r) (hd _ _) (hd _ _)).left.homologyIso

variable {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)

/-- The changed coefficient-residue action is the original quotient product. -/
theorem scalarChange_quotient_smul (J : Ideal A) (d : D) (q : A ⧸ J) :
    d • (show (scalarChange e).obj (ModuleCat.of A (A ⧸ J)) from q) =
      (show (scalarChange e).obj (ModuleCat.of A (A ⧸ J)) from
        Ideal.Quotient.mk J (e.symm d)*q) := rfl

/-- Vanishing of actual tensor differentials is preserved by the explicit
balanced-tensor comparison of the changed projective resolution. -/
theorem resolutionTensor_d_eq_zero (X Y : ModuleCat.{u} A) (P : ProjectiveResolution Y)
    (hd : ∀ i j, ((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).d i j=0) (i j : ℕ) :
    ((((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (resolution e P).complex).d i j=0 := by
  change (((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).map
    ((scalarChange e).map (P.complex.d i j)))=0
  apply (cancel_mono (tensorIso e X (P.complex.X j)).hom).mp
  rw [zero_comp,tensorIso_naturality]
  change (tensorIso e X (P.complex.X i)).hom ≫
    (scalarChange e).map
      (((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).d i j)=0
  rw [hd, (scalarChange e).map_zero, comp_zero]

/-- The scalar associativity needed for the original exterior Koszul degree. -/
theorem associate_integer_smul {R M : Type*} [Monoid R] [AddCommGroup M]
    [DistribMulAction R M] (a b : R) (n : ℤ) (x : M) :
    a • b • (n • x)=n • ((a*b) • x) := by
  rw [←mul_smul,smul_comm]

end PaperVerification.ModuleCatRingEquivTor
end
end
end TAF_LiteralSource_0297

section TAF_LiteralSource_0298
/- Original module: PaperVerification.AlternatingFormsOnePlaneDegreeCompatibility -/


/-!
# The actual one-plane resolution preserves internal degree

The degree-one variables are the classes of the original Plucker
coordinates.  Their monomials are identified through the explicit
ring isomorphism, and each actual contraction term adds one variable
while removing one exterior basis factor.  Thus the ordinary
one-plane Tor grading defined by images of these homogeneous pieces
is the internal grading of the original homogeneous resolution.

This is an uncompiled proof candidate, not a completion certificate.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial CategoryTheory TauCeti

universe u
variable (K : Type u) [Field K] (n : ℕ)
local notation "P" => Ring K n

theorem functional_basis (i : Fin n) :
    functional K n (Pi.basisFun P (Fin n) i)=generator K n i := by
  rw [Pi.basisFun_apply]
  exact (Fintype.linearCombination_apply_single P (generator K n) i 1).trans
    (one_smul _ _)

def differentialOverK (r : ℕ) : freeTermOverK K n (r+1) →ₗ[K] freeTermOverK K n r :=
  ((ModuleCat.restrictScalars (algebraMap K P)).map ((complex K n).d (r+1) r)).hom

set_option backward.isDefEq.respectTransparency false in
theorem differentialOverK_apply (r : ℕ) (z : freeTermOverK K n (r+1)) :
    differentialOverK K n r z=koszulDifferential (functional K n) r z := by
  change ((TauCeti.koszulComplex (functional K n)).d (r+1) r).hom z=_
  rw [TauCeti.koszulComplex_d_apply]

theorem differentialOverK_monomial_mem (r N : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) (r+1)) (hdeg : d.degree+(r+1)=N) :
    differentialOverK K n r (freeMonomialBasis K n (r+1) (d,I))∈
      (freeGrading K n r).piece N := by
  rw [freeMonomialBasis_apply,differentialOverK_apply]
  change koszulDifferential (functional K n) r
    (coordinateMonomial K n d • (Pi.basisFun P (Fin n)).exteriorPower (r+1) I)∈(freeGrading K n r).piece N
  rw [map_smul,PolynomialKoszul.differential_eq_coordinate_sum (Pi.basisFun P (Fin n))]
  simp only [functional_basis,Finset.smul_sum]
  apply Submodule.sum_mem
  intro i hi
  by_cases hI : i∈I.val
  · rw [PolynomialKoszul.coordinate_contraction_mem _ hI]
    have hm : coordinateMonomial K n d*generator K n i=
        coordinateMonomial K n (d+Finsupp.single i 1) := by
      apply (polynomialEquiv K n).injective
      simp only [map_mul,coordinateMonomial,AlgEquiv.apply_symm_apply,
        polynomialEquiv_generator,X,monomial_mul_monomial,mul_one]
    let I' : Set.powersetCard (Fin n) r :=
      Set.powersetCard.ofCard (s := I.val.erase i)
        (by simp [Finset.card_erase_of_mem hI,Set.powersetCard.card_eq])
    have hd' : (d+Finsupp.single i 1).degree+r=N := by
      rw [map_add,Finsupp.degree_single]
      omega
    have hmem := BasisDegree.basis_mem_piece (freeMonomialBasis K n r)
      (fun a ↦ a.1.degree+r) (d+Finsupp.single i 1,I')
    change freeMonomialBasis K n r (d+Finsupp.single i 1,I')∈
      (freeGrading K n r).piece ((d+Finsupp.single i 1).degree+r) at hmem
    rw [hd',freeMonomialBasis_apply] at hmem
    have hsign := ((freeGrading K n r).piece N).toAddSubgroup.zsmul_mem hmem
      (ExteriorAlgebra.basisEraseSign i I.val : ℤ)
    change coordinateMonomial K n d • generator K n i •
        ((ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
          (Pi.basisFun P (Fin n)).exteriorPower r I') ∈ (freeGrading K n r).piece N
    have heq : coordinateMonomial K n d • generator K n i •
        ((ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
          (Pi.basisFun P (Fin n)).exteriorPower r I') =
      (ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
        (coordinateMonomial K n (d+Finsupp.single i 1) •
          (Pi.basisFun P (Fin n)).exteriorPower r I') := by
      calc
        _ = (ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
            ((coordinateMonomial K n d*generator K n i) •
              (Pi.basisFun P (Fin n)).exteriorPower r I') :=
          ModuleCatRingEquivTor.associate_integer_smul
            (coordinateMonomial K n d) (generator K n i)
            (ExteriorAlgebra.basisEraseSign i I.val : ℤ)
            ((Pi.basisFun P (Fin n)).exteriorPower r I')
        _ = _ := congrArg
          (fun a : P => (ExteriorAlgebra.basisEraseSign i I.val : ℤ) •
            (a • (Pi.basisFun P (Fin n)).exteriorPower r I')) hm
    rw [heq]
    exact hsign
  · rw [PolynomialKoszul.coordinate_contraction_not_mem _ hI,smul_zero,smul_zero]
    exact Submodule.zero_mem _

/-- The genuine differential of the full polynomial free resolution
preserves the original internal degree in every homological degree. -/
theorem differentialOverK_homogeneous (r N : ℕ) (z : freeTermOverK K n (r+1))
    (hz : z∈(freeGrading K n (r+1)).piece N) :
    differentialOverK K n r z∈(freeGrading K n r).piece N := by
  change z∈BasisDegree.piece (freeMonomialBasis K n (r+1))
    (fun a ↦ a.1.degree+(r+1)) N at hz
  rw [BasisDegree.piece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨d,I⟩,hd,rfl⟩ := hz
    exact differentialOverK_monomial_mem K n r N d I hd
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

end PaperVerification.AlternatingForms.OnePlaneKoszul
end
end
end TAF_LiteralSource_0298

section TAF_LiteralSource_0299
/- Original module: PaperVerification.AlternatingFormsOnePlaneDegreeFaithfulness -/


/-!
# Comparison with the original homogeneous Plucker degree

The coordinate-monomial grading used on the one-plane resolution is
proved equal to the images of homogeneous polynomials in the original
Plucker presentation.  This prevents a transported coordinate grading
from silently changing the intended internal degree.

This reconstructed source is uncompiled in the current run.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial

universe u
variable (K : Type u) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateEvaluation_eq_quotient_rename :
    aeval (generator K n)=
      (Ideal.Quotient.mkₐ K (matrixPluckerIdeal (K := K) (s := 1) (n := n))).comp
        (MvPolynomial.rename onePlaneIndex) := by
  ext i
  simp only [aeval_X,AlgHom.comp_apply,rename_X]
  rfl

theorem coordinateMonomial_eq_original_class (d : Fin n →₀ ℕ) :
    coordinateMonomial K n d=Ideal.Quotient.mk _
      (MvPolynomial.rename onePlaneIndex (monomial d (1 : K))) := by
  rw [coordinateMonomial_eq_evaluation,coordinateEvaluation_eq_quotient_rename]
  rfl

def originalDegree (N : ℕ) : Submodule K (Ring K n) :=
  HomogeneousIdealPieces.piece matrixPluckerIdeal N

theorem coordinateBasis_mem_originalDegree (d : Fin n →₀ ℕ) :
    coordinateBasis K n d∈originalDegree K n d.degree := by
  rw [coordinateBasis_apply,coordinateMonomial_eq_original_class]
  exact ⟨MvPolynomial.rename onePlaneIndex (monomial d (1 : K)),
    (isHomogeneous_monomial (1 : K) rfl).rename_isHomogeneous,rfl⟩

theorem onePlaneIdeal_isHomogeneous :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex 1 n) K) := by
  rw [onePlane_matrixPluckerIdeal]
  exact Ideal.IsHomogeneous.bot _

/-- The degree used on the coefficient basis is exactly the image of
the original ordinary homogeneous Plucker-polynomial subspace. -/
theorem coefficientDegree_eq_originalDegree (N : ℕ) :
    BasisDegree.piece (coordinateBasis K n) Finsupp.degree N=originalDegree K n N := by
  let G := HomogeneousIdealPieces.grading
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)) (onePlaneIdeal_isHomogeneous K n)
  have hB : ∀ d,coordinateBasis K n d∈G.piece d.degree := by
    intro d
    rw [HomogeneousIdealPieces.grading_piece]
    exact coordinateBasis_mem_originalDegree K n d
  have h := GradedComponentBasis.span_homogeneous_basis_piece G
    (coordinateBasis K n) Finsupp.degree hB N
  have hset : coordinateBasis K n '' {d | d.degree=N}=
      Set.range (fun d : {d : Fin n →₀ ℕ // d.degree=N} ↦ coordinateBasis K n d.val) := by
    ext x
    constructor
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
    · rintro ⟨d,rfl⟩
      exact ⟨d.val,d.property,rfl⟩
  rw [BasisDegree.piece_eq_span,hset,h,HomogeneousIdealPieces.grading_piece]
  rfl

end PaperVerification.AlternatingForms.OnePlaneKoszul
end
end
end TAF_LiteralSource_0299

section TAF_LiteralSource_0300
/- Original module: PaperVerification.AlternatingFormsChartConverse -/


/-!
# The converse between Plücker isotropy and row isotropy on a big cell

Selecting the complementary pivot columns turns a Plücker wedge equation into
each actual row-pair restriction equation. The determinant identity is integral;
no radical, pointwise vanishing principle, or dimension assumption is used.
This file is a fresh reconstruction after loss of the earlier source.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {t n m : ℕ}

/-- Split the first two columns from the remaining pivot columns. -/
def chartTwoTailEquiv (t : ℕ) : Fin 2 ⊕ Fin t ≃ Fin (t+2) :=
  (finSumFinEquiv : Fin 2 ⊕ Fin t ≃ Fin (2+t)).trans
    (finCongr (Nat.add_comm 2 t))

@[simp] theorem chartTwoTailEquiv_zero (t : ℕ) :
    chartTwoTailEquiv t (Sum.inl 0)=0 := by
  apply Fin.ext
  simp [chartTwoTailEquiv]

@[simp] theorem chartTwoTailEquiv_one (t : ℕ) :
    chartTwoTailEquiv t (Sum.inl 1)=(0 : Fin (t+1)).succ := by
  apply Fin.ext
  simp [chartTwoTailEquiv]

@[simp] theorem chartTwoTailEquiv_tail (t : ℕ) (i : Fin t) :
    chartTwoTailEquiv t (Sum.inr i)=i.succ.succ := by
  apply Fin.ext
  simp [chartTwoTailEquiv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Any ordered pair of distinct rows can be made the first two rows. -/
theorem exists_chart_row_permutation (i j : Fin (t+2)) (hij : i≠j) :
    ∃ σ : Equiv.Perm (Fin (t+2)), σ 0=i ∧ σ (Fin.succ 0)=j := by
  let a : Fin 2 → Fin (t+2) := fun z ↦ chartTwoTailEquiv t (Sum.inl z)
  let b : Fin 2 → Fin (t+2) := ![i,j]
  have ha : Function.Injective a := (chartTwoTailEquiv t).injective.comp Sum.inl_injective
  have hb : Function.Injective b := by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [b]
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  refine ⟨σ, ?_, ?_⟩
  · simpa only [a,b,chartTwoTailEquiv_zero,Matrix.cons_val_zero] using hσ 0
  · simpa only [a,b,chartTwoTailEquiv_one,Matrix.cons_val_one,Matrix.cons_val_zero] using hσ 1

/-- With the other columns fixed to complementary pivots, the determinant is
the indicated two by two minor, up to the actual row-permutation sign. -/
theorem determinant_complementary_pivots
    {R : Type*} [CommRing R]
    (A : Matrix (Fin (t+2)) (Fin n) R) (p : Fin (t+2) → Fin n)
    (hp : (fun i j ↦ A i (p j)) = (1 : Matrix (Fin (t+2)) (Fin (t+2)) R))
    (σ : Equiv.Perm (Fin (t+2))) (a b : Fin n) :
    ((Equiv.Perm.sign σ : ℤ) : R) *
        Matrix.det (Matrix.of fun (i j : Fin (t+2)) ↦ A i
          (Fin.cons (α := fun _ : Fin (t+2) => Fin n) a
            (Fin.cons (α := fun _ : Fin (t+1) => Fin n) b
              (fun z : Fin t ↦ p (σ z.succ.succ))) j)) =
      A (σ 0) a * A (σ (Fin.succ 0)) b -
        A (σ 0) b * A (σ (Fin.succ 0)) a := by
  classical
  let M : Matrix (Fin (t+2)) (Fin (t+2)) R :=
    Matrix.of fun (i j : Fin (t+2)) ↦ A i (Fin.cons (α := fun _ : Fin (t+2) => Fin n) a
            (Fin.cons (α := fun _ : Fin (t+1) => Fin n) b
              (fun z : Fin t ↦ p (σ z.succ.succ))) j)
  let U : Matrix (Fin 2) (Fin 2) R :=
    !![A (σ 0) a, A (σ 0) b;
       A (σ (Fin.succ 0)) a, A (σ (Fin.succ 0)) b]
  let L : Matrix (Fin t) (Fin 2) R :=
    fun i j ↦ if j=0 then A (σ i.succ.succ) a else A (σ i.succ.succ) b
  have hp' (i j : Fin (t+2)) : A i (p j) = if i=j then 1 else 0 := by
    exact congrFun (congrFun hp i) j
  have hblock :
      (M.submatrix σ id).submatrix (chartTwoTailEquiv t) (chartTwoTailEquiv t) =
        Matrix.fromBlocks U 0 L 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        fin_cases i <;> fin_cases j <;>
          simp [M,U,Matrix.submatrix_apply]
      | inr j =>
        fin_cases i <;>
          simp [M,Matrix.submatrix_apply,hp',σ.injective.eq_iff,Fin.succ_ne_zero,
            Ne.symm (Fin.succ_ne_zero j.succ),Ne.symm (Fin.succ_succ_ne_one j)]
    | inr i =>
      cases j with
      | inl j =>
        fin_cases j <;> simp [M,L,Matrix.submatrix_apply,Matrix.fromBlocks_apply₂₁] <;> rfl
      | inr j =>
        simp [M,Matrix.submatrix_apply,hp',σ.injective.eq_iff,Matrix.one_apply]
  calc
    ((Equiv.Perm.sign σ : ℤ) : R) * Matrix.det M =
        Matrix.det (M.submatrix σ id) := (Matrix.det_permute σ M).symm
    _ = Matrix.det ((M.submatrix σ id).submatrix
        (chartTwoTailEquiv t) (chartTwoTailEquiv t)) :=
      (Matrix.det_submatrix_equiv_self _ _).symm
    _ = Matrix.det U := by rw [hblock,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,mul_one]
    _ = _ := by simp only [U,Matrix.det_fin_two_of]

/-- A complementary-pivot wedge equation is precisely a row-pair restriction.
This identity is valid over every commutative K-algebra. -/
theorem matrixMinorEvaluation_complementary_isotropy
    {R : Type*} [CommRing R] [Algebra K R]
    (f : StrictPairs n → K) (A : Matrix (Fin (t+2)) (Fin n) R)
    (p : Fin (t+2) → Fin n)
    (hp : (fun i j ↦ A i (p j)) = (1 : Matrix (Fin (t+2)) (Fin (t+2)) R))
    (σ : Equiv.Perm (Fin (t+2))) :
    ((Equiv.Perm.sign σ : ℤ) : R) *
      matrixMinorEvaluation (K := K) A
        (pluckerIsotropyEquation f (fun z ↦ p (σ z.succ.succ))) =
      alternatingRowPair f A (σ 0) (σ (Fin.succ 0)) := by
  classical
  simp only [pluckerIsotropyEquation,map_sum,map_smul,
    matrixMinorEvaluation_orderedCoordinate,alternatingRowPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_smul_comm,determinant_complementary_pivots A p hp σ a.val.1 a.val.2]

/-- The row-isotropy ideal is the image of the actual Plücker isotropy ideal.
This is ideal equality, retaining the scheme structure on the chart. -/
theorem isotropicPluckerIdeal_map_chart_eq [CharZero K]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (isotropicPluckerIdeal forms).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        isotropicChartIdeal p forms := by
  classical
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    have h := isotropicPluckerIdeal_le_chartKernel p forms hq
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 at h
    change matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q ∈ isotropicChartIdeal p forms
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨l,ij⟩,rfl⟩
    obtain ⟨σ,hσ0,hσ1⟩ := exists_chart_row_permutation ij.val.1 ij.val.2
      (ne_of_lt ij.property)
    let J : Fin t → Fin n := fun z ↦ p.val (σ z.succ.succ)
    have hmem :
        matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)
          (pluckerIsotropyEquation (forms l) J) ∈
          (isotropicPluckerIdeal forms).map
            (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom :=
      Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨(l,J),rfl⟩))
    have he := matrixMinorEvaluation_complementary_isotropy (forms l)
      (pluckerChartMatrix (K := K) p) p.val (pluckerChartMatrix_pivot p) σ
    rw [hσ0,hσ1] at he
    change alternatingRowPair (forms l) (pluckerChartMatrix p) ij.val.1 ij.val.2 ∈ _
    rw [←he]
    exact Ideal.mul_mem_left _ _ hmem

theorem matrixMinorEvaluation_chart_kernel (p : PluckerIndex (t+2) n) :
    RingHom.ker (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
      pluckerBigCellIdeal (K := K) p := by
  ext q
  change matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q=0 ↔ _
  rw [←pluckerBigCellToMatrix_class]
  change pluckerBigCellEquiv (K := K) p (pluckerBigCellClass (K := K) p q)=0 ↔ _
  have he : pluckerBigCellEquiv (K := K) p (pluckerBigCellClass (K := K) p q)=0 ↔
      pluckerBigCellClass (K := K) p q=0 := by
    constructor
    · intro h
      apply (pluckerBigCellEquiv (K := K) p).injective
      simpa only [map_zero] using h
    · intro h
      rw [h,map_zero]
  exact he.trans Ideal.Quotient.eq_zero_iff_mem

/-- The full kernel includes exactly the original isotropy ideal and the
normalization of the selected pivot coordinate. -/
theorem isotropicChartEvaluation_kernel [CharZero K]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1} := by
  have h := Ideal.comap_map_of_surjective
    (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom
    (matrixMinorEvaluation_chart_surjective p) (isotropicPluckerIdeal forms)
  rw [isotropicPluckerIdeal_map_chart_eq p forms,
    ←RingHom.ker_eq_comap_bot,matrixMinorEvaluation_chart_kernel] at h
  have hk : RingHom.ker (isotropicChartEvaluation p forms).toRingHom =
      (isotropicChartIdeal p forms).comap
        (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom := by
    ext q
    change (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q)=0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hk,h,pluckerBigCellIdeal]
  have hle : matrixPluckerIdeal (K := K) (s := t+2) (n := n) ≤
      isotropicPluckerIdeal (t := t) forms := le_sup_left
  rw [←sup_assoc,sup_of_le_left hle]

/-- The actual normalized Plücker quotient is the affine scheme chart cut out
by the pairwise row restrictions. Both quotient ideals are stated literally. -/
def isotropicPluckerBigCellEquiv [CharZero K]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K ⧸
      (isotropicPluckerIdeal forms ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms) :=
  (Ideal.quotientEquivAlgOfEq K (isotropicChartEvaluation_kernel p forms).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (isotropicChartEvaluation_surjective p forms))

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0300

section TAF_LiteralSource_0301
/- Original module: PaperVerification.AlternatingFormsConnectedGrading -/


/-!
# Connectedness of the original homogeneous quotient grading

The grading in this file is the image of the ordinary polynomial grading.
Its degree-zero subspace consists precisely of scalar multiples of the unit,
and multiplication adds degrees.  An actual augmentation to the coefficient
field proves that the scalar embedding is injective.  These facts are the
connected-graded hypotheses in the homological definition of a Koszul algebra;
they do not assert anything about Tor or assume a resolution.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The degree-zero part of the actual quotient is its scalar subspace. -/
theorem homogeneousQuotient_degree_zero (Q : Ideal P) :
    HomogeneousIdealPieces.piece Q 0=(1 : Submodule K (P⧸Q)) := by
  rw [HomogeneousIdealPieces.piece,homogeneousSubmodule_zero]
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨c,rfl⟩ := Submodule.mem_one.mp hp
    exact Submodule.mem_one.mpr ⟨c,((Ideal.Quotient.mkₐ K Q).commutes c).symm⟩
  · intro hx
    obtain ⟨c,rfl⟩ := Submodule.mem_one.mp hx
    exact ⟨algebraMap K P c,Submodule.mem_one.mpr ⟨c,rfl⟩,
      (Ideal.Quotient.mkₐ K Q).commutes c⟩

/-- Multiplication in the original quotient adds the original Plücker degrees. -/
theorem homogeneousQuotient_mul_mem (Q : Ideal P) (i j : ℕ)
    (x y : P⧸Q)
    (hx : x∈HomogeneousIdealPieces.piece Q i)
    (hy : y∈HomogeneousIdealPieces.piece Q j) :
    x*y∈HomogeneousIdealPieces.piece Q (i+j) := by
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨q,hq,rfl⟩ := hy
  change p.IsHomogeneous i at hp
  change q.IsHomogeneous j at hq
  exact ⟨p*q,hp.mul hq,map_mul (Ideal.Quotient.mkₐ K Q) p q⟩

/-- An actual coefficient-field augmentation makes the scalar embedding
injective, so connectedness is not merely an equality with a zero subspace. -/
theorem augmentedQuotient_scalar_injective (Q : Ideal P) (ε : (P⧸Q) →ₐ[K] K) :
    Function.Injective (algebraMap K (P⧸Q)) := by
  apply Function.LeftInverse.injective (g := ε)
  intro c
  simpa only [Algebra.algebraMap_self,RingHom.id_apply] using ε.commutes c

/-- The ordinary homogeneous quotient grading is connected.  The actual
direct-sum decomposition is constructed by `HomogeneousIdealPieces.grading`;
its piece formula is retained here, alongside the scalar embedding and the
multiplication law. -/
theorem homogeneousQuotient_connected
    (Q : Ideal P) (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
    (ε : (P⧸Q) →ₐ[K] K) :
    (∀ r,(HomogeneousIdealPieces.grading Q hQ).piece r=
      HomogeneousIdealPieces.piece Q r) ∧
    HomogeneousIdealPieces.piece Q 0=(1 : Submodule K (P⧸Q)) ∧
    Function.Injective (algebraMap K (P⧸Q)) ∧
    (∀ i j (x y : P⧸Q),
      x∈HomogeneousIdealPieces.piece Q i →
      y∈HomogeneousIdealPieces.piece Q j →
      x*y∈HomogeneousIdealPieces.piece Q (i+j)) :=
  ⟨HomogeneousIdealPieces.grading_piece Q hQ,
    homogeneousQuotient_degree_zero Q,
    augmentedQuotient_scalar_injective Q ε,
    homogeneousQuotient_mul_mem Q⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0301

section TAF_LiteralSource_0302
/- Original module: PaperVerification.KoszulSyzygies -/


/-!
# Explicit first syzygies of a regular sequence

This gives the coordinate form of the first exactness statement in the Koszul
complex. The regular-sequence exactness theorem is proved in the pinned,
vendored dependency; this file identifies its image with literal alternating
coefficient matrices. It is the syzygy statement needed for the Jacobian
divergence quotient.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace PaperVerification.KoszulSyzygies

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- Contracting a symmetric matrix with an alternating coefficient matrix gives zero. -/
theorem symmetric_skew_sum (S A : ι → ι → R) (hS : ∀ i j, S i j = S j i) :
    (∑ i, ∑ j, S i j * (A j i - A i j)) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hS i j]

/-- The coefficient map `(g_i) ↦ ∑ g_i f_i`. -/
def coefficient (f : ι → R) : (ι → R) →ₗ[R] R :=
  Fintype.linearCombination R f

@[simp] theorem coefficient_apply (f g : ι → R) :
    coefficient f g = ∑ i, g i * f i := by
  simp [coefficient, Fintype.linearCombination_apply, smul_eq_mul]

/-- A matrix parametrizes the familiar first Koszul relations. -/
def boundary (f : ι → R) : (ι → ι → R) →ₗ[R] (ι → R) where
  toFun A i := ∑ j, f j * (A j i - A i j)
  map_add' A B := by
    ext i
    simp only [Pi.add_apply, add_sub_add_comm, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

@[simp] theorem boundary_apply (f : ι → R) (A : ι → ι → R) (i : ι) :
    boundary f A i = ∑ j, f j * (A j i - A i j) := rfl

theorem coefficient_boundary (f : ι → R) (A : ι → ι → R) :
    coefficient f (boundary f A) = 0 := by
  have h := symmetric_skew_sum (fun i j => f i * f j) A (fun i j => mul_comm _ _)
  simpa only [coefficient_apply, boundary_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc,
    mul_comm, mul_left_comm] using h

theorem boundary_range_le_kernel (f : ι → R) :
    LinearMap.range (boundary f) ≤ LinearMap.ker (coefficient f) := by
  rintro _ ⟨A, rfl⟩
  exact coefficient_boundary f A

/-- A decomposable two-vector maps to the elementary Koszul relation. -/
theorem koszul_two_decomposable (f : ι → R) (v : Fin 2 → (ι → R)) :
    exteriorPower.oneEquiv R (ι → R)
        (TauCeti.koszulDifferential (coefficient f) 1 (exteriorPower.ιMulti R 2 v)) =
      coefficient f (v 0) • v 1 - coefficient f (v 1) • v 0 := by
  simp [TauCeti.koszulDifferential_ιMulti, Fin.sum_univ_two,
    exteriorPower.oneEquiv_ιMulti, Fin.removeNth, Fin.succAbove, Fin.tail, sub_eq_add_neg]

/-- Every value of the actual second Koszul differential has the coordinate matrix form. -/
theorem koszul_two_mem_boundary_range (f : ι → R)
    (y : ⋀[R]^2 (ι → R)) :
    exteriorPower.oneEquiv R (ι → R) (TauCeti.koszulDifferential (coefficient f) 1 y)
      ∈ LinearMap.range (boundary f) := by
  let L : (⋀[R]^2 (ι → R)) →ₗ[R] (ι → R) :=
    (exteriorPower.oneEquiv R (ι → R)).toLinearMap.comp
      (TauCeti.koszulDifferential (coefficient f) 1)
  have hle : Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) ≤
      (LinearMap.range (boundary f)).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change L (exteriorPower.ιMulti R 2 v) ∈ LinearMap.range (boundary f)
    refine ⟨fun i j => v 0 i * v 1 j, ?_⟩
    change boundary f (fun i j => v 0 i * v 1 j) =
      exteriorPower.oneEquiv R (ι → R)
        (TauCeti.koszulDifferential (coefficient f) 1 (exteriorPower.ιMulti R 2 v))
    rw [koszul_two_decomposable]
    ext i
    simp only [boundary_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      coefficient_apply, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hy : y ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  exact hle hy

/-- A regular sequence has precisely the first syzygies generated by alternating matrices. -/
theorem kernel_eq_boundary_range {n : ℕ} (f : Fin n → R)
    (hf : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) :
    LinearMap.ker (coefficient f) = LinearMap.range (boundary f) := by
  apply le_antisymm
  · intro g hg
    have hg' : coefficient f g = 0 := hg
    let x : ⋀[R]^1 (Fin n → R) := (exteriorPower.oneEquiv R (Fin n → R)).symm g
    have hx : TauCeti.koszulDifferential (coefficient f) 0 x = 0 := by
      apply (exteriorPower.zeroEquiv R (Fin n → R)).injective
      rw [map_zero, TauCeti.zeroEquiv_koszulDifferential_zero]
      simpa only [x, LinearEquiv.apply_symm_apply] using hg'
    have hex := TauCeti.koszulComplex.exactAt_of_isWeaklyRegular f hf 0
    rw [TauCeti.koszulComplex.exactAt_succ_iff] at hex
    obtain ⟨y, hy⟩ := (hex x).mp hx
    have h := koszul_two_mem_boundary_range f y
    change TauCeti.koszulDifferential (coefficient f) 1 y = x at hy
    rw [hy] at h
    simpa only [x, LinearEquiv.apply_symm_apply] using h
  · exact boundary_range_le_kernel f

end PaperVerification.KoszulSyzygies
end
end
end TAF_LiteralSource_0302

section TAF_LiteralSource_0303
/- Original module: PaperVerification.FermionWeightedLeading -/


/-!
# Weighted leading components and shifted Koszul relations

All degree bounds are assertions about the actual polynomial coefficients.
The top product identity and the homogeneous first-syzygy lift are proved
for arbitrary nonnegative integer weights and every coefficient ring.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Filtered

open MvPolynomial
open scoped BigOperators Pointwise

variable {R ι : Type*} [CommRing R] (w : ι → ℕ)

def Bound (d : ℕ) (p : MvPolynomial ι R) : Prop :=
  ∀ a, p.coeff a ≠ 0 → Finsupp.weight w a ≤ d

def StrictBound (d : ℕ) (p : MvPolynomial ι R) : Prop :=
  ∀ a, p.coeff a ≠ 0 → Finsupp.weight w a < d

theorem bound_zero (d : ℕ) : Bound w d (0 : MvPolynomial ι R) := by simp [Bound]

theorem strictBound_zero (d : ℕ) : StrictBound w d (0 : MvPolynomial ι R) := by simp [StrictBound]

theorem Bound.mono {d e : ℕ} {p : MvPolynomial ι R} (hp : Bound w d p) (hde : d ≤ e) :
    Bound w e p := fun a ha ↦ (hp a ha).trans hde

theorem StrictBound.bound {d : ℕ} {p : MvPolynomial ι R} (hp : StrictBound w d p) :
    Bound w d p := fun a ha ↦ (hp a ha).le

theorem bound_add {d : ℕ} {p q : MvPolynomial ι R} (hp : Bound w d p) (hq : Bound w d q) :
    Bound w d (p + q) := by
  intro a ha
  by_cases hp0 : p.coeff a = 0
  · exact hq a (by simpa only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp0,zero_add] using ha)
  · exact hp a hp0

theorem bound_sub {d : ℕ} {p q : MvPolynomial ι R} (hp : Bound w d p) (hq : Bound w d q) :
    Bound w d (p - q) := by
  intro a ha
  by_cases hp0 : p.coeff a = 0
  · exact hq a (by simpa only [coeff_sub,hp0,zero_sub,neg_ne_zero] using ha)
  · exact hp a hp0

theorem bound_sum {J : Type*} (S : Finset J) (p : J → MvPolynomial ι R) (d : ℕ)
    (hp : ∀ j ∈ S, Bound w d (p j)) : Bound w d (∑ j ∈ S, p j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using bound_zero w d
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj]
      exact bound_add w (hp j (Finset.mem_insert_self _ _))
        (ih (fun k hk ↦ hp k (Finset.mem_insert_of_mem hk)))

theorem bound_mul {a b : ℕ} {p q : MvPolynomial ι R} (hp : Bound w a p) (hq : Bound w b q) :
    Bound w (a + b) (p * q) := by
  classical
  intro e he
  obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_add.mp
    (support_mul p q (mem_support_iff.mpr he))
  rw [map_add]
  exact add_le_add (hp u (mem_support_iff.mp hu)) (hq v (mem_support_iff.mp hv))

theorem bound_component (d : ℕ) (p : MvPolynomial ι R) :
    Bound w d (weightedHomogeneousComponent w d p) :=
  fun a ha ↦ (weightedHomogeneousComponent_isWeightedHomogeneous d p ha).le

theorem homogeneous_bound {d : ℕ} {p : MvPolynomial ι R} (hp : p.IsWeightedHomogeneous w d) :
    Bound w d p := fun a ha ↦ (hp ha).le

theorem component_zero_of_strict {d : ℕ} {p : MvPolynomial ι R} (hp : StrictBound w d p) :
    weightedHomogeneousComponent w d p = 0 := by
  ext a
  rw [coeff_weightedHomogeneousComponent,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  split_ifs with ha
  · by_contra hc
    have hh := hp a hc
    omega
  · rfl

theorem strict_of_bound_component_zero {d : ℕ} {p : MvPolynomial ι R}
    (hp : Bound w d p) (hz : weightedHomogeneousComponent w d p = 0) :
    StrictBound w d p := by
  intro a ha
  have hle := hp a ha
  have hne : Finsupp.weight w a ≠ d := by
    intro he
    have h := congrArg (fun q : MvPolynomial ι R ↦ q.coeff a) hz
    simp only [coeff_weightedHomogeneousComponent,he,if_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at h
    exact ha h
  omega

theorem subtract_component_strict {d : ℕ} {p : MvPolynomial ι R} (hp : Bound w d p) :
    StrictBound w d (p - weightedHomogeneousComponent w d p) := by
  apply strict_of_bound_component_zero w (bound_sub w hp (bound_component w d p))
  rw [map_sub,weightedHomogeneousComponent_eq_self
    (weightedHomogeneousComponent_isWeightedHomogeneous d p),sub_self]

/-- The highest possible component of a product is the product of the
corresponding components. The coefficient proof needs no domain assumption. -/
theorem component_mul_top {a b : ℕ} {p q : MvPolynomial ι R}
    (hp : Bound w a p) (hq : Bound w b q) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent,coeff_mul,coeff_mul]
  by_cases he : Finsupp.weight w e = a + b
  · rw [if_pos he]
    apply Finset.sum_congr rfl
    intro uv huv
    have hsum := Finset.mem_antidiagonal.mp huv
    have hw : Finsupp.weight w uv.1 + Finsupp.weight w uv.2 = a + b := by
      rw [← map_add,hsum,he]
    by_cases hp0 : p.coeff uv.1 = 0
    · simp [coeff_weightedHomogeneousComponent,hp0]
    by_cases hq0 : q.coeff uv.2 = 0
    · simp [coeff_weightedHomogeneousComponent,hq0]
    have ha := hp uv.1 hp0
    have hb := hq uv.2 hq0
    have hea : Finsupp.weight w uv.1 = a := by omega
    have heb : Finsupp.weight w uv.2 = b := by omega
    simp only [coeff_weightedHomogeneousComponent,hea,heb,if_true]
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro uv huv
    have hsum := Finset.mem_antidiagonal.mp huv
    by_cases ha : Finsupp.weight w uv.1 = a
    · have hb : Finsupp.weight w uv.2 ≠ b := by
        intro hb
        apply he
        rw [← hsum,map_add,ha,hb]
      simp only [coeff_weightedHomogeneousComponent,ha,if_true,if_neg hb,mul_zero]
    · simp only [coeff_weightedHomogeneousComponent,if_neg ha,zero_mul]

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
theorem component_mul_homogeneous {d : ℕ} {q : MvPolynomial ι R}
    (hq : q.IsWeightedHomogeneous w d) (p : MvPolynomial ι R) (D : ℕ) :
    weightedHomogeneousComponent w D (p * q) =
      if d ≤ D then weightedHomogeneousComponent w (D - d) p * q else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (weightedHomogeneousSubmodule R w) D (a := p) hq
  have key (a : MvPolynomial ι R) (j : ℕ) :
      (DirectSum.decompose (weightedHomogeneousSubmodule R w) a j : MvPolynomial ι R) =
        weightedHomogeneousComponent w j a :=
    weightedDecomposition.decompose'_apply R w a j
  simpa only [key] using h

def shiftedProjection (s D : ℕ) : MvPolynomial ι R →ₗ[R] MvPolynomial ι R :=
  if s ≤ D then weightedHomogeneousComponent w (D - s) else 0

theorem shiftedProjection_mul {q : MvPolynomial ι R} {d : ℕ}
    (hq : q.IsWeightedHomogeneous w d) (s D : ℕ) (p : MvPolynomial ι R) :
    shiftedProjection w s D (p * q) = shiftedProjection w (s + d) D p * q := by
  by_cases hs : s ≤ D
  · rw [shiftedProjection,if_pos hs,component_mul_homogeneous w hq]
    by_cases hd : d ≤ D - s
    · have hsd : s + d ≤ D := by omega
      simp only [if_pos hd,shiftedProjection,if_pos hsd,Nat.sub_sub]
    · have hsd : ¬s + d ≤ D := by omega
      simp only [if_neg hd,shiftedProjection,if_neg hsd,LinearMap.zero_apply,zero_mul]
  · have hsd : ¬s + d ≤ D := by omega
    simp only [shiftedProjection,if_neg hs,if_neg hsd,LinearMap.zero_apply,zero_mul]

theorem shiftedProjection_idempotent (s D : ℕ) (p : MvPolynomial ι R) :
    shiftedProjection w s D (shiftedProjection w s D p) = shiftedProjection w s D p := by
  unfold shiftedProjection
  split_ifs
  · exact weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  · simp only [LinearMap.zero_apply]

theorem shiftedProjection_homogeneous (s D : ℕ) (p : MvPolynomial ι R) :
    (shiftedProjection w s D p).IsWeightedHomogeneous w (D - s) := by
  unfold shiftedProjection
  split_ifs
  · exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem shiftedProjection_eq_zero_of_lt (s D : ℕ) (h : D < s) (p : MvPolynomial ι R) :
    shiftedProjection w s D p = 0 := by
  simp only [shiftedProjection,if_neg (Nat.not_le.mpr h),LinearMap.zero_apply]

/-- Every homogeneous first relation has a homogeneous alternating-matrix
preimage, with all low-degree zero cases included. -/
theorem homogeneous_first_syzygy {m : ℕ}
    (g : Fin m → MvPolynomial ι R) (degree : Fin m → ℕ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w (degree i))
    (hreg : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial ι R) (List.ofFn g))
    (D : ℕ) (a : Fin m → MvPolynomial ι R)
    (ha : ∀ i, shiftedProjection w (degree i) D (a i) = a i)
    (hz : KoszulSyzygies.coefficient g a = 0) :
    ∃ B : Fin m → Fin m → MvPolynomial ι R,
      (∀ i j, shiftedProjection w (degree i + degree j) D (B i j) = B i j) ∧
      KoszulSyzygies.boundary g B = a := by
  have hm : a ∈ LinearMap.range (KoszulSyzygies.boundary g) := by
    rw [← KoszulSyzygies.kernel_eq_boundary_range g hreg]
    exact hz
  obtain ⟨A,hA⟩ := hm
  let B := fun i j ↦ shiftedProjection w (degree i + degree j) D (A i j)
  refine ⟨B,fun i j ↦ shiftedProjection_idempotent w _ _ _,?_⟩
  funext i
  calc
    KoszulSyzygies.boundary g B i =
        shiftedProjection w (degree i) D (KoszulSyzygies.boundary g A i) := by
      simp only [KoszulSyzygies.boundary_apply,map_sum,map_sub]
      apply Finset.sum_congr rfl
      intro j hj
      conv_rhs => rw [mul_comm (g j),shiftedProjection_mul w (hg j),map_sub]
      simp only [B,Nat.add_comm (degree j) (degree i),mul_comm]
    _ = shiftedProjection w (degree i) D (a i) := by rw [hA]
    _ = a i := ha i

end PaperVerification.Fermion.Filtered
end
end
end TAF_LiteralSource_0303

section TAF_LiteralSource_0304
/- Original module: PaperVerification.WeightedInitialPrime -/


/-!
# Primality descends from an actual weighted initial ideal

Every nonzero original quotient class admits a bounded representative whose
highest bounded component survives in the actual initial quotient.  The proof
repeatedly subtracts a bounded original relation supplied by the established
Rees-kernel lifting theorem, decreasing a natural-number bound.  The top
component of a product is the product of the top components.  Consequently a
prime actual initial ideal forces the original ideal itself to be prime.

The final general lemma states saturation in its ordinary ideal-power form.
It rules out irrelevant-supported torsion when applied to a homogeneous prime
ideal which does not contain the irrelevant ideal.  No primality or saturation
of the original ideal is assumed in the weighted theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.WeightedInitialFiber

open MvPolynomial
open scoped BigOperators

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- Lift an initial component as an actual bounded original relation. -/
theorem top_component_lift (Q : Ideal P) (w : σ → ℕ)
    (p : P) (d : ℕ)
    (hp : weightedHomogeneousComponent w d p∈initialIdeal Q w) :
    ∃ a∈Q,WeightBound w d a ∧
      weightedHomogeneousComponent w d a=weightedHomogeneousComponent w d p := by
  obtain ⟨a,ha,hb,ht⟩ := initial_component_lift Q w
    (weightedHomogeneousComponent w d p) hp d
  refine ⟨a,ha,hb,?_⟩
  simpa only [weightedHomogeneousComponent_eq_self
    (weightedHomogeneousComponent_isWeightedHomogeneous d p)] using ht

/-- Natural-number descent gives a genuine representative with surviving top
component for every nonzero original quotient class. -/
theorem bounded_representative_top_not_mem_initialIdeal
    (Q : Ideal P) (w : σ → ℕ) (d : ℕ) (p : P)
    (hp : WeightBound w d p) (hne : p∉Q) :
    ∃ (e : ℕ) (r : P), e≤d ∧ r-p∈Q ∧ WeightBound w e r ∧
      weightedHomogeneousComponent w e r∉initialIdeal Q w := by
  classical
  induction d generalizing p with
  | zero =>
      refine ⟨0,p,le_rfl,?_,hp,?_⟩
      · simpa only [sub_self] using Q.zero_mem
      · intro ht
        obtain ⟨a,ha,hb,he⟩ := top_component_lift Q w p 0 ht
        have hp0 : weightedHomogeneousComponent w 0 p=p := by
          simpa only [Nat.zero_add,Finset.sum_range_one] using
            sum_components_of_bound w p 0 hp
        have ha0 : weightedHomogeneousComponent w 0 a=a := by
          simpa only [Nat.zero_add,Finset.sum_range_one] using
            sum_components_of_bound w a 0 hb
        have hap : a=p := by simpa only [ha0,hp0] using he
        exact hne (hap ▸ ha)
  | succ d ih =>
      by_cases ht : weightedHomogeneousComponent w (d+1) p∈initialIdeal Q w
      · obtain ⟨a,ha,hb,he⟩ := top_component_lift Q w p (d+1) ht
        have hsub : Fermion.Filtered.Bound w (d+1) (p-a) :=
          Fermion.Filtered.bound_sub w hp hb
        have htop : weightedHomogeneousComponent w (d+1) (p-a)=0 := by
          rw [map_sub,he,sub_self]
        have hs := Fermion.Filtered.strict_of_bound_component_zero w hsub htop
        have hb' : WeightBound w d (p-a) := by
          intro m hm
          exact Nat.lt_succ_iff.mp (hs m hm)
        have hne' : p-a∉Q := by
          intro h
          exact hne (by simpa only [sub_add_cancel] using Q.add_mem h ha)
        obtain ⟨e,r,hed,hr,hrb,hrt⟩ := ih (p-a) hb' hne'
        refine ⟨e,r,hed.trans (Nat.le_succ d),?_,hrb,hrt⟩
        convert Q.sub_mem hr ha using 1 <;> ring
      · exact ⟨d+1,p,le_rfl,by simpa only [sub_self] using Q.zero_mem,hp,ht⟩

/-- A prime conventional weighted initial ideal makes the original ideal
prime, for arbitrary nonnegative weights and any variable type. -/
theorem isPrime_of_initialIdeal_isPrime (Q : Ideal P) (w : σ → ℕ)
    (hprime : (initialIdeal Q w).IsPrime) : Q.IsPrime := by
  classical
  refine ⟨?_,?_⟩
  · intro hQ
    have h1 : (1 : P)∈Q := by rw [hQ]; trivial
    have hb : WeightBound w 0 (1 : P) :=
      fun m hm ↦ (isWeightedHomogeneous_one K w hm).le
    have ht := component_mem_initialIdeal Q w 1 h1 0 hb
    rw [weightedHomogeneousComponent_eq_self (isWeightedHomogeneous_one K w)] at ht
    exact hprime.one_notMem ht
  · intro p q hpq
    by_cases hp : p∈Q
    · exact Or.inl hp
    by_cases hq : q∈Q
    · exact Or.inr hq
    obtain ⟨a,r,ha,hr,hrb,hrt⟩ := bounded_representative_top_not_mem_initialIdeal
      Q w (weightedTotalDegree w p) p (weightBound_total w p) hp
    obtain ⟨b,s,hb,hs,hsb,hst⟩ := bounded_representative_top_not_mem_initialIdeal
      Q w (weightedTotalDegree w q) q (weightBound_total w q) hq
    have hrs : r*s∈Q := by
      convert Q.add_mem (Q.add_mem (Q.mul_mem_right s hr) (Q.mul_mem_left p hs)) hpq
        using 1 <;> ring
    have hmul := component_mem_initialIdeal Q w (r*s) hrs (a+b)
      (Fermion.Filtered.bound_mul w hrb hsb)
    rw [Fermion.Filtered.component_mul_top w hrb hsb] at hmul
    exact False.elim ((hprime.mul_notMem hrt hst) hmul)

section Saturation

variable {R : Type*} [CommRing R]

/-- The ordinary saturation condition `Q : J^∞ = Q`, stated with ideal powers
so that no auxiliary saturation convention or finiteness premise is hidden. -/
def IsSaturatedWithRespectTo (Q J : Ideal R) : Prop :=
  ∀ f : R, (∃ m : ℕ, ∀ g∈J^m,g*f∈Q) ↔ f∈Q

/-- A prime ideal not containing J is saturated with respect to J. -/
theorem isSaturatedWithRespectTo_of_isPrime (Q J : Ideal R)
    (hprime : Q.IsPrime) (hJ : ¬J≤Q) : IsSaturatedWithRespectTo Q J := by
  classical
  have hex : ∃ x : R,x∈J ∧ x∉Q := by
    by_contra h
    apply hJ
    intro x hx
    by_contra hxQ
    exact h ⟨x,hx,hxQ⟩
  obtain ⟨x,hx,hxQ⟩ := hex
  intro f
  constructor
  · rintro ⟨m,hm⟩
    have hp := hm (x^m) (Ideal.pow_mem_pow hx m)
    rcases hprime.mem_or_mem hp with hpow | hf
    · exact False.elim (hxQ (hprime.mem_of_pow_mem m hpow))
    · exact hf
  · intro hf
    exact ⟨0,fun g _ ↦ Q.mul_mem_left g hf⟩

end Saturation
end PaperVerification.WeightedInitialFiber
end
end
end TAF_LiteralSource_0304

section TAF_LiteralSource_0305
/- Original module: PaperVerification.AlternatingFormsOddPrime -/


/-!
# Primality of the actual odd common-isotropic Plücker ideal

The initial ideal is the actual prime Richardson ideal.  General weighted
descent therefore proves primality of the original ideal itself.  A concrete
lower-interval coordinate survives: its class is an actual degree-one standard
basis vector.  Thus the irrelevant ideal is not contained in the isotropy
ideal, which is the needed input to its projective saturation statement.

The chart isomorphisms by themselves would not exclude homogeneous torsion
supported at the irrelevant ideal.  This file supplies the missing global
algebraic input, without assuming primality or a projective coordinate-ring
identification as an application hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K] [CharZero K]

def oddLowerPluckerIndex (k s : ℕ) (hs : s≤k+1) : PluckerIndex s (2*k+1) :=
  ⟨oddIntervalLower k s hs,oddIntervalLower_strictMono k s hs⟩

def oddLowerChain (k s : ℕ) (hs : s≤k+1) :
    BandChain (oddIntervalLower k s hs) (oddIntervalUpper k s hs) 1 :=
  ⟨fun _ ↦ oddIntervalLower k s hs,
    (fun _ ↦ oddIntervalLower_strictMono k s hs),
    (fun _ i ↦ ⟨le_rfl,oddIntervalLower_le_upper k s hs i⟩),monotone_const⟩

theorem odd_lowerCoordinate_not_mem (k t : ℕ) (hs : t+2≤k+1) :
    X (oddLowerPluckerIndex k (t+2) hs)∉
      isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k) := by
  intro hmem
  have hne := (oddPluckerDegreeBasis (K := K) k t hs 1).ne_zero
    (oddLowerChain k (t+2) hs)
  apply hne
  apply Subtype.ext
  rw [oddPluckerDegreeBasis_apply]
  change Ideal.Quotient.mk _
    (chainPluckerProduct _ _ (oddLowerChain k (t+2) hs))=0
  simpa only [chainPluckerProduct,Fin.prod_univ_one,oddLowerChain,
    oddLowerPluckerIndex] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- Primality is proved for the literal original isotropy ideal. -/
theorem odd_isotropicPluckerIdeal_isPrime (k t : ℕ) (hs : t+2≤k+1) :
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime := by
  apply isPrime_of_initialIdeal_isPrime _ (pluckerVertexWeight (oddNatVertexWeight k))
  rw [odd_isotropic_initial_eq_interval k t hs]
  exact intervalPluckerIdeal_isPrime
    (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)
    (oddIntervalLower_strictMono k (t+2) hs).monotone
    (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)

/-- The actual irrelevant ideal in the displayed Plücker polynomial ring. -/
def pluckerIrrelevantIdeal (s n : ℕ) : Ideal (MvPolynomial (PluckerIndex s n) K) :=
  Ideal.span (Set.range (X : PluckerIndex s n → MvPolynomial (PluckerIndex s n) K))

theorem odd_irrelevant_not_le (k t : ℕ) (hs : t+2≤k+1) :
    ¬pluckerIrrelevantIdeal (K := K) (t+2) (2*k+1)≤
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k) := by
  intro h
  exact odd_lowerCoordinate_not_mem k t hs
    (h (Ideal.subset_span ⟨oddLowerPluckerIndex k (t+2) hs,rfl⟩))

theorem onePlane_ideal_isPrime (n : ℕ) :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsPrime :=
  RingHom.ker_isPrime _

theorem onePlane_irrelevant_not_le (k : ℕ) :
    ¬pluckerIrrelevantIdeal (K := K) 1 (2*k+1)≤matrixPluckerIdeal := by
  intro h
  have hx := h (Ideal.subset_span
    ⟨onePlaneIndex (0 : Fin (2*k+1)),rfl⟩)
  rw [onePlane_matrixPluckerIdeal] at hx
  exact X_ne_zero (onePlaneIndex (0 : Fin (2*k+1))) (Ideal.mem_bot.mp hx)

/-- The exact original homogeneous ideal is saturated against the full
irrelevant ideal, so its projective coordinate ring has no omitted torsion. -/
theorem odd_isotropicPluckerIdeal_saturated (k t : ℕ) (hs : t+2≤k+1) :
    IsSaturatedWithRespectTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
      (pluckerIrrelevantIdeal (t+2) (2*k+1)) :=
  isSaturatedWithRespectTo_of_isPrime _ _
    (odd_isotropicPluckerIdeal_isPrime k t hs) (odd_irrelevant_not_le k t hs)

theorem onePlane_PluckerIdeal_saturated (k : ℕ) :
    IsSaturatedWithRespectTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerIrrelevantIdeal 1 (2*k+1)) :=
  isSaturatedWithRespectTo_of_isPrime _ _
    (onePlane_ideal_isPrime (2*k+1)) (onePlane_irrelevant_not_le k)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0305

section TAF_LiteralSource_0306
/- Original module: PaperVerification.AlternatingFormsOddIndexCorrespondence -/


/-!
# The printed one-based inequalities in every exterior degree

The formal basis uses zero-based finite indices and moves the upper
inequality across subtraction.  This lemma proves its equivalence to the
printed inequalities over the integers.  In particular, no truncated natural
subtraction can create extra good indices above the middle degree.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

theorem goodOddIndex_printed_inequalities (k s : ℕ)
    (I : PluckerIndex s (2*k+1)) :
    (∀ i,2*i.val≤(I.val i).val ∧
      (I.val i).val+2*s≤2*k+2+2*i.val) ↔
    (∀ i : Fin s,
      2*((i.val : ℤ)+1)-1≤((I.val i).val : ℤ)+1 ∧
      ((I.val i).val : ℤ)+1≤
        (2*(k : ℤ)+1)-2*(s : ℤ)+2*((i.val : ℤ)+1)) := by
  constructor
  · intro h i
    have hi := h i
    constructor <;> omega
  · intro h i
    have hi := h i
    constructor <;> omega

theorem goodOddIndex_printed_bounds (k s : ℕ) (I : GoodOddIndex k s) :
    ∀ i : Fin s,
      2*((i.val : ℤ)+1)-1≤((I.val.val i).val : ℤ)+1 ∧
      ((I.val.val i).val : ℤ)+1≤
        (2*(k : ℤ)+1)-2*(s : ℤ)+2*((i.val : ℤ)+1) :=
  (goodOddIndex_printed_inequalities k s I.val).mp I.property

end PaperVerification.AlternatingForms
end
end TAF_LiteralSource_0306

section TAF_LiteralSource_0307
/- Original module: PaperVerification.AlternatingFormsOddPrincipal -/


/-!
# The full all-degree and all-plane statement of Theorem 1.3

The exterior-basis clause includes every degree, including degrees zero and
one and the vanishing range.  The geometric and algebraic clauses include
every `1 ≤ s ≤ k+1`.  The one-plane case is the actual polynomial Plücker
ring; the remaining cases use `s=t+2`, with no restriction on `t`.

The word Koszul has its standard homological meaning here: the actual
ordinary Tor of the augmentation residue is concentrated in internal degree
equal to homological degree.  The residue is proved isomorphic to the
coefficient field, and the internal pieces come from the original polynomial
grading.  Connectedness, degree compatibility, and exhaustion are included
explicitly below.  No separately constructed minimal linear resolution is
claimed.  The coordinate-chart equivalence retains the actual isotropy ideal
and its scheme structure.  Primality and irrelevant-ideal saturation exclude
any hidden homogeneous torsion.  The two flat families are the actual weighted Rees
images, with all nonzero fibers identified.

This assembly is a proof candidate until its complete source closure and
actual theorem bodies have passed the compiler and independent audit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

open MvPolynomial
open PaperVerification.WeightedInitialFiber

universe u v
variable {K : Type u} [Field K] [CharZero K]

/-- Flatness and the exact special and nonzero fibers of the literal weighted
Rees image.  Both endpoint rings retain their displayed polynomial ideals. -/
def WeightedFlatDegeneration {σ τ : Type*}
    (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ)
    (J : Ideal (MvPolynomial τ K)) : Prop :=
  Module.Flat (Polynomial K) (reesAlgebra Q w) ∧
  Nonempty (ZeroFiber Q w ≃ₐ[K] (MvPolynomial τ K⧸J)) ∧
  ∀ c : K,c≠0 → Nonempty (ParameterFiber Q w c ≃ₐ[K] (MvPolynomial σ K⧸Q))

/-- The usual finite homogeneous-quadratic Gröbner property of the literal
kernel in the displayed coordinate variables. -/
def HasQuadraticGroebnerBasis {σ : Type v} (Q : Ideal (MvPolynomial σ K)) : Prop :=
  ∃ (m : MonomialOrder.{v,v} σ) (S : Set (MvPolynomial σ K)),
    S.Finite ∧ (∀ p∈S,p.IsHomogeneous 2) ∧ m.IsGroebnerBasis S Q

/-- For one-planes every coordinate lies in the printed interval `[0,2k]`.
Thus the Richardson ideal is exactly the original one-plane Plücker ideal. -/
theorem onePlane_odd_intervalIdeal (k : ℕ) (hs : 1≤k+1) :
    intervalPluckerIdeal (K := K) (oddIntervalLower k 1 hs)
      (oddIntervalUpper k 1 hs)=matrixPluckerIdeal := by
  have hspan : Ideal.span
      {p | ∃ I : PluckerIndex 1 (2*k+1),
        (¬∀ i,oddIntervalLower k 1 hs i≤I.val i ∧
          I.val i≤oddIntervalUpper k 1 hs i) ∧ p=X I}=
      (⊥ : Ideal (MvPolynomial (PluckerIndex 1 (2*k+1)) K)) := by
    apply le_antisymm ?_ bot_le
    apply Ideal.span_le.mpr
    rintro p ⟨I,hI,hp⟩
    exact False.elim (hI (by
      intro i
      have hi : i.val=0 := by omega
      constructor
      · change 2*i.val≤(I.val i).val
        omega
      · change (I.val i).val≤2*(k+1-1+i.val)
        have hlt := (I.val i).isLt
        omega))
  rw [intervalPluckerIdeal,hspan,sup_bot_eq]

theorem onePlane_odd_richardson_flat (k : ℕ) (hs : 1≤k+1) :
    WeightedFlatDegeneration
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k 1 hs) (oddIntervalUpper k 1 hs)) := by
  rw [onePlane_odd_intervalIdeal]
  exact onePlane_flat_family _

def onePlaneCoefficientAugmentation (n : ℕ) :
    OnePlaneKoszul.Ring K n →ₐ[K] K :=
  (aeval (fun _ : Fin n ↦ (0 : K))).comp
    (OnePlaneKoszul.polynomialEquiv K n).toAlgHom

set_option synthInstance.maxHeartbeats 80000 in
/-- All clauses for the one-plane boundary.  In particular, the empty
quadratic Gröbner basis is a basis of a proved zero kernel, and the Tor
grading is linked to the original homogeneous coordinates and differential. -/
structure OddOnePlaneConclusions (k : ℕ) : Prop where
  prime : (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)).IsPrime
  saturated : IsSaturatedWithRespectTo
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerIrrelevantIdeal 1 (2*k+1))
  richardson : WeightedFlatDegeneration
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
  hibi : WeightedFlatDegeneration
    (Hibi.goodBandIdeal (K := K) (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (Hibi.diagonalWeight (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (Hibi.relationIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
  hibi_original_fibers : ∀ c : K,c≠0 → Nonempty
    (ParameterFiber
      (Hibi.goodBandIdeal (K := K) (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))
      (Hibi.diagonalWeight (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega))) c ≃ₐ[K]
      (MvPolynomial (PluckerIndex 1 (2*k+1)) K⧸
        intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
          (oddIntervalUpper k 1 (by omega))))
  quadratic : HasQuadraticGroebnerBasis
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
  connected : HomogeneousIdealPieces.piece
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1)) 0=
      (1 : Submodule K (OnePlaneKoszul.Ring K (2*k+1)))
  scalars : Function.Injective (algebraMap K (OnePlaneKoszul.Ring K (2*k+1)))
  grading : Nonempty {G : TauCeti.InternalGrading K (OnePlaneKoszul.Ring K (2*k+1)) ℕ //
    ∀ N,G.piece N=OnePlaneKoszul.originalDegree K (2*k+1) N}
  degree_mul : ∀ i j (x y : OnePlaneKoszul.Ring K (2*k+1)),
    x∈OnePlaneKoszul.originalDegree K (2*k+1) i →
    y∈OnePlaneKoszul.originalDegree K (2*k+1) j →
    x*y∈OnePlaneKoszul.originalDegree K (2*k+1) (i+j)
  residue_field : Nonempty (OnePlaneKoszul.Residue K (2*k+1) ≃ₐ[K] K)
  original_degree : ∀ N,
    BasisDegree.piece (OnePlaneKoszul.coordinateBasis K (2*k+1)) Finsupp.degree N=
      OnePlaneKoszul.originalDegree K (2*k+1) N
  differential_degree : ∀ r N (z : OnePlaneKoszul.freeTermOverK K (2*k+1) (r+1)),
    z∈(OnePlaneKoszul.freeGrading K (2*k+1) (r+1)).piece N →
      OnePlaneKoszul.differentialOverK K (2*k+1) r z∈
        (OnePlaneKoszul.freeGrading K (2*k+1) r).piece N
  koszul : ∀ r N,
    (OnePlaneKoszul.torGrading K (2*k+1) r).piece N=if N=r then ⊤ else ⊥

theorem odd_onePlane_conclusions (k : ℕ) : OddOnePlaneConclusions (K := K) k := by
  let hs : 1≤k+1 := by omega
  let α := oddIntervalLower k 1 hs
  let β := oddIntervalUpper k 1 hs
  refine ⟨onePlane_ideal_isPrime (2*k+1),onePlane_PluckerIdeal_saturated k,
    onePlane_odd_richardson_flat k hs,?_,?_,?_,
    homogeneousQuotient_degree_zero _,
    augmentedQuotient_scalar_injective _ (onePlaneCoefficientAugmentation (2*k+1)),
    ⟨⟨HomogeneousIdealPieces.grading _
      (OnePlaneKoszul.onePlaneIdeal_isHomogeneous K (2*k+1)),
      HomogeneousIdealPieces.grading_piece _ _⟩⟩,
    homogeneousQuotient_mul_mem _,⟨OnePlaneKoszul.residueEquivField K (2*k+1)⟩,
    OnePlaneKoszul.coefficientDegree_eq_originalDegree K (2*k+1),
    OnePlaneKoszul.differentialOverK_homogeneous K (2*k+1),
    OnePlaneKoszul.actual_onePlane_Tor_degree K (2*k+1)⟩
  · exact ⟨inferInstance,
      ⟨Hibi.hibiSpecialFiberEquiv α β
        (oddIntervalLower_strictMono k 1 hs).monotone
        (oddIntervalUpper_strictMono k 1 hs).monotone (by decide)⟩,
      fun c hc ↦ ⟨nonzeroFiberEquiv _ _ c hc⟩⟩
  · intro c hc
    exact ⟨Hibi.hibiNonzeroFiberEquiv α β
      (oddIntervalLower_strictMono k 1 hs).monotone
      (oddIntervalUpper_strictMono k 1 hs).monotone (by decide) c hc⟩
  · exact ⟨WeightedMonomialOrder.finiteBaseOrder (PluckerIndex 1 (2*k+1)),∅,
      onePlane_quadratic_groebner _⟩

/-- The remaining cases use the original common-isotropic ring and its
original good-coordinate presentation.  The chart clause identifies its
literal equations with row isotropy, rather than postulating a geometric
interpretation.  The Tor pieces are the images of the original homogeneous
bar subcomplexes inside ordinary Mathlib Tor. -/
structure OddHigherPlaneConclusions (k t : ℕ) (hs : t+2≤k+1) : Prop where
  prime : (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k)).IsPrime
  saturated : IsSaturatedWithRespectTo
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (pluckerIrrelevantIdeal (t+2) (2*k+1))
  charts : ∀ p : PluckerIndex (t+2) (2*k+1),Nonempty
    ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      (isotropicPluckerIdeal (t := t) (oddPluckerForms k) ⊔ Ideal.span {X p-1})) ≃ₐ[K]
      (MvPolynomial (PluckerChartVariable p) K⧸
        isotropicChartIdeal p (oddPluckerForms k)))
  richardson : WeightedFlatDegeneration
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms k))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))
  hibi : WeightedFlatDegeneration
    (Hibi.goodBandIdeal (K := K) (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs))
    (Hibi.diagonalWeight (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))
    (Hibi.relationIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs))
  hibi_original_fibers : ∀ c : K,c≠0 → Nonempty
    (ParameterFiber
      (Hibi.goodBandIdeal (K := K) (oddIntervalLower k (t+2) hs)
        (oddIntervalUpper k (t+2) hs))
      (Hibi.diagonalWeight (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) c ≃ₐ[K]
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        intervalPluckerIdeal (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)))
  good_coordinates : Nonempty
    ((MvPolynomial
      (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs) (oddIntervalUpper k (t+2) hs)) K⧸
      oddGoodIdeal k t hs) ≃ₐ[K]
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
  quadratic : HasQuadraticGroebnerBasis (oddGoodIdeal (K := K) k t hs)
  connected : oddPluckerDegree (K := K) k t 0=
    (1 : Submodule K (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
  scalars : Function.Injective (algebraMap K
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms k)))
  grading : Nonempty {G : TauCeti.InternalGrading K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms k)) ℕ //
    ∀ N,G.piece N=oddPluckerDegree (K := K) k t N}
  degree_mul : ∀ i j (x y : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms k)),
    x∈oddPluckerDegree k t i → y∈oddPluckerDegree k t j →
      x*y∈oddPluckerDegree k t (i+j)
  residue_field : Nonempty (BarFree.Residue (oddAugmentation (K := K) k t) ≃ₐ[K] K)
  tor_exhaustive : ∀ r,(⨆ N,oddTorInternalPiece (K := K) k t hs r N)=⊤
  koszul : ∀ r N,oddTorInternalPiece (K := K) k t hs r N=if N=r then ⊤ else ⊥

theorem odd_higherPlane_conclusions (k t : ℕ) (hs : t+2≤k+1) :
    OddHigherPlaneConclusions (K := K) k t hs := by
  let α := oddIntervalLower k (t+2) hs
  let β := oddIntervalUpper k (t+2) hs
  refine ⟨odd_isotropicPluckerIdeal_isPrime k t hs,
    odd_isotropicPluckerIdeal_saturated k t hs,
    fun p ↦ ⟨isotropicPluckerBigCellEquiv p (oddPluckerForms k)⟩,
    odd_richardson_flat_family k t hs,?_,?_,⟨oddGoodQuotientEquiv k t hs⟩,?_,
    homogeneousQuotient_degree_zero _,
    augmentedQuotient_scalar_injective _ (oddAugmentation k t),
    ⟨⟨HomogeneousIdealPieces.grading _ (isotropicPluckerIdeal_isHomogeneous _),
      HomogeneousIdealPieces.grading_piece _ _⟩⟩,
    homogeneousQuotient_mul_mem _,⟨BarFree.residueEquivCoefficients (oddAugmentation k t)⟩,
    oddTorInternalPieces_iSup k t hs,odd_actual_Tor_internal_degree k t hs⟩
  · exact ⟨inferInstance,
      ⟨Hibi.hibiSpecialFiberEquiv α β
        (oddIntervalLower_strictMono k (t+2) hs).monotone
        (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega)⟩,
      fun c hc ↦ ⟨nonzeroFiberEquiv _ _ c hc⟩⟩
  · intro c hc
    exact ⟨Hibi.hibiNonzeroFiberEquiv α β
      (oddIntervalLower_strictMono k (t+2) hs).monotone
      (oddIntervalUpper_strictMono k (t+2) hs).monotone (by omega) c hc⟩
  · obtain ⟨m,hm⟩ := odd_good_exists_quadratic_groebner (K := K) k t hs
    exact ⟨m,oddQuadraticSet k t hs,hm⟩

/-- A literal case split on the requested plane dimension.  Degree zero
is outside the geometric clause; the theorem below assumes `0<s` and hence
never proves that branch.  Every positive dimension occurs in exactly one
of the actual one-plane or higher-plane statements above. -/
def OddPluckerConclusions (k s : ℕ) (hs : s≤k+1) : Prop :=
  match s,hs with
  | 0,_ => False
  | 1,_ => OddOnePlaneConclusions (K := K) k
  | t+2,h => OddHigherPlaneConclusions (K := K) k t h

theorem odd_all_positive_plane_conclusions (k s : ℕ)
    (hpos : 0<s) (hs : s≤k+1) : OddPluckerConclusions (K := K) k s hs := by
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ s =>
    cases s with
    | zero => exact odd_onePlane_conclusions k
    | succ t => exact odd_higherPlane_conclusions k t hs

/-- All clauses of Theorem 1.3 for the canonical odd pencil, over every
characteristic-zero field, every odd dimension `2*k+1`, every exterior degree,
and the complete positive range `1≤s≤k+1` for the two degenerations, quadratic
Gröbner presentation and homological Koszul assertion. -/
theorem paper_theorem_1_3 (k : ℕ) :
    (∀ s,∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2*k+1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0<s) (hs : s≤k+1),OddPluckerConclusions (K := K) k s hs) :=
  ⟨paper_theorem_1_3_exterior_basis k,odd_all_positive_plane_conclusions k⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0307

section TAF_LiteralSource_0308
/- Original module: TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Coefficients and lifts for homogeneous localizations

For a graded ring `A`, an element `f : A` and a ring homomorphism `φ : A →+* R` with `φ f` a unit,
`HomogeneousLocalization.Away.lift 𝒜 φ hf` is the ring homomorphism `A_{(f)} →+* R` sending
`a / fⁿ` to `φ a / (φ f)ⁿ`: the restriction to the degree-zero part `A_{(f)}` of the lift
`A_f →+* R` of `φ`. Geometrically, when `A` is `ℕ`-graded and `f` is homogeneous of positive
degree, `Spec A_{(f)}` is the standard affine chart `D₊(f)` of `Proj A`, and `Spec` of `lift` is
the morphism `Spec R ⟶ D₊(f) ⊆ Proj A` given by the "homogeneous coordinates" `φ`.

For a graded algebra over a coefficient ring, homogeneous localization inherits the
coefficient algebra structure, and fractions with a fixed homogeneous denominator depend
linearly on their numerator. This permits scalar extension of the homogeneous affine charts.

The file also records that the restriction map `A_{(f)} →+* A_{(fg)}` is injective when `g` is a
nonzerodivisor of `A`, and that a homogeneous localization is reduced whenever the corresponding
localization is.

## Main definitions

* `HomogeneousLocalization.Away.mkLinearMap`: the linear numerator map for a fixed denominator.
* `HomogeneousLocalization.Away.promoteNumerator`: raising a numerator to a larger power of the
  denominator.
* `HomogeneousLocalization.Away.lift`: the ring homomorphism `A_{(f)} →+* R` induced by `φ`.

## Main results

* `HomogeneousLocalization.Away.mkLinearMap_promoteNumerator`: raising numerator and denominator
  by the same power does not change a homogeneous fraction.

* `HomogeneousLocalization.Away.lift_mk`: `lift` sends `a / fⁿ` to `φ a * ((φ f)ⁿ)⁻¹`.
* `HomogeneousLocalization.Away.lift_algebraMap`: `lift` restricts to `φ` on the degree-zero
  part `𝒜 0`.
* `HomogeneousLocalization.Away.lift_comp_awayMap`: `lift` is compatible with the restriction
  `awayMap` from `A_{(f)}` to `A_{(fg)}`.
* `HomogeneousLocalization.Away.lift_comp_map`: `lift` is compatible with the map induced by a
  graded ring homomorphism.
* `HomogeneousLocalization.Away.map_surjective`: a surjective graded ring homomorphism induces
  surjections of homogeneous localizations at homogeneous elements.
* `HomogeneousLocalization.Away.map_surjective_of_grade_subset_range`: for `ℕ`-graded rings,
  surjectivity onto the elements of positive degree suffices at homogeneous elements of positive
  degree.
* `HomogeneousLocalization.Away.lift_eq_of_forall_mem`: rescaling the homogeneous coordinates,
  so that `ψ a = cⁿ φ a` on the degree-`n` part, does not change `lift`.
* `HomogeneousLocalization.awayMap_injective`: the restriction `awayMap` from `A_{(f)}` to
  `A_{(fg)}` is injective when `g` is a nonzerodivisor of `A`.
* `HomogeneousLocalization.awayMap_algebraMap`: the restriction `awayMap` respects the
  coefficients of a graded algebra.
* `HomogeneousLocalization.isReduced`: a homogeneous localization is reduced whenever the
  corresponding localization is, in particular for any reduced graded ring.

## Provenance

`HomogeneousLocalization.isReduced` is adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`,
Apache-2.0) at commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/ForMathlib/ProjIntegral.lean`, declaration
`AlgebraicGeometry.Proj.isReduced_away`, which treats `Away 𝒜 f` for an `ℕ`-graded domain; here
the localization is at any submonoid and only its reducedness is assumed.
-/

public section

namespace HomogeneousLocalization

variable {ι A B R σ τ : Type*} [CommRing A] [CommRing B] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B] [AddCommMonoid ι] [DecidableEq ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

variable (𝒜) in
/-- The ring homomorphism `A_{(f)} →+* R`, `a / fⁿ ↦ φ a / (φ f)ⁿ`, induced by a ring
homomorphism `φ : A →+* R` inverting `f`: the restriction of the lift `A_f →+* R` of `φ` to the
degree-zero part `A_{(f)}` of the localization. -/
noncomputable def Away.lift (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) : Away 𝒜 f →+* R :=
  (IsLocalization.Away.lift f hf).comp (algebraMap (Away 𝒜 f) (Localization.Away f))

private theorem Away.lift_apply (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) (z : Away 𝒜 f) :
    Away.lift 𝒜 φ hf z = IsLocalization.Away.lift f hf z.val :=
  (rfl)

/-- `Away.lift` sends `a / fⁿ` to `φ a / (φ f)ⁿ`. -/
@[simp]
theorem Away.lift_mk (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) {d : ι} (hfd : f ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    Away.lift 𝒜 φ hf (Away.mk 𝒜 hfd n a ha) = φ a * ↑(hf.unit ^ n)⁻¹ := by
  have hfn : φ (f ^ n) = ↑(hf.unit ^ n) := by
    rw [map_pow, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [Away.lift_apply, Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec, mul_left_comm, hfn, Units.mul_inv, mul_one]

/-- `Away.lift` restricts to `φ` on the degree-zero part `𝒜 0`. -/
@[simp]
theorem Away.lift_algebraMap (φ : A →+* R) {f : A} (hf : IsUnit (φ f)) (a : 𝒜 0) :
    Away.lift 𝒜 φ hf (algebraMap (𝒜 0) (Away 𝒜 f) a) = φ a := by
  rw [Away.lift_apply, ← algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝒜 0) A, IsLocalization.Away.lift_eq,
    SetLike.GradeZero.algebraMap_apply]

/-- Changing the value ring of homogeneous coordinates commutes with the chart lift. -/
@[simp]
theorem _root_.RingHom.comp_homogeneousLocalizationAwayLift {S : Type*} [CommRing S]
    (ψ : R →+* S) (φ : A →+* R)
    {f : A} (hf : IsUnit (φ f)) :
    ψ.comp (Away.lift 𝒜 φ hf) = Away.lift 𝒜 (ψ.comp φ) (hf.map ψ) := by
  unfold Away.lift
  rw [← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp [IsLocalization.Away.lift_eq]

/-- `Away.lift` is compatible with the restriction `awayMap : A_{(f)} →+* A_{(fg)}`. -/
theorem Away.lift_comp_awayMap (φ : A →+* R) {e : ι} {f g x : A} (hg : g ∈ 𝒜 e)
    (hx : x = f * g) (hφx : IsUnit (φ x)) (hφf : IsUnit (φ f)) :
    (Away.lift 𝒜 φ hφx).comp (awayMap 𝒜 hg hx) = Away.lift 𝒜 φ hφf := by
  ext z
  rw [RingHom.comp_apply, Away.lift_apply, Away.lift_apply, val_awayMap, ← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a ↦ ?_)
  simp [IsLocalization.Away.lift_eq]

/-- `Away.lift` is compatible with the map `A_{(s)} →+* B_{(F s)}` induced by a graded ring
homomorphism `F`. -/
@[simp]
theorem Away.lift_comp_map (φ : B →+* R) (F : 𝒜 →+*ᵍ ℬ) {s : A} (hs : IsUnit (φ (F s))) :
    (Away.lift ℬ φ hs).comp (Away.map F s) = Away.lift 𝒜 (φ.comp F.toRingHom) (f := s) hs := by
  ext z
  have hval : (Away.map F s z).val = Localization.awayMap F.toRingHom s z.val := by
    obtain ⟨c, rfl⟩ := mk_surjective z
    simp [Away.map, HomogeneousLocalization.map_mk, Localization.mk_eq_mk',
      IsLocalization.Away.map, IsLocalization.map_mk']
  rw [RingHom.comp_apply, Away.lift_apply, Away.lift_apply, hval, ← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
  simp [IsLocalization.Away.lift_eq, IsLocalization.Away.map]

/-- A surjective graded ring homomorphism `F` induces a surjection `A_{(s)} →+* B_{(F s)}` for
every homogeneous `s`: a fraction `b / F(s)ⁿ` with `b` of degree `n • d` is the image of
`a / sⁿ`, where `a` is the degree-`n • d` component of any preimage of `b`. -/
theorem Away.map_surjective {F : 𝒜 →+*ᵍ ℬ} (hF : Function.Surjective F) {s : A} {d : ι}
    (hs : s ∈ 𝒜 d) : Function.Surjective (Away.map F s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (Graded.map_mem F hs) z
  obtain ⟨a, rfl⟩ := hF b
  refine ⟨Away.mk 𝒜 hs n (DirectSum.decompose 𝒜 a (n • d)) (SetLike.coe_mem _), ?_⟩
  rw [Away.map_mk]
  congr 1
  rw [GradedRingHom.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ hb]

/-- A graded ring homomorphism `F` of `ℕ`-graded rings whose image contains every homogeneous
element of positive degree induces a surjection `A_{(s)} →+* B_{(F s)}` for every `s` homogeneous
of positive degree. The degree-zero part of `B` need not lie in the image: a fraction
`b / F(s)ⁿ` is also `b F(s) / F(s)ⁿ⁺¹`, whose numerator has positive degree. -/
theorem Away.map_surjective_of_grade_subset_range {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜]
    [GradedRing ℬ] {F : 𝒜 →+*ᵍ ℬ} (hF : ∀ i, 0 < i → (ℬ i : Set B) ⊆ Set.range F) {s : A}
    {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) : Function.Surjective (Away.map F s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (Graded.map_mem F hs) z
  have hb' : b * F s ∈ ℬ ((n + 1) • d) := by
    rw [succ_nsmul]
    exact SetLike.mul_mem_graded hb (Graded.map_mem F hs)
  obtain ⟨a, ha⟩ := hF _ (by rw [smul_eq_mul]; positivity) hb'
  -- `b / F(s)ⁿ = b F(s) / F(s)ⁿ⁺¹`
  have hz : Away.mk ℬ (Graded.map_mem F hs) n b hb =
      Away.mk ℬ (Graded.map_mem F hs) (n + 1) (b * F s) hb' := by
    apply val_injective
    rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, pow_succ]; ring⟩
  refine ⟨Away.mk 𝒜 hs (n + 1) (DirectSum.decompose 𝒜 a ((n + 1) • d)) (SetLike.coe_mem _), ?_⟩
  rw [hz, Away.map_mk]
  congr 1
  rw [GradedRingHom.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same ℬ hb']

/-- Rescaling homogeneous coordinates does not change `Away.lift`: if `ψ a = cⁿ φ a` for every
`a` of degree `n`, then `φ` and `ψ` induce the same homomorphism `A_{(f)} →+* R`. -/
theorem Away.lift_eq_of_forall_mem {𝒜 : ℕ → σ} [GradedRing 𝒜] (φ ψ : A →+* R) (c : Rˣ)
    (h : ∀ n, ∀ a ∈ 𝒜 n, ψ a = c ^ n * φ a) {f : A} {d : ℕ} (hfd : f ∈ 𝒜 d)
    (hψ : IsUnit (ψ f)) (hφ : IsUnit (φ f)) :
    Away.lift 𝒜 ψ hψ = Away.lift 𝒜 φ hφ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hfd z
  rw [Away.lift_mk, Away.lift_mk, Units.eq_mul_inv_iff_mul_eq, mul_assoc, mul_left_comm,
    Units.inv_mul_eq_iff_eq_mul]
  simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, h _ _ ha, h _ _ hfd, smul_eq_mul]
  ring

/-- The restriction `awayMap : A_{(f)} →+* A_{(fg)}`, `a / fⁿ ↦ a gⁿ / (fg)ⁿ`, is injective when
`g` is a nonzerodivisor of `A`. -/
theorem awayMap_injective {e : ι} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (h : g ∈ nonZeroDivisors A) : Function.Injective (awayMap 𝒜 hg hx) := by
  intro z w hzw
  rw [ext_iff_val, val_awayMap, val_awayMap] at hzw
  -- `awayMap` restricts `A_f →+* A_{fg}`, which is injective if it kills no nonzero `a / 1`
  refine val_injective _ <| IsLocalization.injective_of_map_algebraMap_zero (M := .powers f) _ _
    (fun a ha ↦ ?_) hzw
  -- the image of `a / 1` in `A_{fg}` vanishes, so `(fg)ᵏ a = 0` for some `k`
  rw [IsLocalization.Away.lift_eq] at ha
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x (ha.trans (map_zero _).symm)
  -- as `g` is a nonzerodivisor, `fᵏ a = 0`, so `a / 1` vanishes in `A_f`
  rw [mul_zero, hx, mul_pow, mul_right_comm,
    mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem h k)] at hk
  exact (IsLocalization.map_eq_zero_iff (.powers f) _ a).mpr
    ⟨⟨f ^ k, pow_mem (Submonoid.mem_powers f) k⟩, hk⟩

variable (𝒜) in
/-- A homogeneous localization at `x` is reduced whenever the localization at `x` is reduced; in
particular, it is reduced whenever the graded ring is. -/
instance isReduced (x : Submonoid A) [IsReduced (Localization x)] :
    IsReduced (HomogeneousLocalization 𝒜 x) :=
  isReduced_of_injective (algebraMap _ (Localization x)) (val_injective x)

/-- The homogeneous localization map is the restriction of the ordinary localization map. -/
@[simp]
theorem val_map {ι A B σ τ : Type*} [AddCommMonoid ι] [DecidableEq ι]
    [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ι → σ} {ℬ : ι → τ}
    [GradedRing 𝒜] [GradedRing ℬ] (g : 𝒜 →+*ᵍ ℬ)
    {P : Submonoid A} {Q : Submonoid B} (h : P ≤ Q.comap g)
    (z : HomogeneousLocalization 𝒜 P) :
    (map g h z).val = IsLocalization.map (Localization Q) g.toRingHom h z.val := by
  obtain ⟨c, rfl⟩ := mk_surjective z
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk']
  exact (IsLocalization.map_mk' (S := Localization P) (Q := Localization Q) (g := g.toRingHom)
    (M := P) (T := Q) h (c.num : A) ⟨c.den, c.den_mem⟩).symm

/-- The degree-zero coefficient map sends `a` to the ordinary fraction `a/1`. -/
@[simp]
theorem val_fromZeroRingHom {ι A σ : Type*} [AddCommMonoid ι] [DecidableEq ι]
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
    [GradedRing 𝒜] (P : Submonoid A) (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 P a).val = algebraMap A (Localization P) a :=
  Localization.mk_one_eq_algebraMap _

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (P : Submonoid A)

/-- Homogeneous localization of a graded algebra is an algebra over its coefficient ring. -/
instance algebra : Algebra R (HomogeneousLocalization 𝒜 P) where
  algebraMap := (fromZeroRingHom 𝒜 P).comp (algebraMap R (𝒜 0))
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    apply val_injective P
    simp only [val_smul, Algebra.smul_def, val_mul, RingHom.comp_apply,
      val_fromZeroRingHom, SetLike.GradeZero.coe_algebraMap]
    rw [← IsScalarTower.algebraMap_apply R A (Localization P)]

/-- The coefficient map is the composite through the degree-zero part. -/
theorem algebraMap_eq_comp :
    algebraMap R (HomogeneousLocalization 𝒜 P) =
      (fromZeroRingHom 𝒜 P).comp (algebraMap R (𝒜 0)) := (rfl)

/-- Forgetting homogeneity respects coefficients. -/
@[simp]
theorem val_algebraMap (r : R) :
    (algebraMap R (HomogeneousLocalization 𝒜 P) r).val =
      algebraMap R (Localization P) r := by
  rw [algebraMap_eq_comp, RingHom.comp_apply, val_fromZeroRingHom]
  simp only [SetLike.GradeZero.coe_algebraMap,
    ← IsScalarTower.algebraMap_apply R A (Localization P)]

/-- The coefficient action factors through homogeneous localization into ordinary localization. -/
instance isScalarTower :
    IsScalarTower R (HomogeneousLocalization 𝒜 P) (Localization P) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := HomogeneousLocalization 𝒜 P)
    (A := Localization P) (by
    ext r
    exact (val_algebraMap 𝒜 P r).symm)

variable {𝒜}

/-- The restriction `awayMap` from `A_{(f)}` to `A_{(fg)}` respects coefficients. -/
@[simp]
theorem awayMap_algebraMap {e : ι} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g) (r : R) :
    awayMap 𝒜 hg hx (algebraMap R (Away 𝒜 f) r) = algebraMap R (Away 𝒜 x) r := by
  simp only [algebraMap_eq_comp, RingHom.comp_apply, awayMap_fromZeroRingHom]

/-- Fractions with a fixed homogeneous denominator depend linearly on the numerator. -/
noncomputable def Away.mkLinearMap {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) :
    𝒜 (n • d) →ₗ[R] Away 𝒜 f where
  toFun a := Away.mk 𝒜 hf n a a.2
  map_add' a b := by
    apply val_injective
    simp only [Away.val_mk, val_add, Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' r a := by
    apply val_injective
    simp only [Away.val_mk, val_smul, Submodule.coe_smul]
    exact (Localization.smul_mk (S := Submonoid.powers f) r (a : A) _).symm

/-- The linear numerator map forms the homogeneous fraction with the chosen denominator. -/
@[simp]
theorem Away.mkLinearMap_apply {f : A} {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ)
    (a : 𝒜 (n • d)) : Away.mkLinearMap (𝒜 := 𝒜) hf n a = Away.mk 𝒜 hf n a a.2 := (rfl)

/-- Raise the denominator of a homogeneous fraction without changing the fraction. -/
def Away.promoteNumerator {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    (n N : ℕ) (hnN : n ≤ N) : 𝒜 (n • d) →ₗ[R] 𝒜 (N • d) where
  toFun a := ⟨(a : A) * f ^ (N - n), by
    have h := SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded (N - n) hf)
    convert h using 1
    rw [← add_nsmul, Nat.add_sub_of_le hnN]⟩
  map_add' a b := by
    apply Subtype.ext
    exact add_mul (a : A) b (f ^ (N - n))
  map_smul' r a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply, Algebra.smul_mul_assoc]

/-- Raising a numerator multiplies it by the added power of the denominator. -/
@[simp]
theorem Away.coe_promoteNumerator {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    (n N : ℕ) (hnN : n ≤ N) (a : 𝒜 (n • d)) :
    (Away.promoteNumerator hf n N hnN a : A) = a * f ^ (N - n) := (rfl)

/-- Raising a numerator and its denominator by the same power does not change a homogeneous
fraction. -/
theorem Away.mkLinearMap_promoteNumerator {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    (n N : ℕ) (hnN : n ≤ N) (a : 𝒜 (n • d)) :
    Away.mkLinearMap hf N (Away.promoteNumerator hf n N hnN a) =
      Away.mkLinearMap hf n a := by
  apply val_injective
  simp only [Away.mkLinearMap_apply, Away.val_mk, Away.coe_promoteNumerator]
  let b : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩
  let c : Submonoid.powers f := ⟨f ^ (N - n), ⟨N - n, rfl⟩⟩
  have hbc : b * c = ⟨f ^ N, ⟨N, rfl⟩⟩ := by
    apply Subtype.ext
    simp only [b, c, Submonoid.coe_mul, ← pow_add, Nat.add_sub_of_le hnN]
  rw [← hbc]
  have hcancel := IsLocalization.mk'_cancel
    (S := Localization (Submonoid.powers f)) (a : A) b c
  rw [← Localization.mk_eq_mk'_apply, ← Localization.mk_eq_mk'_apply] at hcancel
  convert hcancel using 1

end HomogeneousLocalization
end
end TAF_LiteralSource_0308

section TAF_LiteralSource_0309
/- Original module: PaperVerification.HomogeneousChartDehomogenization -/


/-!
# Degree-one dehomogenization of the actual Proj affine ring

For an arbitrary naturally graded commutative ring and a degree-one element f,
the actual degree-zero localization A_(f) is the literal quotient A/(f-1).
The construction sends a homogeneous fraction a/f^n to the class of a; its
inverse first normalizes every homogeneous component by its corresponding
power of f. Both inverses are proved. No domain, reducedness, or generation
in degree one is assumed.

This is the actual algebraic comparison needed to connect normalized
homogeneous charts to the affine basic opens of Proj. This source candidate
has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousChartDehomogenization

open DirectSum

universe u v
variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f : A} (hf : f ∈ 𝒜 1)

/-- The full normalization ideal, without taking its radical. -/
def normalizationIdeal (f : A) : Ideal A := Ideal.span ({f - 1} : Set A)

/-- The literal normalized quotient ring. -/
abbrev NormalizedRing (f : A) := A ⧸ normalizationIdeal f

/-- The canonical quotient map. -/
def quotientMap (f : A) : A →+* NormalizedRing f :=
  Ideal.Quotient.mk (normalizationIdeal f)

@[simp] theorem quotientMap_pivot (f : A) : quotientMap f f = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (quotientMap f), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem quotientMap_pivot_isUnit (f : A) : IsUnit (quotientMap f f) := by
  rw [quotientMap_pivot]
  exact isUnit_one

/-- A degree-n element normalized by the literal power f^n. -/
def fraction (n : ℕ) (a : 𝒜 n) : HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using a.property)

@[simp] theorem fraction_val (n : ℕ) (a : 𝒜 n) :
    (fraction 𝒜 hf n a).val =
      Localization.mk (a : A) (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := rfl

/-- For each fixed degree, normalization is genuinely additive. -/
def fractionAdd (n : ℕ) : 𝒜 n →+ HomogeneousLocalization.Away 𝒜 f where
  toFun := fraction 𝒜 hf n
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [fraction_val, ZeroMemClass.coe_zero,
      HomogeneousLocalization.val_zero, Localization.mk_zero]
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    simp only [fraction_val, HomogeneousLocalization.val_add, AddMemClass.coe_add]
    exact (Localization.add_mk_self _ _ _).symm

@[simp] theorem fractionAdd_apply (n : ℕ) (a : 𝒜 n) :
    fractionAdd 𝒜 hf n a = fraction 𝒜 hf n a := rfl

/-- The normalization maps preserve the actual graded unit. -/
theorem fractionAdd_one :
    fractionAdd 𝒜 hf 0
      (@GradedMonoid.GOne.one ℕ (fun n => ↥(𝒜 n)) _ _) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [fractionAdd_apply, fraction_val, SetLike.coe_gOne,
    HomogeneousLocalization.val_one, pow_zero]
  change Localization.mk (1 : A) (1 : Submonoid.powers f) = 1
  rw [Localization.mk_one_eq_algebraMap, map_one]

/-- The normalization maps preserve every actual graded product. -/
theorem fractionAdd_mul {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j) :
    fractionAdd 𝒜 hf (i + j)
      (@GradedMonoid.GMul.mul ℕ (fun n => ↥(𝒜 n)) _ _ i j a b) =
      fractionAdd 𝒜 hf i a * fractionAdd 𝒜 hf j b := by
  apply HomogeneousLocalization.val_injective
  simp only [fractionAdd_apply, HomogeneousLocalization.val_mul, fraction_val,
    SetLike.coe_gMul, Localization.mk_eq_mk']
  rw [← IsLocalization.mk'_mul]
  exact congrArg
    (IsLocalization.mk' (Localization.Away f) ((a : A) * (b : A)))
    (Subtype.ext (pow_add f i j))

/-- First extend the homogeneous normalization maps to the actual direct sum. -/
def componentNormalization :
    (⨁ n : ℕ, 𝒜 n) →+* HomogeneousLocalization.Away 𝒜 f :=
  DirectSum.toSemiring (fractionAdd 𝒜 hf)
    (fractionAdd_one 𝒜 hf) (fractionAdd_mul 𝒜 hf)

/-- Normalize all homogeneous components using the actual graded decomposition. -/
def normalize : A →+* HomogeneousLocalization.Away 𝒜 f :=
  (componentNormalization 𝒜 hf).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- On a homogeneous element, the full map is its literal homogeneous fraction. -/
theorem normalize_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    normalize 𝒜 hf a = fraction 𝒜 hf n ⟨a, ha⟩ := by
  change DirectSum.toAddMonoid (fractionAdd 𝒜 hf) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

@[simp] theorem normalize_pivot : normalize 𝒜 hf f = 1 := by
  rw [normalize_of_mem 𝒜 hf hf]
  apply HomogeneousLocalization.val_injective
  rw [fraction_val, HomogeneousLocalization.val_one]
  simp only [pow_one, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self (Localization.Away f) (Submonoid.mem_powers f)

/-- The full normalization ideal is annihilated; no kernel equality is assumed. -/
theorem normalizationIdeal_le_ker :
    normalizationIdeal f ≤ RingHom.ker (normalize 𝒜 hf) := by
  apply Ideal.span_le.mpr
  intro a ha
  obtain rfl := Set.mem_singleton_iff.mp ha
  change normalize 𝒜 hf (f - 1) = 0
  rw [map_sub, normalize_pivot, map_one, sub_self]

/-- The map from the literal quotient to the actual homogeneous localization. -/
def fromQuotient : NormalizedRing f →+* HomogeneousLocalization.Away 𝒜 f :=
  Ideal.Quotient.lift (normalizationIdeal f) (normalize 𝒜 hf)
    (fun a ha => normalizationIdeal_le_ker 𝒜 hf ha)

@[simp] theorem fromQuotient_quotientMap (a : A) :
    fromQuotient 𝒜 hf (quotientMap f a) = normalize 𝒜 hf a := rfl

/-- Restrict the genuine localization lift of the quotient map to degree zero. -/
def toQuotient (_ : f ∈ 𝒜 1) : HomogeneousLocalization.Away 𝒜 f →+* NormalizedRing f :=
  HomogeneousLocalization.Away.lift 𝒜 (quotientMap f) (quotientMap_pivot_isUnit f)

/-- On every homogeneous fraction, setting f=1 retains its full numerator. -/
@[simp] theorem toQuotient_fraction (n : ℕ) (a : 𝒜 n) :
    toQuotient 𝒜 hf (fraction 𝒜 hf n a) = quotientMap f a := by
  have hu : (quotientMap_pivot_isUnit f).unit = 1 := by
    apply Units.ext
    exact (quotientMap_pivot_isUnit f).unit_spec.trans (quotientMap_pivot f)
  simp only [toQuotient, fraction, HomogeneousLocalization.Away.lift_mk,
    hu, one_pow, inv_one, Units.val_one, mul_one]

/-- Decomposition and subsequent normalization recover the original quotient map. -/
theorem toQuotient_normalize (a : A) :
    toQuotient 𝒜 hf (normalize 𝒜 hf a) = quotientMap f a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous a =>
      rw [normalize_of_mem 𝒜 hf a.property, toQuotient_fraction]

/-- The quotient-to-localization-to-quotient composite is the identity. -/
theorem toQuotient_fromQuotient (x : NormalizedRing f) :
    toQuotient 𝒜 hf (fromQuotient 𝒜 hf x) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show Ideal.Quotient.mk (normalizationIdeal f) a = quotientMap f a from rfl,
    fromQuotient_quotientMap, toQuotient_normalize]

/-- The reverse composite is the identity on every homogeneous fraction. -/
theorem fromQuotient_toQuotient (z : HomogeneousLocalization.Away 𝒜 f) :
    fromQuotient 𝒜 hf (toQuotient 𝒜 hf z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z
  have ha' : a ∈ 𝒜 n := by simpa using ha
  change fromQuotient 𝒜 hf
      (toQuotient 𝒜 hf (fraction 𝒜 hf n ⟨a, ha'⟩)) =
    fraction 𝒜 hf n ⟨a, ha'⟩
  rw [toQuotient_fraction, fromQuotient_quotientMap, normalize_of_mem 𝒜 hf ha']

/-- The actual degree-one affine Proj chart ring is the actual normalized quotient. -/
def awayEquivNormalized :
    HomogeneousLocalization.Away 𝒜 f ≃+* NormalizedRing f where
  toFun := toQuotient 𝒜 hf
  invFun := fromQuotient 𝒜 hf
  left_inv := fromQuotient_toQuotient 𝒜 hf
  right_inv := toQuotient_fromQuotient 𝒜 hf
  map_add' := map_add _
  map_mul' := map_mul _

/-- The equivalence has the defining formula on every degree-n fraction. -/
@[simp] theorem awayEquivNormalized_fraction (n : ℕ) (a : 𝒜 n) :
    awayEquivNormalized 𝒜 hf (fraction 𝒜 hf n a) = quotientMap f a :=
  toQuotient_fraction 𝒜 hf n a

/-- Its inverse on every homogeneous quotient element is the actual normalized fraction. -/
@[simp] theorem awayEquivNormalized_symm_quotientMap {n : ℕ} {a : A}
    (ha : a ∈ 𝒜 n) :
    (awayEquivNormalized 𝒜 hf).symm (quotientMap f a) =
      fraction 𝒜 hf n ⟨a, ha⟩ :=
  normalize_of_mem 𝒜 hf ha

end PaperVerification.HomogeneousChartDehomogenization

end
end
end TAF_LiteralSource_0309

section TAF_LiteralSource_0310
/- Original module: TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Graded coefficient inclusion and images of the irrelevant ideal

For a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` whose image contains every homogeneous element
of positive degree, in particular for a surjective one, the irrelevant ideal `ℬ₊` is contained
in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. This containment is the hypothesis under
which `f` induces `AlgebraicGeometry.Proj.map f : Proj ℬ ⟶ Proj 𝒜`. Nothing is required in
degree zero. An injective graded ring
homomorphism reflects homogeneity, so the inverse of a bijective one is again graded and the two
induce mutually inverse morphisms of `Proj`.

Degreewise rescaling by powers of a unit preserves the condition that a coordinate map
sends the irrelevant ideal to the unit ideal, allowing the rescaled coordinates to define
a morphism to `Proj` as well.

Coefficient inclusion also satisfies this containment, although it need not be surjective.
`TauCeti.GradedAlgebra.baseChangeMap` uses the same ring inclusion as Mathlib's
`GradedAlgHom.includeRight`, with the target grading over the extended coefficient ring.
This is the form needed for homogeneous localizations and projective coefficient projections.

More generally, a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` over a coefficient extension `R → S`
induces the graded comparison `TauCeti.GradedAlgebra.baseChangeLift f : S ⊗[R] A → B`. When `f`
exhibits `B` as the base change of `A` (`IsBaseChange S f`), the comparison is bijective and its
inverse `TauCeti.GradedAlgebra.baseChangeLiftInv` is graded as well.

## Main results

* `HomogeneousIdeal.irrelevant_le_map_of_grade_subset_range`: `ℬ₊ ≤ 𝒜₊.map f` when the image of
  `f` contains every homogeneous element of positive degree.
* `HomogeneousIdeal.irrelevant_le_map_of_surjective`: `ℬ₊ ≤ 𝒜₊.map f` for a surjective `f`.
* `Graded.map_mem_iff_of_injective`: an injective graded ring homomorphism reflects homogeneity.
* `HomogeneousIdeal.irrelevant_le_map_baseChangeMap`: the same containment for extension
  of the coefficient ring.
* `HomogeneousIdeal.irrelevant_le_map_of_isBaseChange`: the same containment for a graded ring
  homomorphism exhibiting its target as a base change.
* `TauCeti.GradedAlgebra.bijective_baseChangeLift`: the graded comparison `S ⊗[R] A → B` of a
  graded ring homomorphism exhibiting `B` as the base change of `A` is bijective.
* `GradedRingHom.mem_of_map_mem`: an injective graded ring homomorphism reflects homogeneity, so
  the inverse of a bijective one is again graded.
-/

public section

namespace GradedRingHom

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- An injective graded ring homomorphism reflects homogeneity: if `f a` lies in `ℬ i`, then `a`
lies in `𝒜 i`. In particular, the inverse of a bijective graded ring homomorphism is graded. -/
theorem mem_of_map_mem (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Injective f) {a : A} {i : ι}
    (ha : f a ∈ ℬ i) : a ∈ 𝒜 i := by
  -- `f` carries the degree-`i` component of `a` to that of `f a`, which is `f a` itself
  have h : f (DirectSum.decompose 𝒜 a i) = f a := by
    rw [f.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ ha]
  exact hf h ▸ SetLike.coe_mem _

end GradedRingHom

namespace HomogeneousIdeal

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  [PartialOrder ι] [CanonicallyOrderedAdd ι] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- If the image of a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` contains every homogeneous element
of positive degree, then the irrelevant ideal `ℬ₊` is contained in the image `𝒜₊.map f` of the
irrelevant ideal `𝒜₊`. -/
theorem irrelevant_le_map_of_grade_subset_range (f : 𝒜 →+*ᵍ ℬ)
    (hf : ∀ i, 0 < i → (ℬ i : Set B) ⊆ Set.range f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  refine (irrelevant_le _).mpr fun i hi b hb ↦ ?_
  obtain ⟨a, rfl⟩ := hf i hi hb
  -- `f a` is homogeneous of degree `i`, so it is the image of the degree-`i` component of `a`
  rw [← DirectSum.decompose_of_mem_same ℬ (hb : f a ∈ ℬ i), ← f.map_directSumDecompose]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hi (SetLike.coe_mem _))

/-- For a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the irrelevant ideal `ℬ₊` is
contained in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f :=
  irrelevant_le_map_of_grade_subset_range f fun _ _ ↦ hf.range_eq ▸ Set.subset_univ _

end HomogeneousIdeal

section Injective

variable {ι A B σ τ F : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]
  [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

/-- An injective graded ring homomorphism reflects homogeneity: `f x` is homogeneous of degree
`i` exactly when `x` is. In particular the inverse of a bijective graded ring homomorphism is
again graded. -/
theorem Graded.map_mem_iff_of_injective (f : F) (hf : Function.Injective f) {i : ι} {x : A} :
    f x ∈ ℬ i ↔ x ∈ 𝒜 i := by
  refine ⟨fun h ↦ ?_, Graded.map_mem f⟩
  -- `f` sends the degree-`i` component of `x` to that of `f x`, which is `f x` itself
  rw [← hf ((map_directSumDecompose 𝒜 ℬ f).trans (DirectSum.decompose_of_mem_same ℬ h))]
  exact SetLike.coe_mem _

end Injective

namespace TauCeti.HomogeneousIdeal

variable {A B σ : Type*} [Semiring A] [CommSemiring B] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Unit rescaling in positive degrees preserves the condition that the irrelevant ideal maps
to the unit ideal. -/
theorem map_irrelevant_eq_top_of_unit_rescaling
    (f g : A →+* B) (c : Bˣ)
    (h : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, g a = c ^ n * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤ := by
  have hle : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g := by
    rw [Ideal.map_le_iff_le_comap, HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn a ha
    exact (Ideal.unit_mul_mem_iff_mem _ (c.isUnit.pow n)).mp
      (h n hn a ha ▸ Ideal.mem_map_of_mem g (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha))
  rw [hf] at hle
  exact top_unique hle

end TauCeti.HomogeneousIdeal

namespace TauCeti.GradedAlgebra

open scoped TensorProduct

variable {ι R A : Type*}
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  (S : Type*) [CommSemiring S] [Algebra R S]
  (𝒜 : ι → Submodule R A)

/-- The coefficient inclusion as a graded ring map, using the grading over the extended
coefficient ring rather than its restriction of scalars. -/
-- The inclusion must compute in dependent types such as `Away ℬ (baseChangeMap S 𝒜 f)`.
@[expose]
def baseChangeMap : 𝒜 →+*ᵍ (fun n ↦ (𝒜 n).baseChange S) where
  __ := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem 1 hx

/-- The graded coefficient inclusion has the usual tensor-product inclusion as its ring map. -/
@[simp]
theorem baseChangeMap_toRingHom :
    (baseChangeMap S 𝒜).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom := (rfl)

/-- Coefficient extension sends a homogeneous element to its pure tensor with one. -/
@[simp]
theorem baseChangeMap_apply (a : A) : baseChangeMap S 𝒜 a = 1 ⊗ₜ[R] a := (rfl)

section IsBaseChange

variable {S} {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r)

/-- The graded comparison map `S ⊗[R] A → B`, `s ⊗ a ↦ s • f a`, of a graded ring homomorphism
`f` over the coefficient extension `R → S`. It is the graded ring homomorphism underlying
`GradedAlgHom.liftEquiv`, applied to `f` as a graded `R`-algebra homomorphism. -/
noncomputable def baseChangeLift : (fun n ↦ (𝒜 n).baseChange S) →+*ᵍ ℬ :=
  (GradedAlgHom.liftEquiv 𝒜 ℬ ⟨⟨f.toRingHom, hfR⟩, f.map_mem⟩).toGradedRingHom

/-- The graded comparison map sends a pure tensor `s ⊗ a` to `s • f a`
(`GradedAlgHom.liftEquiv_tmul`). -/
@[simp]
theorem baseChangeLift_tmul (s : S) (a : A) :
    baseChangeLift 𝒜 f hfR (s ⊗ₜ[R] a) = s • f a :=
  GradedAlgHom.liftEquiv_tmul _ s a

/-- The graded comparison map restricts to `f` along the coefficient inclusion. -/
@[simp]
theorem baseChangeLift_comp_baseChangeMap :
    (baseChangeLift 𝒜 f hfR).comp (baseChangeMap S 𝒜) = f :=
  GradedRingHom.ext fun a ↦ by simp

variable {𝒜 f hfR} in
/-- If `f` exhibits `B` as the base change of `A`, the graded comparison map `S ⊗[R] A → B` is
bijective. -/
theorem bijective_baseChangeLift
    (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap) :
    Function.Bijective (baseChangeLift 𝒜 f hfR) := by
  have h : ⇑(baseChangeLift 𝒜 f hfR) = hf.equiv := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp [IsBaseChange.equiv_tmul]
    | add x y hx hy => simp [hx, hy]
  rw [h]
  exact hf.equiv.bijective

variable (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap)

/-- The inverse of the graded comparison map `S ⊗[R] A → B` of a graded ring homomorphism
exhibiting `B` as the base change of `A`, which is graded as well. -/
noncomputable def baseChangeLiftInv : ℬ →+*ᵍ (fun n ↦ (𝒜 n).baseChange S) where
  __ := (RingEquiv.ofBijective _ (bijective_baseChangeLift hf)).symm.toRingHom
  map_mem {n b} hb := (baseChangeLift 𝒜 f hfR).mem_of_map_mem
    (bijective_baseChangeLift hf).injective (by
      simpa [← RingEquiv.ofBijective_apply _ (bijective_baseChangeLift hf)] using hb)

/-- `baseChangeLiftInv` is a right inverse of the graded comparison map. -/
theorem baseChangeLift_baseChangeLiftInv :
    Function.RightInverse (baseChangeLiftInv 𝒜 f hfR hf) (baseChangeLift 𝒜 f hfR) :=
  (RingEquiv.ofBijective _ (bijective_baseChangeLift hf)).apply_symm_apply

/-- `baseChangeLiftInv` is a left inverse of the graded comparison map. -/
theorem baseChangeLiftInv_baseChangeLift :
    Function.LeftInverse (baseChangeLiftInv 𝒜 f hfR hf) (baseChangeLift 𝒜 f hfR) :=
  (RingEquiv.ofBijective _ (bijective_baseChangeLift hf)).symm_apply_apply

end IsBaseChange

end TauCeti.GradedAlgebra

namespace HomogeneousIdeal

open scoped TensorProduct
open TauCeti.GradedAlgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (S : Type*) [CommSemiring S] [Algebra R S]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The irrelevant ideal after scalar extension lies in the ideal generated by the images
of the original positive-degree elements. In particular, coefficient extension defines a morphism
of `Proj`. -/
theorem irrelevant_le_map_baseChangeMap :
    irrelevant (fun n ↦ (𝒜 n).baseChange S) ≤ (irrelevant 𝒜).map (baseChangeMap S 𝒜) := by
  refine (irrelevant_le _).mpr fun n hn x hx ↦ ?_
  obtain ⟨y, hy⟩ := (𝒜 n).toBaseChange_surjective S ⟨x, hx⟩
  have hmem : ∀ y : S ⊗[R] 𝒜 n, ((𝒜 n).toBaseChange S y : S ⊗[R] A) ∈
      ((irrelevant 𝒜).map (baseChangeMap S 𝒜)).toIdeal := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simpa only [map_add, Submodule.coe_add] using add_mem hy hz
    | tmul s a =>
      rw [HomogeneousIdeal.toIdeal_map]
      have ha := Ideal.mem_map_of_mem (baseChangeMap S 𝒜)
        (mem_irrelevant_of_mem 𝒜 hn a.2)
      simpa only [Submodule.coe_toBaseChange_tmul, baseChangeMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] using
        Ideal.mul_mem_left _ (s ⊗ₜ[R] (1 : A)) ha
  -- `irrelevant_le` presents membership in the additive submonoid; the tensor induction
  -- uses membership in the ideal, with the same underlying carrier.
  change x ∈ ((irrelevant 𝒜).map (baseChangeMap S 𝒜)).toIdeal
  simpa only [hy] using hmem y

variable {S} {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ)
  (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r)

/-- If a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` over `R → S` exhibits `B` as the base change
`S ⊗[R] A`, then `ℬ₊ ≤ 𝒜₊.map f`, so that `f` induces a morphism `Proj ℬ ⟶ Proj 𝒜`. -/
theorem irrelevant_le_map_of_isBaseChange
    (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  rw [← baseChangeLift_comp_baseChangeMap 𝒜 f hfR]
  exact irrelevant_le_map_comp (irrelevant_le_map_baseChangeMap S 𝒜)
    (irrelevant_le_map_of_surjective _ (bijective_baseChangeLift hf).surjective)

end HomogeneousIdeal
end
end TAF_LiteralSource_0310

section TAF_LiteralSource_0311
/- Original module: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Points of `Proj` through standard charts, and compatibilities of `Proj.map`

For a graded ring `A`, a ring homomorphism `φ : A →+* R` and a homogeneous element `f` of positive
degree with `φ f` a unit, the composite

`Spec R ⟶ Spec A_{(f)} ⟶ Proj A`

of `Spec` of `HomogeneousLocalization.Away.lift φ` with the standard chart `Proj.awayι` is the
`R`-point of `Proj A` with "homogeneous coordinates" `φ`. This file proves that it does not
depend on the chart: any other homogeneous `g` of positive degree with `φ g` a unit gives the same
morphism. It also proves that `Proj.map` of a graded ring homomorphism lies over the induced map on
`Spec` of the degree-zero parts, and packages `Proj.map` of a graded ring isomorphism as an
isomorphism of schemes. It computes the locus where a function `g / fⁿ` on a standard
chart `D₊(f)` is invertible: it is `D₊(fg)`, so the restriction of sections from `D₊(f)` to
`D₊(fg)` is a localization at `g / fⁿ`. Finally, it identifies the inverse image under
`Proj A ⟶ Spec A₀` of the basic open of a degree-zero element `r` with the standard open `D₊(r)`,
so that the structure map to `Spec A₀` can be studied through homogeneous prime ideals, and shows
that on `D₊(f)`, and hence at every point, the functions pulled back from `Spec A₀` are the
fractions `a / 1`. It also
proves the homogeneous Nullstellensatz for elements of the irrelevant ideal, with two consequences
used to compute the sections of the twisting sheaves over standard opens: a homogeneous element
vanishing in the localizations at all points of `D₊(g)` is killed by a power of `g`, and compatible
homogeneous fractions covering `D₊(f)` glue to a single fraction over a power of `f`. These two
are graded versions of the injectivity and gluing steps of Mathlib's computation of the sections
of the structure sheaf of `Spec` over basic opens
(`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_injective` and
`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_surjective` in
`Mathlib/AlgebraicGeometry/StructureSheaf.lean`), whose arguments they adapt.

## Main definitions

* `AlgebraicGeometry.Proj.mapIso`: the isomorphism `Proj ℬ ≅ Proj 𝒜` induced by mutually inverse
  graded ring homomorphisms.

## Main results

* `AlgebraicGeometry.Proj.map_congr`: `Proj.map f` depends only on `f`.
* `AlgebraicGeometry.Proj.SpecMap_awayLift_awayι_eq`: the point of `Proj A` defined by `φ` on the
  chart `D₊(f)` agrees with the one defined on the chart `D₊(g)`.
* `AlgebraicGeometry.Proj.map_toSpecZero`: `Proj.map f` lies over `Spec` of the degree-zero part
  of `f`.
* `AlgebraicGeometry.Proj.basicOpen_awayToSection_mk`: on the chart `D₊(f)`, the function `g / fⁿ`
  is invertible exactly on `D₊(fg)`; its values in the localizations are given by
  `AlgebraicGeometry.Proj.val_awayToSection_mk_apply`.
* `AlgebraicGeometry.Proj.toSpecZero_preimage_basicOpen`: the inverse image of the basic open
  `D(r)` of a degree-zero element under `Proj A ⟶ Spec A₀` is the standard open `D₊(r)`.
* `AlgebraicGeometry.Proj.toSpecZero_appLE_basicOpen`: on `D₊(f)`, the functions pulled back
  along `Proj A ⟶ Spec A₀` are the fractions `a / 1`; globally, their values in the localizations
  are given by `AlgebraicGeometry.Proj.val_toSpecZero_appTop_apply`.
* `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top`: if `A` is generated in degree
  one over `A₀`, the standard opens of degree-one elements cover `Proj A`.
* `ProjectiveSpectrum.exists_le_mem_notMem`: a projective point misses homogeneous elements of
  arbitrarily large degree.
* `ProjectiveSpectrum.ext_of_mem_pos`: positive-degree homogeneous elements determine a
  projective point, allowing comparison through its positive-degree coordinate opens.
* `ProjectiveSpectrum.mem_radical_of_zeroLocus_subset`: the homogeneous Nullstellensatz, for
  elements of the irrelevant ideal.
* `ProjectiveSpectrum.exists_pow_mul_eq_zero`: a homogeneous element which is locally zero on
  `D₊(g)` is killed by a power of `g`.
* `ProjectiveSpectrum.exists_mul_eq_pow_mul`: compatible homogeneous fractions whose standard opens
  cover `D₊(f)` glue to a single fraction with a power of `f` as denominator.
* `ProjectiveSpectrum.comap_extendOfIsLocalization` and
  `ProjectiveSpectrum.extendOfIsLocalization_comap`: if a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`
  exhibits `B` as a localization of `A` at `M`, the points of `Proj ℬ` are, through `f⁻¹`, the
  points of `Proj 𝒜` disjoint from `M`; the point over `x` is the extension of the homogeneous
  prime ideal of `x` (`ProjectiveSpectrum.extendOfIsLocalization`).
-/

public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The `R`-point of `Proj A` with homogeneous coordinates `φ : A →+* R`, read on the standard
chart `D₊(f)`, does not depend on the homogeneous element `f` of positive degree with `φ f` a
unit: both charts give the point read on `D₊(fg)`. -/
theorem SpecMap_awayLift_awayι_eq {R : Type u} [CommRing R] (φ : A →+* R) {f g : A} {m m' : ℕ}
    (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') (hf : IsUnit (φ f))
    (hg : IsUnit (φ g)) :
    Spec.map (CommRingCat.ofHom (Away.lift 𝒜 φ hf)) ≫ awayι 𝒜 f f_deg hm =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 φ hg)) ≫ awayι 𝒜 g g_deg hm' := by
  have hfg : IsUnit (φ (f * g)) := by rw [map_mul]; exact hf.mul hg
  rw [← Away.lift_comp_awayMap φ g_deg rfl hfg hf,
    ← Away.lift_comp_awayMap φ f_deg (mul_comm f g) hfg hg, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    SpecMap_awayMap_awayι, SpecMap_awayMap_awayι]
  -- the two charts `D₊(fg)` differ only in the order of the degree `m + m'` of `fg`
  congr 2
  exact add_comm m m'

/-- `Proj.map f` lies over `Spec` of the ring homomorphism `𝒜 0 →+* ℬ 0` induced by `f` on the
degree-zero parts. -/
@[reassoc (attr := simp)]
theorem map_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤
    (HomogeneousIdeal.irrelevant 𝒜).map f) :
    map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun ⟨i, x, hx⟩ ↦ ?_
  -- the chart of `mapAffineOpenCover` at `⟨i, x⟩` is `awayι ℬ (f x)`, by definition
  have hpos : 0 < (i : ℕ) := i.2
  have key : awayι ℬ (f x) (f.2 hx) hpos ≫ map f hf ≫ toSpecZero 𝒜 =
      awayι ℬ (f x) (f.2 hx) hpos ≫ toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
    rw [awayι_comp_map_assoc f hf hpos x hx, awayι_toSpecZero, awayι_toSpecZero_assoc,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    have h𝒜 : fromZeroRingHom 𝒜 (.powers x) a = Away.mk 𝒜 hx 0 a (by simp) := by
      ext
      exact (Localization.mk_eq_mk_iff.mpr (by simp [Localization.r_iff_exists])).symm
    rw [h𝒜, Away.map_mk]
    exact Localization.mk_eq_mk_iff.mpr (by simp [Localization.r_iff_exists])
  exact key

/-- `Proj.map f` depends only on the graded ring homomorphism `f`, and not on the proof that the
irrelevant ideal of the target is contained in the ideal generated by the image of the irrelevant
ideal of the source. -/
theorem map_congr {f g : 𝒜 →+*ᵍ ℬ} (hfg : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    map f hf = map g hg := by
  subst hfg
  rfl

/-- Mutually inverse graded ring homomorphisms `f : 𝒜 →+*ᵍ ℬ` and `g : ℬ →+*ᵍ 𝒜` induce mutually
inverse morphisms `Proj.map f` and `Proj.map g`. -/
noncomputable def mapIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : Function.RightInverse g f)
    (hgf : Function.LeftInverse g f) : Proj ℬ ≅ Proj 𝒜 where
  hom := map f (HomogeneousIdeal.irrelevant_le_map_of_surjective f hfg.surjective)
  inv := map g (HomogeneousIdeal.irrelevant_le_map_of_surjective g hgf.surjective)
  hom_inv_id := by
    rw [← map_comp]
    convert map_id (𝒜 := ℬ)
    exact GradedRingHom.ext hfg
  inv_hom_id := by
    rw [← map_comp]
    convert map_id (𝒜 := 𝒜)
    exact GradedRingHom.ext hgf

@[simp]
theorem mapIso_hom (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : Function.RightInverse g f)
    (hgf : Function.LeftInverse g f) :
    (mapIso f g hfg hgf).hom =
      map f (HomogeneousIdeal.irrelevant_le_map_of_surjective f hfg.surjective) :=
  (rfl)

@[simp]
theorem mapIso_inv (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (hfg : Function.RightInverse g f)
    (hgf : Function.LeftInverse g f) :
    (mapIso f g hfg hgf).inv =
      map g (HomogeneousIdeal.irrelevant_le_map_of_surjective g hgf.surjective) :=
  (rfl)

variable (𝒜) in
/-- **Degree-zero basic opens.** The inverse image under `Proj A ⟶ Spec A₀` of the basic open
`D(r)` of a degree-zero element `r` is the standard open `D₊(r)` of `Proj A`: the points `x` with
`r ∉ x`. -/
@[simp]
theorem toSpecZero_preimage_basicOpen (r : 𝒜 0) :
    toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen r = basicOpen 𝒜 (r : A) := by
  ext x
  -- `x` lies in some standard chart `D₊(f)` with `f` homogeneous of positive degree.
  obtain ⟨i, hi, f, f_deg, hfx⟩ : ∃ i > 0, ∃ f ∈ 𝒜 i, f ∉ x.asHomogeneousIdeal := by
    by_contra! h
    exact x.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp
      ((HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr h))
  obtain ⟨z, rfl⟩ : x ∈ (awayι 𝒜 f f_deg hi).opensRange := by rwa [opensRange_awayι]
  have h₁ : awayι 𝒜 f f_deg hi z ∈ toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen r ↔
      z ∈ (PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 _ r) : (Spec (.of (Away 𝒜 f))).Opens) := by
    have h := Scheme.Hom.comp_preimage (awayι 𝒜 f f_deg hi) (toSpecZero 𝒜)
      (PrimeSpectrum.basicOpen r)
    rw [awayι_toSpecZero, SpecMap_preimage_basicOpen] at h
    rw [← Scheme.Hom.mem_preimage, ← h, CommRingCat.ofHom_apply]
    -- the sides differ only in typing `D(r / 1)` as an open of `Spec` or of the prime spectrum
    rfl
  -- On `D₊(f)`, the standard open `D₊(r) = D₊(r f)` is cut out by `(r f)ⁱ / fⁱ = (r / 1)ⁱ`.
  have hrf : (r : A) * f ∈ 𝒜 i := by simpa using SetLike.mul_mem_graded r.2 f_deg
  have helem : Away.isLocalizationElem f_deg hrf = fromZeroRingHom 𝒜 _ r ^ i := by
    apply val_injective
    -- `fromZeroRingHom` sends `r` to the fraction `r / 1`
    have hr : (fromZeroRingHom 𝒜 (Submonoid.powers f) r).val = Localization.mk (r : A) 1 := by
      simp only [fromZeroRingHom]
      exact val_mk _
    rw [Away.val_mk, val_pow, hr, Localization.mk_pow, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp [mul_pow, mul_comm]⟩
  have h₂ : awayι 𝒜 f f_deg hi z ∈ basicOpen 𝒜 (r : A) ↔
      z ∈ (PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 _ r) : (Spec (.of (Away 𝒜 f))).Opens) := by
    have hzf : awayι 𝒜 f f_deg hi z ∈ basicOpen 𝒜 f := opensRange_awayι 𝒜 f f_deg hi ▸ ⟨z, rfl⟩
    rw [← PrimeSpectrum.basicOpen_pow _ i hi, ← helem,
      ← awayι_preimage_basicOpen 𝒜 f_deg hi hrf hi]
    exact ⟨fun h ↦ (basicOpen_mul 𝒜 _ _).ge ⟨h, hzf⟩, fun h ↦ ((basicOpen_mul 𝒜 _ _).le h).1⟩
  exact h₁.trans h₂.symm

variable (𝒜) in
/-- **Constants on a standard chart.** On the chart `D₊(f)`, for `f` homogeneous of positive degree,
the functions pulled back from `Spec A₀` along `Proj A ⟶ Spec A₀` are the fractions `a / 1` of
degree-zero elements `a`. -/
theorem toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (toSpecZero 𝒜).appLE ⊤ (basicOpen 𝒜 f) le_top =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (fromZeroRingHom 𝒜 _) ≫ awayToSection 𝒜 f := by
  -- compose with the isomorphism `Γ(Proj A, D₊(f)) ≅ Γ(D₊(f), ⊤)` given by the inclusion
  rw [← cancel_mono ((basicOpen 𝒜 f).ι.appLE (basicOpen 𝒜 f) ⊤ (basicOpen 𝒜 f).ι_preimage_self.ge)]
  refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
  -- on `D₊(f) ≅ Spec A_(f)`, the structure map is `Spec` of `A₀ → A_(f)`
  have hι : (basicOpen 𝒜 f).ι ≫ toSpecZero 𝒜 = (basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
    rw [← awayι_toSpecZero 𝒜 f f_deg hm, ← basicOpenIsoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  -- The proof of `⊤ ≤ ⊤` carried by the restriction map has type `⊤ ≤ f ⁻¹ᵁ ⊤` only up to
  -- unfolding `Scheme.Hom.preimage`, so `Scheme.Hom.appLE_eq_app` is applied by unification
  -- rather than by `rw`; the middle term is fixed to `appTop`, whose codomain is `Γ(_, ⊤)`
  -- rather than `Γ(_, f ⁻¹ᵁ ⊤)`.
  refine Eq.trans (b := Scheme.Hom.appTop _) (Scheme.Hom.appLE_eq_app _) ?_
  -- The `show` reads `basicOpenToSpec_app_top`, stated for `app ⊤`, through the abbreviation
  -- `appTop`.
  rw [hι, Scheme.Hom.comp_appTop, basicOpenIsoSpec_hom,
    show (basicOpenToSpec 𝒜 f).appTop = _ from basicOpenToSpec_app_top 𝒜 f, ← Category.assoc,
    Scheme.ΓSpecIso_naturality]
  simp only [Category.assoc, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
  -- both sides restrict along the inclusion `D₊(f) ≤ ι '' ⊤`, and inclusions of opens are unique
  rfl

/-- **Constants are the fractions `a / 1`.** The global function on `Proj A` pulled back from the
degree-zero element `a` of `A₀` along `Proj A ⟶ Spec A₀` takes the value `a / 1` in the
localization at every point. -/
theorem val_toSpecZero_appTop_apply (a : 𝒜 0) (x : (⊤ : (Proj 𝒜).Opens)) :
    (((toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv a)).1 x).val = Localization.mk (a : A) 1 := by
  -- `x` lies in a standard chart `D₊(f)`, on which the function is `a / 1`
  obtain ⟨m, hm, f, f_deg, hfx⟩ : ∃ m > 0, ∃ f ∈ 𝒜 m, f ∉ x.1.asHomogeneousIdeal := by
    by_contra! h
    exact x.1.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr h)
  have h := ConcreteCategory.congr_hom (toSpecZero_appLE_basicOpen 𝒜 f_deg hm)
    ((Scheme.ΓSpecIso _).inv a)
  -- restriction to `D₊(f)` keeps the value at `x`
  have e : (((toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv a)).1 x).val = _ :=
    congrArg (fun s : Γ(Proj 𝒜, basicOpen 𝒜 f) ↦ (s.1 ⟨x.1, hfx⟩).val) h
  refine e.trans ?_
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  -- `awayToSection` sends `a / 1` to the function whose value at each point is the fraction
  -- `a / 1`, by definition of `fromZeroRingHom` and `awayToSection`
  rfl

variable (𝒜) in
/-- **Generation in degree one.** If `A` is generated by `A₁` as an `A₀`-algebra, the standard
opens `D₊(f)` of the elements `f ∈ A₁` cover `Proj A`. -/
theorem iSup_basicOpen_eq_top_of_adjoin_eq_top (h : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) :
    ⨆ f : 𝒜 1, basicOpen 𝒜 (f : A) = ⊤ :=
  iSup_basicOpen_eq_top' 𝒜 _ (fun f ↦ ⟨1, f.2⟩) (by rwa [Subtype.range_coe_subtype])

section

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- On the standard chart `D₊(f)`, the function `g / fⁿ` takes the value `g / fⁿ` in the
localization at each point. -/
theorem val_awayToSection_mk_apply {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (g : A)
    (hg : g ∈ 𝒜 (n • d)) (x : basicOpen 𝒜 f) :
    ((awayToSection 𝒜 f (Away.mk 𝒜 hf n g hg)).1 x).val =
      Localization.mk g ⟨f ^ n, fun h ↦ x.2 (x.1.isPrime.mem_of_pow_mem n h)⟩ :=
  (rfl)

/-- On the standard chart `D₊(f)`, the function `g / fⁿ` is invertible exactly on `D₊(fg)`. -/
theorem basicOpen_awayToSection_mk {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (g : A)
    (hg : g ∈ 𝒜 (n • d)) :
    (Proj 𝒜).basicOpen (awayToSection 𝒜 f (Away.mk 𝒜 hf n g hg)) = basicOpen 𝒜 (f * g) := by
  ext p
  rw [SetLike.mem_coe, SetLike.mem_coe, basicOpen_mul, TopologicalSpace.Opens.mem_inf]
  by_cases hp : p ∈ basicOpen 𝒜 f
  · -- the germ of `g / fⁿ` at `p` is `g / fⁿ` in the homogeneous localization at `p`
    rw [Scheme.mem_basicOpen _ _ _ hp]
    have h := ConcreteCategory.congr_hom (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f p hp)
      (Away.mk 𝒜 hf n g hg)
    -- `erw`: the germ map of the scheme `Proj 𝒜` is that of its structure sheaf only up to
    -- unfolding the scheme structure
    erw [h]
    refine (MulEquiv.isUnit_map (Proj.stalkIso' 𝒜 p).symm.toMulEquiv
      (x := mapId 𝒜 (Submonoid.powers_le.mpr hp) (Away.mk 𝒜 hf n g hg))).trans ?_
    rw [← isUnit_iff_isUnit_val]
    -- `erw`: the homogeneous prime of `p` is read through the same identification
    erw [Away.mk, map_mk, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact ⟨fun h ↦ ⟨hp, h⟩, And.right⟩
  · simp only [hp, false_and, iff_false]
    exact fun h ↦ hp ((Proj 𝒜).basicOpen_le _ h)

end

end AlgebraicGeometry.Proj

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A relevant homogeneous prime ideal misses homogeneous elements of arbitrarily large degree: it
misses a homogeneous element of positive degree, and hence all of its powers. -/
theorem exists_le_mem_notMem (x : ProjectiveSpectrum 𝒜) (N : ℕ) :
    ∃ i, N ≤ i ∧ ∃ s ∈ 𝒜 i, s ∉ x.asHomogeneousIdeal := by
  obtain ⟨d, hd, f, hf, hfx⟩ : ∃ d > 0, ∃ f ∈ 𝒜 d, f ∉ x.asHomogeneousIdeal := by
    by_contra! h
    exact x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr h)
  exact ⟨N * d, Nat.le_mul_of_pos_right N hd, f ^ N, by simpa using SetLike.pow_mem_graded N hf,
    fun h ↦ hfx (x.isPrime.mem_of_pow_mem N h)⟩

/-- Relevant homogeneous prime ideals are determined by their positive-degree elements. -/
theorem ext_of_mem_pos {x y : ProjectiveSpectrum 𝒜}
    (h : ∀ n > 0, ∀ s ∈ 𝒜 n,
      s ∈ x.asHomogeneousIdeal ↔ s ∈ y.asHomogeneousIdeal) : x = y := by
  have hex : ∃ n > 0, ∃ t ∈ 𝒜 n, t ∉ x.asHomogeneousIdeal := by
    by_contra! ht
    exact x.not_irrelevant_le ((toIdeal_le_toIdeal_iff).mp
      ((HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr ht))
  obtain ⟨n, hn, t, ht, htx⟩ := hex
  have hty : t ∉ y.asHomogeneousIdeal := fun hy ↦ htx ((h n hn t ht).mpr hy)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro i s hs
  rcases i with _ | i
  · have hst : s * t ∈ 𝒜 n := by
      simpa using SetLike.mul_mem_graded hs ht
    have heq := h n hn (s * t) hst
    have htx' : t ∉ x.asHomogeneousIdeal.toIdeal := HomogeneousIdeal.mem_iff.not.mpr htx
    have hty' : t ∉ y.asHomogeneousIdeal.toIdeal := HomogeneousIdeal.mem_iff.not.mpr hty
    simpa only [← HomogeneousIdeal.mem_iff, x.isPrime.mul_mem_iff_mem_or_mem,
      y.isPrime.mul_mem_iff_mem_or_mem, htx', hty', or_false] using heq
  · exact h (i + 1) (Nat.succ_pos i) s hs

/-- **Homogeneous Nullstellensatz on `Proj`.** If an element `f` of the irrelevant ideal lies in
every point of `Proj A` containing a homogeneous ideal `I`, then `f` lies in the radical of `I`. -/
theorem mem_radical_of_zeroLocus_subset {I : Ideal A} (hI : I.IsHomogeneous 𝒜) {f : A}
    (hf : f ∈ HomogeneousIdeal.irrelevant 𝒜) (h : zeroLocus 𝒜 I ⊆ zeroLocus 𝒜 {f}) :
    f ∈ I.radical := by
  rw [Ideal.IsHomogeneous.radical_eq hI, Submodule.mem_sInf]
  rintro J ⟨hJ, hIJ, hJp⟩
  by_contra hfJ
  -- otherwise `J` is a relevant homogeneous prime containing `I` but not `f`
  have hx : (⟨⟨J, hJ⟩, hJp, fun hle ↦ hfJ (hle hf)⟩ : ProjectiveSpectrum 𝒜) ∈ zeroLocus 𝒜 {f} :=
    h hIJ
  exact hfJ (hx (Set.mem_singleton f))

/-- Let `g` be an element of the irrelevant ideal, for instance homogeneous of positive degree,
and `a` homogeneous. If at every point `x` of `D₊(g)` the element `a` is annihilated by some element
outside `x`, then `a` is annihilated by a power of `g`. -/
theorem exists_pow_mul_eq_zero {g a : A} {k : ℕ} (hg : g ∈ HomogeneousIdeal.irrelevant 𝒜)
    (ha : a ∈ 𝒜 k)
    (h : ∀ x : ProjectiveSpectrum 𝒜, g ∉ x.asHomogeneousIdeal →
      ∃ c ∉ x.asHomogeneousIdeal, c * a = 0) :
    ∃ N, g ^ N * a = 0 := by
  classical
  -- the homogeneous core `I` of the annihilator of `a` is a homogeneous ideal annihilating `a`
  let I := (Submodule.span A {a}).annihilator.homogeneousCore 𝒜
  suffices g ∈ I.toIdeal.radical from this.imp fun N hN ↦
    (Submodule.mem_annihilator_span_singleton _ _).1 (Ideal.toIdeal_homogeneousCore_le 𝒜 _ hN)
  refine mem_radical_of_zeroLocus_subset I.isHomogeneous hg fun x hx ↦ ?_
  rw [mem_zeroLocus, Set.singleton_subset_iff]
  by_contra hgx
  obtain ⟨c, hcx, hc⟩ := h x hgx
  -- some homogeneous component `cᵢ` of `c` lies outside `x`, and `cᵢ * a = 0` lies in `I`
  obtain ⟨i, hi⟩ : ∃ i, (DirectSum.decompose 𝒜 c i : A) ∉ x.asHomogeneousIdeal := by
    by_contra! H
    exact hcx ((x.asHomogeneousIdeal.isHomogeneous.mem_iff 𝒜).2 H)
  refine hi (hx (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨i, SetLike.coe_mem _⟩
    ((Submodule.mem_annihilator_span_singleton _ _).2 ?_)))
  simpa [hc] using (DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := c) (i := i) ha).symm

/-- **Gluing homogeneous fractions.** Let `f` be homogeneous of positive degree `d`, and let
`r x / g x` be finitely many fractions of homogeneous elements of degrees `deg r x = deg g x + n`
whose standard opens `D₊(g x)` cover `D₊(f)`, and which are compatible in the strong sense
`g x * r z = g z * r x`. Then there is a single fraction `R / fᵏ`, with `R` homogeneous of degree
`k * d + n`, such that `g x * R = fᵏ * r x` for every `x`. -/
theorem exists_mul_eq_pow_mul {n : ℤ} {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {ι : Type*}
    [Finite ι] {i j : ι → ℕ} (h : ∀ x, (j x : ℤ) = i x + n) {r g : ι → A}
    (hr : ∀ x, r x ∈ 𝒜 (j x)) (hg : ∀ x, g x ∈ 𝒜 (i x))
    (hcover : ∀ y : ProjectiveSpectrum 𝒜, f ∉ y.asHomogeneousIdeal →
      ∃ x, g x ∉ y.asHomogeneousIdeal)
    (hcompat : ∀ x z, g x * r z = g z * r x) :
    ∃ (k J : ℕ) (_ : (J : ℤ) = (k * d : ℕ) + n) (R : A), R ∈ 𝒜 J ∧ ∀ x, g x * R = f ^ k * r x := by
  classical
  have := Fintype.ofFinite ι
  -- `f` lies in the radical of the ideal generated by the `g x`
  obtain ⟨K, hK⟩ : f ∈ (Ideal.span (Set.range g)).radical := by
    refine mem_radical_of_zeroLocus_subset (Ideal.homogeneous_span _ _ ?_)
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hf) fun y hy ↦ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, hg x⟩
    rw [mem_zeroLocus, Set.singleton_subset_iff]
    by_contra hfy
    obtain ⟨x, hx⟩ := hcover y hfy
    exact hx (hy (Ideal.subset_span ⟨x, rfl⟩))
  -- raise the exponent so that the numerator has nonnegative degree `k * d + n`
  set k := K + n.natAbs
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1
    (show f ^ k ∈ _ from pow_add f K n.natAbs ▸ Ideal.mul_mem_right _ _ hK)
  have hkd : k ≤ k * d := Nat.le_mul_of_pos_right k hd
  set J := ((k * d : ℕ) + n).toNat
  have hJ : (J : ℤ) = (k * d : ℕ) + n := by omega
  -- the numerator is the degree-`J` part of `∑ x, c x * r x`
  refine ⟨k, J, hJ, _, SetLike.coe_mem (DirectSum.decompose 𝒜 (∑ x, c x * r x) J), fun x ↦ ?_⟩
  have hmem : f ^ k * r x ∈ 𝒜 (J + i x) := by
    convert SetLike.mul_mem_graded (SetLike.pow_mem_graded k hf) (hr x) using 2
    have := h x
    simp only [smul_eq_mul]
    omega
  have hsum : (∑ z, c z * r z) * g x = f ^ k * r x := by
    rw [Finset.sum_mul, ← hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ ↦ by
      rw [mul_assoc, mul_comm (r z), hcompat x z, ← mul_assoc]
  rw [mul_comm (g x), ← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (hg x), hsum,
    DirectSum.decompose_of_mem_same 𝒜 hmem]

section Localization

open HomogeneousIdeal

variable {A B σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {f : 𝒜 →+*ᵍ ℬ} {M : Submonoid A} (hloc : letI := f.toRingHom.toAlgebra; IsLocalization M B)

/-- For `f : 𝒜 →+*ᵍ ℬ` exhibiting `B` as a localization of `A` at `M`, the point of `Proj ℬ`
over a point `x` of `Proj 𝒜` disjoint from `M`: its homogeneous prime ideal is the extension of
that of `x`. -/
def extendOfIsLocalization (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) : ProjectiveSpectrum ℬ where
  asHomogeneousIdeal := x.asHomogeneousIdeal.map f
  isPrime :=
    letI := f.toRingHom.toAlgebra
    IsLocalization.isPrime_of_isPrime_disjoint M B _ x.isPrime hx
  not_irrelevant_le h := by
    let := f.toRingHom.toAlgebra
    obtain ⟨i, hi, s, hs, hsx⟩ := x.exists_le_mem_notMem 1
    refine hsx ?_
    rw [← HomogeneousIdeal.mem_iff,
      ← IsLocalization.under_map_of_isPrime_disjoint M B x.isPrime hx]
    exact h (mem_irrelevant_of_mem ℬ (by omega : 0 < i) (Graded.map_mem f hs))

/-- The homogeneous prime ideal of the point over `x` is the extension of that of `x`. -/
theorem extendOfIsLocalization_asHomogeneousIdeal (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) :
    (x.extendOfIsLocalization hloc hx).asHomogeneousIdeal = x.asHomogeneousIdeal.map f :=
  (rfl)

include hloc in
/-- The point of `Proj ℬ` over `x` contains `f a` exactly when `x` contains `a`. -/
@[simp]
theorem map_mem_extendOfIsLocalization_iff (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) (a : A) :
    f a ∈ (x.extendOfIsLocalization hloc hx).asHomogeneousIdeal ↔ a ∈ x.asHomogeneousIdeal := by
  let := f.toRingHom.toAlgebra
  -- `f a ∈ x B` says that `a` lies in the contraction of the extension `x B`, which is `x`
  exact Iff.of_eq
    (congrArg (a ∈ ·) (IsLocalization.under_map_of_isPrime_disjoint M B x.isPrime hx))

variable (hf : ℬ₊ ≤ 𝒜₊.map f)
include hloc

/-- The point of `Proj ℬ` over `x` lies over `x`. -/
@[simp]
theorem comap_extendOfIsLocalization (x : ProjectiveSpectrum 𝒜)
    (hx : Disjoint (M : Set A) x.asHomogeneousIdeal.toIdeal) :
    AlgebraicGeometry.ProjectiveSpectrum.comap f hf (x.extendOfIsLocalization hloc hx) = x :=
  ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
    (Ideal.ext (map_mem_extendOfIsLocalization_iff hloc x hx)))

/-- The points of `Proj 𝒜` under points of `Proj ℬ` are disjoint from `M`, whose image consists of
units. -/
theorem disjoint_comap_of_isLocalization (y : ProjectiveSpectrum ℬ) :
    Disjoint (M : Set A)
      (AlgebraicGeometry.ProjectiveSpectrum.comap f hf y).asHomogeneousIdeal.toIdeal := by
  let := f.toRingHom.toAlgebra
  exact Set.disjoint_left.mpr fun m hm hmy ↦
    y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmy (IsLocalization.map_units B ⟨m, hm⟩))

/-- Every point of `Proj ℬ` is the point over its image in `Proj 𝒜`. -/
@[simp]
theorem extendOfIsLocalization_comap (y : ProjectiveSpectrum ℬ) :
    (AlgebraicGeometry.ProjectiveSpectrum.comap f hf y).extendOfIsLocalization hloc
      (ProjectiveSpectrum.disjoint_comap_of_isLocalization hloc hf y) = y := by
  let := f.toRingHom.toAlgebra
  exact ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
    (IsLocalization.map_under M B y.asHomogeneousIdeal.toIdeal))

end Localization

end ProjectiveSpectrum
end
end TAF_LiteralSource_0311

section TAF_LiteralSource_0312
/- Original module: PaperVerification.HomogeneousQuotientProjective -/


/-!
# The actual graded ring and projective spectrum of a homogeneous quotient

The homogeneous pieces are the images of the original polynomial pieces.
Their previously proved internal direct sum and multiplication laws give
Mathlib's genuine GradedAlgebra instance.  A surjective polynomial
presentation by degree-one elements gives an actual basic-open cover of Proj.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousQuotientProjective

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K

/-- The same internal grading already constructed from the original quotient. -/
def grading (Q : Ideal P) (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    ℕ → Submodule K (P⧸Q) := (HomogeneousIdealPieces.grading Q hQ).piece

@[simp] theorem grading_eq_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (d : ℕ) :
    grading Q hQ d=HomogeneousIdealPieces.piece Q d :=
  HomogeneousIdealPieces.grading_piece Q hQ d

instance quotientGradedMonoid (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    SetLike.GradedMonoid (grading Q hQ) where
  one_mem := by
    rw [grading_eq_piece,AlternatingForms.homogeneousQuotient_degree_zero]
    exact Submodule.mem_one.mpr ⟨1,map_one _⟩
  mul_mem := by
    intro a b x y hx hy
    rw [grading_eq_piece] at hx hy ⊢
    exact AlternatingForms.homogeneousQuotient_mul_mem Q a b x y hx hy

/-- A genuine GradedRing instance, with the original multiplication and
original homogeneous pieces; no grading is assumed at the application. -/
instance quotientGradedAlgebra (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    GradedAlgebra (grading Q hQ) := by
  letI : SetLike.GradedMonoid (HomogeneousIdealPieces.grading Q hQ).piece :=
    quotientGradedMonoid Q hQ
  exact (HomogeneousIdealPieces.grading Q hQ).isInternal.gradedAlgebra

theorem quotient_X_mem_one (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (i : σ) :
    Ideal.Quotient.mk Q (X i)∈grading Q hQ 1 := by
  rw [grading_eq_piece]
  exact ⟨X i,isHomogeneous_X K i,rfl⟩

/-- Every surjective polynomial presentation generates the actual quotient
as an algebra, with the literal images of its variables. -/
theorem adjoin_range_variable_eq_top {τ : Type*} (Q : Ideal P)
    (F : MvPolynomial τ K →ₐ[K] (P⧸Q)) (hF : Function.Surjective F) :
    Algebra.adjoin K (Set.range (fun i ↦ F (X i)))=⊤ := by
  change Algebra.adjoin K (Set.range (F ∘ (X : τ → MvPolynomial τ K)))=⊤
  rw [Set.range_comp,Algebra.adjoin_image,adjoin_range_X,Algebra.map_top]
  exact (AlgHom.range_eq_top F).mpr hF

/-- A degree-one presentation supplies the standard cover on the actual
projective spectrum, rather than a cover imposed on a separate point model. -/
theorem presentation_basicOpen_cover {τ : Type*} (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
    (F : MvPolynomial τ K →ₐ[K] (P⧸Q)) (hF : Function.Surjective F)
    (hdeg : ∀ i,F (X i)∈grading Q hQ 1) :
    (⨆ i,Proj.basicOpen (grading Q hQ) (F (X i)))=⊤ := by
  apply Proj.iSup_basicOpen_eq_top' _ _ (fun i ↦ ⟨1,hdeg i⟩)
  apply top_unique
  intro a ha
  obtain ⟨p,rfl⟩ := hF a
  clear ha
  induction p using MvPolynomial.induction_on with
  | C c =>
      have hFC : F (C c)=Ideal.Quotient.mk Q (C c) := by
        change F (algebraMap K (MvPolynomial τ K) c)=algebraMap K (P⧸Q) c
        exact F.commutes c
      have hc : F (C c)∈grading Q hQ 0 := by
        rw [hFC,grading_eq_piece]
        refine ⟨C c, ?_, rfl⟩
        change (C c : P).IsHomogeneous 0
        exact isHomogeneous_C σ c
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (grading Q hQ 0) (Set.range (fun i ↦ F (X i))))
        ⟨F (C c),hc⟩
  | add p q hp hq =>
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i,rfl⟩)

end PaperVerification.HomogeneousQuotientProjective
end
end
end TAF_LiteralSource_0312

section TAF_LiteralSource_0313
/- Original module: PaperVerification.HomogeneousQuotientCharts -/


/-!
# The actual affine charts of a homogeneous polynomial quotient

For every homogeneous ideal Q and every coordinate p, the actual
degree-zero localization of P/Q at the class of X_p is canonically
P/(Q+(X_p-1)).  The comparison uses the existing homogeneous localization,
the proved degree-one dehomogenization isomorphism, and the ordinary
double-quotient theorem.  No radical or saturation is substituted.

Applying the actual Proj basic-open isomorphism gives a scheme
isomorphism, not only equality of field-valued points.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousQuotientCharts

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra
open PaperVerification.HomogeneousChartDehomogenization

variable {K ι : Type*} [Field K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K))
  (p : ι)

local notation "P" => MvPolynomial ι K
local notation "𝒜" => HomogeneousQuotientProjective.grading Q hQ

/-- The normalization ideal in the original quotient is exactly the
image of the literal normalization equation in the polynomial ring. -/
theorem normalizationIdeal_eq_map :
    normalizationIdeal (Ideal.Quotient.mk Q (X p))=
      (Ideal.span ({X p-1} : Set P)).map (Ideal.Quotient.mk Q) := by
  rw [normalizationIdeal,Ideal.map_span,Set.image_singleton,map_sub,map_one]

/-- The two successive literal quotients are the simultaneous quotient. -/
def normalizedQuotientEquiv :
    NormalizedRing (Ideal.Quotient.mk Q (X p)) ≃+*
      (P ⧸ (Q ⊔ Ideal.span {X p-1})) :=
  (Ideal.quotEquivOfEq (normalizationIdeal_eq_map Q p)).trans
    (DoubleQuot.quotQuotEquivQuotSup Q (Ideal.span {X p-1}))

@[simp] theorem normalizedQuotientEquiv_class (f : P) :
    normalizedQuotientEquiv Q p
      (quotientMap (Ideal.Quotient.mk Q (X p)) (Ideal.Quotient.mk Q f))=
      Ideal.Quotient.mk (Q ⊔ Ideal.span {X p-1}) f := by
  change (DoubleQuot.quotQuotEquivQuotSup Q (Ideal.span {X p-1}))
    ((Ideal.quotEquivOfEq (normalizationIdeal_eq_map Q p))
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk Q f)))=_
  rw [Ideal.quotEquivOfEq_mk]
  rfl

/-- The actual affine Proj chart ring is the original normalized
homogeneous quotient, preserving its whole scheme structure. -/
def awayQuotientChartEquiv :
    HomogeneousLocalization.Away 𝒜 (Ideal.Quotient.mk Q (X p)) ≃+*
      (P ⧸ (Q ⊔ Ideal.span {X p-1})) :=
  (awayEquivNormalized 𝒜
    (HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p)).trans
    (normalizedQuotientEquiv Q p)

/-- Its formula on each original homogeneous coordinate is exactly
X_i/X_p mapped to the class of X_i after setting X_p=1. -/
@[simp] theorem awayQuotientChartEquiv_coordinate (i : ι) :
    awayQuotientChartEquiv Q hQ p
      (fraction 𝒜 (HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p) 1
        ⟨Ideal.Quotient.mk Q (X i),
          HomogeneousQuotientProjective.quotient_X_mem_one Q hQ i⟩)=
      Ideal.Quotient.mk (Q ⊔ Ideal.span {X p-1}) (X i) := by
  rw [awayQuotientChartEquiv,RingEquiv.trans_apply,
    awayEquivNormalized_fraction,normalizedQuotientEquiv_class]

/-- The actual open subscheme D_+(X_p) of Proj(P/Q), with its full
structure sheaf, is the spectrum of the literal normalized quotient. -/
def projectiveBasicOpenIsoNormalized :
    (Proj.basicOpen 𝒜 (Ideal.Quotient.mk Q (X p))).toScheme ≅
      Spec (CommRingCat.of (P ⧸ (Q ⊔ Ideal.span {X p-1}))) :=
  Proj.basicOpenIsoSpec 𝒜 (Ideal.Quotient.mk Q (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one Q hQ p) one_pos ≪≫
    Scheme.Spec.mapIso (awayQuotientChartEquiv Q hQ p).symm.toCommRingCatIso.op

end PaperVerification.HomogeneousQuotientCharts
end
end
end TAF_LiteralSource_0313

section TAF_LiteralSource_0314
/- Original module: PaperVerification.AlternatingFormsChartUniversal -/


/-!
# Universal points of the actual common-isotropic affine charts

For every commutative algebra, including nonreduced algebras, homomorphisms
out of the displayed chart ring are naturally the row-reduced matrices
whose rows satisfy the original alternating-form restrictions.  The pivot
columns give an explicit splitting of the row embedding.  Thus the chart
describes rank-s direct summands, rather than merely a set of vectors or
field-valued isotropic planes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {s n t m : ℕ}

theorem alternatingRowPair_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] S) (f : StrictPairs n → K)
    (A : Matrix (Fin (t+2)) (Fin n) R) (i j : Fin (t+2)) :
    alternatingRowPair f (A.map φ) i j = φ (alternatingRowPair f A i j) := by
  simp only [alternatingRowPair,map_sum,map_smul,map_sub,map_mul,
    Matrix.map_apply]

/-- The literal row-reduced, common-isotropic matrices over an arbitrary
commutative coefficient algebra. -/
structure IsotropicChartPoint
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (R : Type*) [CommRing R] [Algebra K R] where
  matrix : Matrix (Fin (t+2)) (Fin n) R
  pivot : matrix.submatrix id p.val = 1
  isotropic : ∀ l i j, alternatingRowPair (forms l) matrix i j = 0

abbrev IsotropicChartRing (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :=
  MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms

def chartEntryEvaluation {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K] R :=
  aeval (fun a ↦ A a.1 a.2.val)

theorem chartEntryEvaluation_matrix {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R)
    (hp : A.submatrix id p.val=1) :
    (pluckerChartMatrix (K := K) p).map (chartEntryEvaluation (K := K) p A) = A := by
  classical
  apply Matrix.ext
  intro i j
  change chartEntryEvaluation (K := K) p A (pluckerChartMatrix (K := K) p i j)=A i j
  by_cases hj : j ∈ Set.range p.val
  · obtain ⟨r,rfl⟩ := hj
    have h₁ := congrFun (congrFun (pluckerChartMatrix_pivot (K := K) p) i) r
    simp only [Matrix.of_apply] at h₁
    have h₂ := congrFun (congrFun hp i) r
    change A i (p.val r)=(1 : Matrix (Fin s) (Fin s) R) i r at h₂
    rw [h₁,h₂]
    simp only [Matrix.one_apply,apply_ite,map_one,map_zero] <;> split_ifs <;> rfl
  · rw [pluckerChartMatrix_nonpivot p i ⟨j,hj⟩]
    simp only [chartEntryEvaluation,aeval_X]

theorem chartEntryEvaluation_kills_isotropy
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (A : IsotropicChartPoint p forms R) :
    isotropicChartIdeal p forms ≤ RingHom.ker (chartEntryEvaluation (K := K) p A.matrix).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨⟨l,ij⟩,rfl⟩
  change chartEntryEvaluation (K := K) p A.matrix
    (alternatingRowPair (forms l) (pluckerChartMatrix (K := K) p) ij.val.1 ij.val.2)=0
  rw [←alternatingRowPair_map,chartEntryEvaluation_matrix p A.matrix A.pivot]
  exact A.isotropic l ij.val.1 ij.val.2

def IsotropicChartPoint.toAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A : IsotropicChartPoint p forms R) : IsotropicChartRing p forms →ₐ[K] R :=
  Ideal.Quotient.liftₐ _ (chartEntryEvaluation (K := K) p A.matrix)
    (fun f hf ↦ chartEntryEvaluation_kills_isotropy p forms A hf)

theorem IsotropicChartPoint.toAlgHom_entry
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A : IsotropicChartPoint p forms R) (i : Fin (t+2)) (j : Fin n) :
    A.toAlgHom (Ideal.Quotient.mk (isotropicChartIdeal p forms)
      (pluckerChartMatrix (K := K) p i j)) = A.matrix i j := by
  change chartEntryEvaluation (K := K) p A.matrix (pluckerChartMatrix (K := K) p i j)=A.matrix i j
  exact congrFun (congrFun (chartEntryEvaluation_matrix p A.matrix A.pivot) i) j

def chartPointOfAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (φ : IsotropicChartRing p forms →ₐ[K] R) : IsotropicChartPoint p forms R where
  matrix := (pluckerChartMatrix (K := K) p).map
    (φ.comp (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms)))
  pivot := by
    apply Matrix.ext
    intro i j
    change φ (Ideal.Quotient.mk _ (pluckerChartMatrix (K := K) p i (p.val j))) =
      (1 : Matrix (Fin (t+2)) (Fin (t+2)) R) i j
    rw [show pluckerChartMatrix (K := K) p i (p.val j)=
      (1 : Matrix (Fin (t+2)) (Fin (t+2)) (MvPolynomial (PluckerChartVariable p) K)) i j from
      congrFun (congrFun (pluckerChartMatrix_pivot p) i) j]
    simp only [Matrix.one_apply,apply_ite,map_one,map_zero] <;> split_ifs <;> rfl
  isotropic := by
    intro l i j
    rw [alternatingRowPair_map]
    change φ (Ideal.Quotient.mk _
      (alternatingRowPair (forms l) (pluckerChartMatrix (K := K) p) i j))=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (alternatingRowPair_mem_chartIdeal p forms l i j),map_zero]

theorem chartPointOfAlgHom_toAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (φ : IsotropicChartRing p forms →ₐ[K] R) :
    (chartPointOfAlgHom p forms φ).toAlgHom=φ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro a
  change chartEntryEvaluation (K := K) p (chartPointOfAlgHom p forms φ).matrix (X a)=
    φ (Ideal.Quotient.mk _ (X a))
  rw [chartEntryEvaluation,aeval_X]
  change φ (Ideal.Quotient.mk _ (pluckerChartMatrix (K := K) p a.1 a.2.val))=_
  rw [pluckerChartMatrix_nonpivot]

theorem IsotropicChartPoint.ext_matrix
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A B : IsotropicChartPoint p forms R) (h : A.matrix=B.matrix) : A=B := by
  cases A
  cases B
  cases h
  rfl

theorem IsotropicChartPoint.ofAlgHom_toAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A : IsotropicChartPoint p forms R) : chartPointOfAlgHom p forms A.toAlgHom=A := by
  apply IsotropicChartPoint.ext_matrix
  apply Matrix.ext
  intro i j
  exact IsotropicChartPoint.toAlgHom_entry A i j

/-- The actual chart ring represents isotropic, pivot-normalized matrices
over every commutative K-algebra, with no reducedness or field assumption. -/
def isotropicChartPointEquiv
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (IsotropicChartRing p forms →ₐ[K] R) ≃ IsotropicChartPoint p forms R where
  toFun := chartPointOfAlgHom p forms
  invFun := IsotropicChartPoint.toAlgHom
  left_inv := chartPointOfAlgHom_toAlgHom p forms
  right_inv := IsotropicChartPoint.ofAlgHom_toAlgHom

theorem chartPointOfAlgHom_natural
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (φ : IsotropicChartRing p forms →ₐ[K] R) (ψ : R →ₐ[K] S) :
    (chartPointOfAlgHom p forms (ψ.comp φ)).matrix=
      ((chartPointOfAlgHom p forms φ).matrix).map ψ := by
  apply Matrix.ext
  intro i j
  rfl

/-- The pivot projection is a literal left inverse to the row embedding.
Its image is therefore a free rank-s direct summand over the arbitrary ring. -/
theorem normalized_rows_split
    {R : Type*} [CommRing R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R)
    (hp : A.submatrix id p.val=1) (v : Fin s → R) :
    (fun j ↦ (v ᵥ* A) (p.val j))=v := by
  classical
  have h : (fun j ↦ (v ᵥ* A) (p.val j))=v ᵥ* (A.submatrix id p.val) := rfl
  rw [h,hp,Matrix.vecMul_one]

theorem normalized_rows_injective
    {R : Type*} [CommRing R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R)
    (hp : A.submatrix id p.val=1) : Function.Injective (fun v ↦ v ᵥ* A) := by
  intro u v huv
  have h := congrArg (fun w : Fin n → R ↦ fun j ↦ w (p.val j)) huv
  simpa only [normalized_rows_split p A hp] using h

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0314

section TAF_LiteralSource_0315
/- Original module: PaperVerification.AlternatingFormsProjAtlas -/


/-!
# The actual common-isotropic Proj has the original row-isotropy charts

The homogeneous quotient's actual basic open subschemes are the spectra
of the full original row-isotropy ideals.  The previously constructed
universal chart point equivalence therefore describes every affine
chart over every commutative coefficient algebra, including nilpotents.
Together with the explicit normalized-coordinate transition cocycles
this identifies the original common-isotropic atlas with the actual
Proj used in the complete-section comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}

/-- The actual original quotient grading for arbitrary collections of
alternating forms, without any genericity hypothesis. -/
def isotropicProjectiveGrading (forms : Fin m → StrictPairs n → K) :
    ℕ → Submodule K
      (MvPolynomial (PluckerIndex (t+2) n) K ⧸ isotropicPluckerIdeal forms) :=
  HomogeneousQuotientProjective.grading (isotropicPluckerIdeal forms)
    (isotropicPluckerIdeal_isHomogeneous forms)

instance isotropicProjectiveGradedAlgebra
    (forms : Fin m → StrictPairs n → K) :
    GradedAlgebra (isotropicProjectiveGrading (t := t) forms) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- The actual degree-zero localization is the original affine
row-isotropy ring, with no reduction of either ideal. -/
def isotropicProjChartRingEquiv (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    HomogeneousLocalization.Away (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p)) ≃+*
      IsotropicChartRing p forms :=
  (HomogeneousQuotientCharts.awayQuotientChartEquiv
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p).trans
    (isotropicPluckerBigCellEquiv p forms).toRingEquiv

/-- The literal open subscheme of the actual homogeneous quotient's
Proj is the spectrum of the original affine row-restriction equations. -/
def isotropicProjBasicOpenIso (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
      (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p forms)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms) p ≪≫
    Scheme.Spec.mapIso (isotropicPluckerBigCellEquiv p forms).symm.toRingEquiv.toCommRingCatIso.op

/-- These are actual covering basic opens of the same projective scheme. -/
theorem isotropicProjBasicOpen_cover
    (forms : Fin m → StrictPairs n → K) :
    (⨆ p : PluckerIndex (t+2) n,
      Proj.basicOpen (isotropicProjectiveGrading (t := t) forms)
        (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (isotropicPluckerIdeal forms) (isotropicPluckerIdeal_isHomogeneous forms)
    (Ideal.Quotient.mkₐ K (isotropicPluckerIdeal forms))
    Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0315

section TAF_LiteralSource_0316
/- Original module: PaperVerification.RegularPairLocalizationIntersection -/


/-!
# A regular pair and the intersection of its two principal localizations

These statements use the actual principal ideal quotient, localization rings,
and fraction field. If x is regular and y remains regular modulo x, a power
of y cannot introduce divisibility by any power of x. In a domain, an element
of the fraction field that lies in both R[1/x] and R[1/y] therefore lies in R.

This is the algebraic extension argument needed for genuine global sections
on a homogeneous coordinate ring with a regular pair of degree-one elements.
It does not itself identify any projective sheaf or certify a paper theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.RegularPairLocalizationIntersection

variable {R : Type*} [CommRing R]

/-- Regularity in the literal principal-ideal quotient cancels one multiplier
from divisibility by the generator. -/
theorem dvd_of_regular_mod_span {x y r : R}
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (h : x ∣ y * r) : x ∣ r := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hy.left
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  simpa only [map_mul, mul_zero] using hz

/-- A regular element may be replaced by any power in this cancellation
statement, without assuming unique factorization or primality of its ideal. -/
theorem pow_dvd_mul_iff {x y : R} (hx : IsRegular x)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (a : ℕ) (r : R) : x ^ a ∣ y * r ↔ x ^ a ∣ r := by
  induction a generalizing r with
  | zero => simp
  | succ a ih =>
    constructor
    · intro h
      have hxdiv : x ∣ y * r := (dvd_pow_self x (Nat.succ_ne_zero a)).trans h
      obtain ⟨c, rfl⟩ := dvd_of_regular_mod_span hy hxdiv
      obtain ⟨d, hd⟩ := h
      have hc : y * c = x ^ a * d := hx.left (by
        change x * (y * c) = x * (x ^ a * d)
        calc
          x * (y * c) = y * (x * c) := by ring
          _ = x ^ (a + 1) * d := hd
          _ = x * (x ^ a * d) := by rw [pow_succ]; ring)
      obtain ⟨e, he⟩ := (ih c).mp ⟨d, hc⟩
      refine ⟨e, ?_⟩
      rw [he, pow_succ]
      ring
    · rintro ⟨c, hc⟩
      refine ⟨y * c, ?_⟩
      rw [hc]
      ring

/-- The exact power-divisibility consequence of a regular pair. -/
theorem pow_dvd_pow_mul_iff {x y : R} (hx : IsRegular x)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (a b : ℕ) (r : R) : x ^ a ∣ y ^ b * r ↔ x ^ a ∣ r := by
  apply pow_dvd_mul_iff hx
  simpa only [map_pow] using (IsRegular.pow b hy)

section FractionField

variable [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

theorem fractionMap_ne_zero {x : R} (hx : x ≠ 0) :
    algebraMap R F x ≠ 0 := by
  intro h
  exact hx ((IsFractionRing.injective R F) (h.trans (map_zero (algebraMap R F)).symm))

/-- Two genuine denominator representations with a regular pair force a
fraction to have denominator one. -/
theorem exists_eq_algebraMap_of_two_power_denominators
    {x y : R} (hx : x ≠ 0)
    (hy : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y))
    (z : F) (a b : ℕ) (r s : R)
    (hr : z * algebraMap R F (x ^ a) = algebraMap R F r)
    (hs : z * algebraMap R F (y ^ b) = algebraMap R F s) :
    ∃ q : R, algebraMap R F q = z := by
  have hrel : y ^ b * r = x ^ a * s := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, ← hr, ← hs]
    ring
  have hdiv : x ^ a ∣ r :=
    (pow_dvd_pow_mul_iff (isRegular_iff_ne_zero.mpr hx) hy a b r).mp ⟨s, hrel⟩
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ?_⟩
  apply mul_right_cancel₀ (fractionMap_ne_zero (F := F) (pow_ne_zero a hx))
  calc
    algebraMap R F q * algebraMap R F (x ^ a) =
        algebraMap R F (x ^ a * q) := by rw [map_mul]; ring
    _ = algebraMap R F r := congrArg (algebraMap R F) hq.symm
    _ = z * algebraMap R F (x ^ a) := hr.symm

/-- The canonical homomorphism from the actual localization away from x to
its fraction field, induced by the original algebra map. -/
def awayToFraction (x : R) (hx : x ≠ 0) : Localization.Away x →+* F :=
  IsLocalization.Away.lift x (g := algebraMap R F)
    (isUnit_iff_ne_zero.mpr (fractionMap_ne_zero hx))

@[simp]
theorem awayToFraction_algebraMap (x : R) (hx : x ≠ 0) (r : R) :
    awayToFraction (F := F) x hx (algebraMap R (Localization.Away x) r) =
      algebraMap R F r := by
  exact IsLocalization.Away.lift_eq x _ r

/-- A fraction in the image of the actual principal localization has an
actual power-denominator representation. -/
theorem exists_power_denominator_of_mem_range
    (x : R) (hx : x ≠ 0) (z : F)
    (hz : z ∈ Set.range (awayToFraction (F := F) x hx)) :
    ∃ (a : ℕ) (r : R), z * algebraMap R F (x ^ a) = algebraMap R F r := by
  obtain ⟨t, rfl⟩ := hz
  refine ⟨(IsLocalization.Away.sec x t).2, (IsLocalization.Away.sec x t).1, ?_⟩
  have h := congrArg (awayToFraction (F := F) x hx) (IsLocalization.Away.sec_spec x t)
  simpa only [map_mul, awayToFraction_algebraMap] using h

/-- A regular pair recovers the original domain as the intersection of the
images of its two actual principal localizations inside the fraction field. -/
theorem intersection_range_eq (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hregular : IsRegular (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y)) :
    Set.range (awayToFraction (F := F) x hx) ∩
        Set.range (awayToFraction (F := F) y hy) =
      Set.range (algebraMap R F) := by
  ext z
  constructor
  · rintro ⟨hzx, hzy⟩
    obtain ⟨a, r, hr⟩ := exists_power_denominator_of_mem_range x hx z hzx
    obtain ⟨b, s, hs⟩ := exists_power_denominator_of_mem_range y hy z hzy
    exact exists_eq_algebraMap_of_two_power_denominators hx hregular z a b r s hr hs
  · rintro ⟨r, rfl⟩
    exact ⟨⟨algebraMap R (Localization.Away x) r, awayToFraction_algebraMap x hx r⟩,
      ⟨algebraMap R (Localization.Away y) r, awayToFraction_algebraMap y hy r⟩⟩

end FractionField
end PaperVerification.RegularPairLocalizationIntersection
end
end
end TAF_LiteralSource_0316

section TAF_LiteralSource_0317
/- Original module: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The twisting sheaves `𝒪(n)` on `Proj`

Let `A = ⨁ᵢ 𝒜 i` be an `ℕ`-graded commutative ring and `n ∈ ℤ`. The *twisting sheaf* `𝒪(n)` on
`Proj A` is the sheaf of `𝒪_{Proj A}`-modules associated with the shifted graded module `A(n)`,
`A(n)ᵢ = A_{n + i}`. We realise it concretely: a section of `𝒪(n)` over an open `U` is a
dependent function sending each point `x ∈ U` to an element of the localization `A_x` of `A` at
the homogeneous prime `x`, which is locally a fraction `r / s` with `r` and `s` homogeneous, `s`
invertible nearby, and `deg r = deg s + n`. For `n = 0` this recovers the structure sheaf
(`AlgebraicGeometry.Proj.unitIsoTwistingSheafZero`).

The construction is adapted from Mathlib's
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean` (Jujian Zhang), which builds the
structure sheaf `AlgebraicGeometry.Proj.structureSheaf` through the same sequence `IsFraction`,
`isFractionPrelocal`, `isLocallyFraction`, a presheaf of abelian groups and its comparison with
the sheaf of types. The passage to a presheaf of modules via `PresheafOfModules.ofPresheaf`
follows `AlgebraicGeometry.StructureSheaf.moduleStructurePresheaf` in Mathlib's
`Mathlib/AlgebraicGeometry/StructureSheaf.lean` (Johan Commelin, Kim Morrison, Andrew Yang).

The fractions `r / s` form sections `AlgebraicGeometry.Proj.twistingSheaf.const`, and the
difference of two of them is again a fraction
(`AlgebraicGeometry.Proj.twistingSheaf.const_sub_const`). Every section
of `𝒪(n)` is, near each point, such a fraction on a standard open `D₊(g)` with `g` of positive
degree (`AlgebraicGeometry.Proj.twistingSheaf.locally_const_basicOpen`).

We also define the components `A_j → Γ(U, 𝒪(j))`, `r ↦ r / 1`, of the graded map
`A → ⨁ₙ Γ(Proj A, 𝒪(n))` (`AlgebraicGeometry.Proj.toTwistingSheaf`), and, over each open `U`,
the `Γ(U, 𝒪)`-bilinear multiplication `Γ(U, 𝒪(m)) × Γ(U, 𝒪(n)) → Γ(U, 𝒪(m + n))` of sections,
compatible with restriction (`AlgebraicGeometry.Proj.twistingSheaf.mul`); these are the
ingredients of `𝒪(n) ≅ 𝒪(1)^{⊗ n}` when `A` is generated in degree one.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.isLocallyFraction 𝒜 n`: the local predicate
  of being locally a fraction of degree `n`.
* `AlgebraicGeometry.Proj.twistingSheaf 𝒜 n`: the twisting sheaf `𝒪(n)` as an
  `𝒪_{Proj A}`-module.
* `AlgebraicGeometry.Proj.twistingSheaf.const`: the section `r / s` of `𝒪(n)` over an open on
  which the homogeneous element `s` does not vanish.
* `AlgebraicGeometry.Proj.toTwistingSheaf`: the map `A_j → Γ(U, 𝒪(n))`, `r ↦ r / 1`, for
  `j = n`.
* `AlgebraicGeometry.Proj.twistingSheaf.mul`: the `Γ(U, 𝒪)`-bilinear multiplication
  `Γ(U, 𝒪(m)) × Γ(U, 𝒪(n)) → Γ(U, 𝒪(m + n))`.
* `AlgebraicGeometry.Proj.unitIsoTwistingSheafZero`: the isomorphism `𝒪_{Proj A} ≅ 𝒪(0)`.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.5, the definition of `𝒪_X(n)`.
* [Stacks, Section 27.8, Proj of a graded ring](https://stacks.math.columbia.edu/tag/01M3)
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

open TopCat TopologicalSpace CategoryTheory Opposite

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum

namespace TwistingSheaf

/-- The localization of `A` at the homogeneous prime ideal of a point of `Proj A`: the stalks of
all twisting sheaves embed into it. -/
abbrev Localizations (x : ProjectiveSpectrum 𝒜) : Type u :=
  Localization.AtPrime x.asHomogeneousIdeal.toIdeal

variable {𝒜} in
/-- A dependent function on an open `U` is a *fraction of degree `n`* if it is a fixed fraction
`r / s` with `r` and `s` homogeneous, `deg r = deg s + n` and `s` outside every point of `U`. -/
def IsFraction (n : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (f : ∀ x : U, Localizations 𝒜 x.1) : Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + n) (r : 𝒜 j) (s : 𝒜 i)
    (s_nin : ∀ x : U, (s : A) ∉ x.1.asHomogeneousIdeal.toIdeal),
    ∀ x : U, f x = Localization.mk (r : A) ⟨s, s_nin x⟩

/-- Being a fraction of degree `n` is preserved by restriction to smaller opens. -/
def isFractionPrelocal (n : ℤ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Localizations 𝒜 x where
  pred f := IsFraction n f
  res := by rintro V U i f ⟨a, b, h, r, s, hs, w⟩; exact ⟨a, b, h, r, s, (hs <| i ·), (w <| i ·)⟩

/-- The local predicate of being locally a fraction of degree `n`; the sections of the twisting
sheaf `𝒪(n)` are the dependent functions satisfying it. -/
def isLocallyFraction (n : ℤ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 ↦ Localizations 𝒜 x :=
  (isFractionPrelocal 𝒜 n).sheafify

variable {𝒜}

/-- The zero function is locally a fraction of every degree. -/
theorem isLocallyFraction_zero (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (isLocallyFraction 𝒜 n).pred (0 : ∀ x : U, Localizations 𝒜 x.1) := fun x ↦ by
  -- the denominator must have degree at least `-n`, so that the numerator `0` has degree `≥ 0`
  obtain ⟨i, hi, s, hs, hsx⟩ := x.1.exists_le_mem_notMem (-n).toNat
  refine ⟨U ⊓ ProjectiveSpectrum.basicOpen 𝒜 s, ⟨x.2, hsx⟩, homOfLE inf_le_left, i,
    (i + n).toNat, by omega, 0, ⟨s, hs⟩, fun y ↦ y.2.2, fun y ↦ ?_⟩
  exact (Localization.mk_zero _).symm

theorem isLocallyFraction_add {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f g : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 n).pred f)
    (hg : (isLocallyFraction 𝒜 n).pred g) : (isLocallyFraction 𝒜 n).pred (f + g) := by
  intro x
  obtain ⟨Va, ma, ia, ia', ja, hja, ra, sa, hsa, wa⟩ := hf x
  obtain ⟨Vb, mb, ib, ib', jb, hjb, rb, sb, hsb, wb⟩ := hg x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ia' + ib', ja + ib', by push_cast; omega,
    ⟨sb * ra + sa * rb, add_mem (by simpa [add_comm] using SetLike.mul_mem_graded sb.2 ra.2)
      (by convert SetLike.mul_mem_graded sa.2 rb.2 using 2; omega)⟩,
    ⟨sa * sb, SetLike.mul_mem_graded sa.2 sb.2⟩,
    fun y h ↦ (y.1.isPrime.mem_or_mem h).elim (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩),
    fun y ↦ ?_⟩
  refine (congrArg₂ (· + ·) (wa ⟨y.1, y.2.1⟩) (wb ⟨y.1, y.2.2⟩)).trans ?_
  rw [Localization.add_mk, add_comm]
  -- both sides now have the same numerator, and the denominators `⟨sa, _⟩ * ⟨sb, _⟩` and
  -- `⟨sa * sb, _⟩` agree by `Submonoid.mk_mul_mk`, which `congr 1` closes
  congr 1

theorem isLocallyFraction_neg {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 n).pred f) :
    (isLocallyFraction 𝒜 n).pred (-f) := by
  intro x
  obtain ⟨V, m, i, a, b, h, r, s, hs, w⟩ := hf x
  exact ⟨V, m, i, a, b, h, -r, s, hs, fun y ↦
    (congrArg Neg.neg (w y)).trans (Localization.neg_mk _ _)⟩

/-- The product of a local fraction of degree `m` and a local fraction of degree `n` is a local
fraction of degree `m + n`. -/
theorem isLocallyFraction_mul {m n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f g : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 m).pred f)
    (hg : (isLocallyFraction 𝒜 n).pred g) : (isLocallyFraction 𝒜 (m + n)).pred (f * g) := by
  intro x
  obtain ⟨Va, ma, ia, ia', ja, hja, ra, sa, hsa, wa⟩ := hf x
  obtain ⟨Vb, mb, ib, ib', jb, hjb, rb, sb, hsb, wb⟩ := hg x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ia' + ib', ja + jb, by push_cast; omega,
    ⟨ra * rb, SetLike.mul_mem_graded ra.2 rb.2⟩, ⟨sa * sb, SetLike.mul_mem_graded sa.2 sb.2⟩,
    fun y h ↦ (y.1.isPrime.mem_or_mem h).elim (hsa ⟨y.1, y.2.1⟩) (hsb ⟨y.1, y.2.2⟩),
    fun y ↦ ?_⟩
  exact (congrArg₂ (· * ·) (wa ⟨y.1, y.2.1⟩) (wb ⟨y.1, y.2.2⟩)).trans (Localization.mk_mul ..)

/-- Sections of the structure sheaf of `Proj`, viewed in the localizations, are local fractions
of degree `0`. -/
theorem isLocallyFraction_val {U : Opens (ProjectiveSpectrum.top 𝒜)} (a : Γ(Proj 𝒜, U)) :
    (isLocallyFraction 𝒜 0).pred fun x ↦ (a.1 x).val := by
  intro x
  obtain ⟨V, m, i, j, r, s, hs, w⟩ := a.2 x
  exact ⟨V, m, i, j, j, by simp, r, s, hs, fun y ↦
    (congrArg HomogeneousLocalization.val (w y)).trans (HomogeneousLocalization.val_mk _)⟩

/-- Conversely, a local fraction of degree `0` takes values in the homogeneous localizations. -/
theorem exists_val_eq {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {f : ∀ x : U, Localizations 𝒜 x.1} (hf : (isLocallyFraction 𝒜 0).pred f) (x : U) :
    ∃ a : HomogeneousLocalization 𝒜 _, a.val = f x := by
  obtain ⟨V, m, i, a, b, h, r, s, hs, w⟩ := hf x
  obtain rfl : b = a := by omega
  exact ⟨.mk ⟨b, r, s, hs ⟨x, m⟩⟩, (HomogeneousLocalization.val_mk _).trans (w ⟨x, m⟩).symm⟩

variable (𝒜) in
/-- The local fractions of degree `n` on `U`, as an additive subgroup of all dependent functions
into the localizations. -/
def sectionsAddSubgroup (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Localizations 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 n).pred f}
  zero_mem' := isLocallyFraction_zero n U
  add_mem' := isLocallyFraction_add
  neg_mem' := isLocallyFraction_neg

/-- Membership in the section subgroup is the local-fraction predicate. -/
theorem mem_sectionsAddSubgroup_iff {n : ℤ} {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (f : ∀ x : U, Localizations 𝒜 x.1) :
    f ∈ sectionsAddSubgroup 𝒜 n U ↔ (isLocallyFraction 𝒜 n).pred f :=
  (Iff.rfl)

/-- Sections of the structure sheaf of `Proj` act on local fractions of degree `n` pointwise,
through the inclusions `A_{(x)} → A_x` of the homogeneous localizations. -/
instance sectionsAddSubgroup.smul (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    SMul Γ(Proj 𝒜, U) (sectionsAddSubgroup 𝒜 n U) where
  smul a f := ⟨fun x ↦ (a.1 x).val * f.1 x, by
    have := isLocallyFraction_mul (isLocallyFraction_val a) f.2
    rw [zero_add] at this
    exact this⟩

/-- The local fractions of degree `n` on `U` form a module over the sections of the structure
sheaf of `Proj` on `U`. -/
instance sectionsAddSubgroup.module (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    Module Γ(Proj 𝒜, U) (sectionsAddSubgroup 𝒜 n U) where
  one_smul f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) HomogeneousLocalization.val_one).trans (one_mul _)
  mul_smul _ _ f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) (HomogeneousLocalization.val_mul _ _)).trans (mul_assoc _ _ _)
  smul_zero _ := Subtype.ext <| funext fun _ ↦ mul_zero _
  smul_add _ _ _ := Subtype.ext <| funext fun _ ↦ mul_add _ _ _
  add_smul _ _ f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) (HomogeneousLocalization.val_add _ _)).trans (add_mul _ _ _)
  zero_smul f := Subtype.ext <| funext fun x ↦
    (congrArg (· * f.1 x) HomogeneousLocalization.val_zero).trans (zero_mul _)

variable (𝒜)

/-- The twisting sheaf `𝒪(n)` as a sheaf of types: the subsheaf of dependent functions into the
localizations which are locally fractions of degree `n`. -/
def twistingSheafInType (n : ℤ) : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 n)

/-- The twisting sheaf `𝒪(n)` as a presheaf of abelian groups. -/
def twistingPresheafInAb (n : ℤ) : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of (sectionsAddSubgroup 𝒜 n U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun f := ⟨fun x ↦ f.1 (i.unop x), (isLocallyFraction 𝒜 n).res i.unop f.1 f.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of abelian groups `𝒪(n)` has the sheaf of types `𝒪(n)` as underlying presheaf
of types. -/
def twistingPresheafInAbCompForget (n : ℤ) :
    twistingPresheafInAb 𝒜 n ⋙ forget Ab ≅ (twistingSheafInType 𝒜 n).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- The twisting sheaf `𝒪(n)` as a presheaf of modules over the structure sheaf of `Proj`. -/
def twistingPresheaf (n : ℤ) : PresheafOfModules.{u} (Proj 𝒜).ringCatSheaf.obj :=
  letI (U : (Proj 𝒜).Opensᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((twistingPresheafInAb 𝒜 n).obj U) :=
    sectionsAddSubgroup.module n U.unop
  .ofPresheaf (twistingPresheafInAb 𝒜 n) fun _ _ _ _ _ ↦ rfl

end TwistingSheaf

end ProjectiveSpectrum

open ProjectiveSpectrum.TwistingSheaf

namespace Proj

/-- The **twisting sheaf** `𝒪(n)` on `Proj A`, for `n ∈ ℤ`: the sheaf of `𝒪_{Proj A}`-modules
whose sections over `U` are the dependent functions `x ↦ f x ∈ A_x` on `U` which are locally
fractions `r / s` of homogeneous elements with `deg r = deg s + n`. -/
def twistingSheaf (n : ℤ) : (Proj 𝒜).Modules where
  val := twistingPresheaf 𝒜 n
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (TopCat.Presheaf.isSheaf_of_iso (twistingPresheafInAbCompForget 𝒜 n).symm
      (twistingSheafInType 𝒜 n).2)

namespace twistingSheaf

variable {𝒜} {n : ℤ} {U V : (Proj 𝒜).Opens}

/-- A section of `𝒪(n)` is determined by its values in the localizations. -/
@[ext]
theorem ext {s t : Γ(twistingSheaf 𝒜 n, U)} (h : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext h)

@[simp]
theorem res_apply (i : V ⟶ U) (s : Γ(twistingSheaf 𝒜 n, U)) (x : V) :
    ((twistingSheaf 𝒜 n).presheaf.map i.op s).1 x = s.1 (i x) :=
  (rfl)

@[simp]
theorem zero_apply (x : U) : (0 : Γ(twistingSheaf 𝒜 n, U)).1 x = 0 :=
  (rfl)

@[simp]
theorem add_apply (s t : Γ(twistingSheaf 𝒜 n, U)) (x : U) : (s + t).1 x = s.1 x + t.1 x :=
  (rfl)

@[simp]
theorem neg_apply (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) : (-s).1 x = -s.1 x :=
  (rfl)

@[simp]
theorem sub_apply (s t : Γ(twistingSheaf 𝒜 n, U)) (x : U) : (s - t).1 x = s.1 x - t.1 x :=
  (rfl)

/-- Sections of the structure sheaf act on sections of `𝒪(n)` pointwise, through the inclusions
`A_{(x)} → A_x` of the homogeneous localizations. -/
@[simp]
theorem smul_apply (a : Γ(Proj 𝒜, U)) (s : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (a • s).1 x = (a.1 x).val * s.1 x :=
  (rfl)

/-- The section `r / s` of `𝒪(n)` on an open `U` on which the homogeneous element `s` does not
vanish, for homogeneous `r` and `s` with `deg r = deg s + n`. -/
def const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 s) : Γ(twistingSheaf 𝒜 n, U) :=
  ⟨fun x ↦ Localization.mk r ⟨s, hU x.2⟩, fun x ↦ ⟨U, x.2, 𝟙 U, i, j, h, ⟨r, hr⟩, ⟨s, hs⟩,
    fun y ↦ hU y.2, fun _ ↦ rfl⟩⟩

@[simp]
theorem const_apply {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) (x : U) :
    (const h r s hr hs U hU).1 x = Localization.mk r ⟨s, hU x.2⟩ :=
  (rfl)

@[simp]
theorem res_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) (iVU : V ⟶ U) :
    (twistingSheaf 𝒜 n).presheaf.map iVU.op (const h r s hr hs U hU) =
      const h r s hr hs V (iVU.le.trans hU) :=
  (rfl)

@[simp]
theorem const_zero {i j : ℕ} (h : (j : ℤ) = i + n) (s : A) (hr : (0 : A) ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) : const h 0 s hr hs U hU = 0 :=
  ext fun _ ↦ Localization.mk_zero _

@[simp]
theorem neg_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : U ≤ basicOpen 𝒜 s) : -const h r s hr hs U hU = const h (-r) s (neg_mem hr) hs U hU :=
  ext fun _ ↦ Localization.neg_mk _ _

/-- Sections `r / s` and `r' / s` with the same denominator add up to `(r + r') / s`. -/
@[simp]
theorem const_add {i j : ℕ} (h : (j : ℤ) = i + n) (r r' s : A) (hr : r ∈ 𝒜 j) (hr' : r' ∈ 𝒜 j)
    (hs : s ∈ 𝒜 i) (hU : U ≤ basicOpen 𝒜 s) :
    const h r s hr hs U hU + const h r' s hr' hs U hU =
      const h (r + r') s (add_mem hr hr') hs U hU :=
  ext fun _ ↦ Localization.add_mk_self _ _ _

/-- The difference of the sections `r / s` and `r' / s'` is `(s' * r - s * r') / (s * s')`. -/
theorem const_sub_const {i j i' j' : ℕ} (h : (j : ℤ) = i + n) (h' : (j' : ℤ) = i' + n)
    {r s r' s' : A} (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i) (hr' : r' ∈ 𝒜 j') (hs' : s' ∈ 𝒜 i')
    (hU : U ≤ basicOpen 𝒜 s) (hU' : U ≤ basicOpen 𝒜 s') :
    const h r s hr hs U hU - const h' r' s' hr' hs' U hU' =
      const (i := i + i') (j := i' + j) (by push_cast; omega) (s' * r - s * r') (s * s')
        (sub_mem (SetLike.mul_mem_graded hs' hr)
          (by convert SetLike.mul_mem_graded hs hr' using 2; omega))
        (SetLike.mul_mem_graded hs hs') U
        (fun x hx ↦ by simpa [basicOpen_mul] using And.intro (hU hx) (hU' hx)) :=
  ext fun _ ↦ Localization.sub_mk ..

/-- The sections `r / s` and `r' / s'` agree if `s' * r = s * r'`. -/
theorem const_ext {i j i' j' : ℕ} {h : (j : ℤ) = i + n} {h' : (j' : ℤ) = i' + n} {r s r' s' : A}
    {hr : r ∈ 𝒜 j} {hs : s ∈ 𝒜 i} {hr' : r' ∈ 𝒜 j'} {hs' : s' ∈ 𝒜 i'} {hU : U ≤ basicOpen 𝒜 s}
    {hU' : U ≤ basicOpen 𝒜 s'} (e : s' * r = s * r') :
    const h r s hr hs U hU = const h' r' s' hr' hs' U hU' :=
  ext fun _ ↦ Localization.mk_eq_mk_iff.2 (Localization.r_of_eq e)

/-- Every section of `𝒪(n)` is locally of the form `r / s`. -/
theorem exists_const (s : Γ(twistingSheaf 𝒜 n, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    ∃ (V : (Proj 𝒜).Opens) (_ : x ∈ V) (iVU : V ⟶ U) (i j : ℕ) (h : (j : ℤ) = i + n)
      (r t : A) (hr : r ∈ 𝒜 j) (ht : t ∈ 𝒜 i) (hV : V ≤ basicOpen 𝒜 t),
      (twistingSheaf 𝒜 n).presheaf.map iVU.op s = const h r t hr ht V hV := by
  obtain ⟨V, hxV, iVU, i, j, h, r, t, ht, w⟩ := s.2 ⟨x, hx⟩
  exact ⟨V, hxV, iVU, i, j, h, r, t, r.2, t.2, fun y hy ↦ ht ⟨y, hy⟩, ext fun y ↦ w y⟩

/-- Every section of `𝒪(n)` is, near each point `x`, a fraction `r / g` on a standard open
`D₊(g)` containing `x`, with `g` homogeneous of positive degree. -/
theorem locally_const_basicOpen (s : Γ(twistingSheaf 𝒜 n, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    ∃ (i j : ℕ) (h : (j : ℤ) = i + n) (r g : A) (hr : r ∈ 𝒜 j) (hg : g ∈ 𝒜 i)
      (iU : basicOpen 𝒜 g ⟶ U), 0 < i ∧ x ∈ basicOpen 𝒜 g ∧
        (twistingSheaf 𝒜 n).presheaf.map iU.op s = const h r g hr hg _ le_rfl := by
  obtain ⟨V, hxV, iVU, i, j, h, r, t, hr, ht, hV, hs⟩ := exists_const s x hx
  -- a standard open `D₊(a) ∋ x` inside `V`, and a homogeneous component `aₘ` of `a` not in `x`
  obtain ⟨_, ⟨a, rfl⟩, hxa, haV⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen 𝒜) hxV
  obtain ⟨m, hm⟩ : ∃ m, x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 m a) := by
    simpa [basicOpen_eq_iSup_proj 𝒜 a] using hxa
  -- a homogeneous element `p` of positive degree not in `x`
  obtain ⟨l, hl, p, hp, hpx⟩ := x.exists_le_mem_notMem 1
  have hg : t * GradedRing.proj 𝒜 m a * p ∈ 𝒜 (i + m + l) :=
    SetLike.mul_mem_graded (SetLike.mul_mem_graded ht (SetLike.coe_mem _)) hp
  have hgV : basicOpen 𝒜 (t * GradedRing.proj 𝒜 m a * p) ≤ V := fun y hy ↦ by
    simp only [basicOpen_mul, Opens.mem_inf] at hy
    exact haV ((basicOpen_eq_iSup_proj 𝒜 a).ge (Opens.mem_iSup.2 ⟨m, hy.1.2⟩))
  refine ⟨i + m + l, j + m + l, by push_cast; omega, r * GradedRing.proj 𝒜 m a * p, _,
    SetLike.mul_mem_graded (SetLike.mul_mem_graded hr (SetLike.coe_mem _)) hp, hg,
    homOfLE hgV ≫ iVU, by omega, ?_, ?_⟩
  · simpa [basicOpen_mul] using ⟨⟨hV hxV, hm⟩, hpx⟩
  · rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, res_const]
    exact const_ext (by ring)

variable (𝒜 U) in
/-- The multiplication `Γ(U, 𝒪(m)) × Γ(U, 𝒪(n)) → Γ(U, 𝒪(m + n))`, bilinear over the sections of
the structure sheaf: sections are multiplied pointwise in the localizations. -/
def mul (m n : ℤ) :
    Γ(twistingSheaf 𝒜 m, U) →ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 n, U) →ₗ[Γ(Proj 𝒜, U)]
      Γ(twistingSheaf 𝒜 (m + n), U) :=
  LinearMap.mk₂ Γ(Proj 𝒜, U) (fun s t ↦ ⟨s.1 * t.1, isLocallyFraction_mul s.2 t.2⟩)
    (fun _ _ _ ↦ ext fun _ ↦ add_mul _ _ _)
    (fun _ _ _ ↦ ext fun _ ↦ mul_assoc _ _ _)
    (fun _ _ _ ↦ ext fun _ ↦ mul_add _ _ _)
    (fun _ _ _ ↦ ext fun _ ↦ mul_left_comm _ _ _)

@[simp]
theorem mul_apply {m : ℤ} (s : Γ(twistingSheaf 𝒜 m, U)) (t : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (mul 𝒜 U m n s t).1 x = s.1 x * t.1 x :=
  (rfl)

/-- The multiplication of sections of twisting sheaves is associative, pointwise in the
localizations. -/
theorem mul_assoc_apply {l m : ℤ} (s : Γ(twistingSheaf 𝒜 l, U)) (t : Γ(twistingSheaf 𝒜 m, U))
    (u : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (mul 𝒜 U (l + m) n (mul 𝒜 U l m s t) u).1 x = (mul 𝒜 U l (m + n) s (mul 𝒜 U m n t u)).1 x :=
  mul_assoc _ _ _

/-- The multiplication of sections of twisting sheaves is commutative, pointwise in the
localizations. -/
theorem mul_comm_apply {m : ℤ} (s : Γ(twistingSheaf 𝒜 m, U)) (t : Γ(twistingSheaf 𝒜 n, U))
    (x : U) : (mul 𝒜 U m n s t).1 x = (mul 𝒜 U n m t s).1 x :=
  mul_comm _ _

/-- The multiplication of sections of twisting sheaves commutes with restriction. -/
@[simp]
theorem res_mul {m : ℤ} (i : V ⟶ U) (s : Γ(twistingSheaf 𝒜 m, U))
    (t : Γ(twistingSheaf 𝒜 n, U)) :
    (twistingSheaf 𝒜 (m + n)).presheaf.map i.op (mul 𝒜 U m n s t) =
      mul 𝒜 V m n ((twistingSheaf 𝒜 m).presheaf.map i.op s)
        ((twistingSheaf 𝒜 n).presheaf.map i.op t) :=
  (rfl)

@[simp]
theorem mul_const {m : ℤ} {i j i' j' : ℕ} (h : (j : ℤ) = i + m) (h' : (j' : ℤ) = i' + n)
    (r s r' s' : A) (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i) (hr' : r' ∈ 𝒜 j') (hs' : s' ∈ 𝒜 i')
    (hU : U ≤ basicOpen 𝒜 s) (hU' : U ≤ basicOpen 𝒜 s') :
    mul 𝒜 U m n (const h r s hr hs U hU) (const h' r' s' hr' hs' U hU') =
      const (by push_cast; omega) (r * r') (s * s') (SetLike.mul_mem_graded hr hr')
        (SetLike.mul_mem_graded hs hs') U
        (fun x hx ↦ by simpa [basicOpen_mul] using And.intro (hU hx) (hU' hx)) :=
  ext fun _ ↦ Localization.mk_mul ..

end twistingSheaf

open twistingSheaf

variable {𝒜} {n : ℤ} {U V : (Proj 𝒜).Opens}

variable (𝒜) in
/-- The map `r ↦ r / 1` from the homogeneous elements of degree `j` to the sections of `𝒪(n)`,
for `j = n`. Over `U = ⊤`, these are the components of the graded map
`A → ⨁ₙ Γ(Proj A, 𝒪(n))`. -/
def toTwistingSheaf {j : ℕ} (h : (j : ℤ) = n) (U : (Proj 𝒜).Opens) :
    𝒜 j →+ Γ(twistingSheaf 𝒜 n, U) where
  toFun r := twistingSheaf.const (i := 0) (by omega) (r : A) 1 r.2 SetLike.GradedOne.one_mem U
    (by simp [basicOpen_one])
  map_zero' := twistingSheaf.ext fun _ ↦ Localization.mk_zero _
  map_add' r r' := twistingSheaf.ext fun _ ↦ (Localization.add_mk_self _ _ _).symm

theorem toTwistingSheaf_eq_const {j : ℕ} (h : (j : ℤ) = n) (U : (Proj 𝒜).Opens) (r : 𝒜 j) :
    toTwistingSheaf 𝒜 h U r = twistingSheaf.const (i := 0) (by omega) (r : A) 1 r.2
      SetLike.GradedOne.one_mem U (by simp [basicOpen_one]) :=
  (rfl)

@[simp]
theorem toTwistingSheaf_apply_apply {j : ℕ} (h : (j : ℤ) = n) (U : (Proj 𝒜).Opens) (r : 𝒜 j)
    (x : U) : (toTwistingSheaf 𝒜 h U r).1 x = Localization.mk (r : A) 1 :=
  (rfl)

/-- The sections `r / 1` are compatible with restriction. -/
@[simp]
theorem res_toTwistingSheaf {j : ℕ} (h : (j : ℤ) = n) (i : V ⟶ U) (r : 𝒜 j) :
    (twistingSheaf 𝒜 n).presheaf.map i.op (toTwistingSheaf 𝒜 h U r) =
      toTwistingSheaf 𝒜 h V r :=
  (rfl)

/-- The sections `r / 1` are multiplicative: the product of `r / 1` and `r' / 1` is
`(r * r') / 1`. -/
@[simp]
theorem mul_toTwistingSheaf {m : ℤ} {i j : ℕ} (hi : (i : ℤ) = m) (hj : (j : ℤ) = n)
    (U : (Proj 𝒜).Opens) (r : 𝒜 i) (r' : 𝒜 j) :
    mul 𝒜 U m n (toTwistingSheaf 𝒜 hi U r) (toTwistingSheaf 𝒜 hj U r') =
      toTwistingSheaf 𝒜 (by push_cast; omega) U ⟨r * r', SetLike.mul_mem_graded r.2 r'.2⟩ :=
  twistingSheaf.ext fun _ ↦ (Localization.mk_mul ..).trans (congrArg _ (Subtype.ext (mul_one 1)))

variable (𝒜) in
/-- Over every open `U`, the sections of the structure sheaf of `Proj` are the sections of
`𝒪(0)`: the inclusions `A_{(x)} → A_x` identify the local fractions of degree `0` in the
homogeneous localizations with those in the localizations. -/
def sectionsLinearEquivTwistingSheafZero (U : (Proj 𝒜).Opens) :
    Γ(Proj 𝒜, U) ≃ₗ[Γ(Proj 𝒜, U)] Γ(twistingSheaf 𝒜 0, U) where
  toFun a := ⟨fun x ↦ (a.1 x).val, isLocallyFraction_val a⟩
  map_add' a b := twistingSheaf.ext fun x ↦ HomogeneousLocalization.val_add _ _
  map_smul' a b := twistingSheaf.ext fun x ↦ HomogeneousLocalization.val_mul _ _
  invFun f := ⟨fun x ↦ (exists_val_eq f.2 x).choose, fun x ↦ by
    obtain ⟨V, m, iVU, i, j, h, r, s, hs, w⟩ := f.2 x
    obtain rfl : j = i := by omega
    refine ⟨V, m, iVU, j, r, s, hs, fun y ↦ HomogeneousLocalization.val_injective _ ?_⟩
    rw [HomogeneousLocalization.val_mk]
    exact (exists_val_eq f.2 (iVU y)).choose_spec.trans (w y)⟩
  left_inv a := Subtype.ext <| funext fun x ↦ HomogeneousLocalization.val_injective _
    (exists_val_eq (isLocallyFraction_val a) x).choose_spec
  right_inv f := twistingSheaf.ext fun x ↦ (exists_val_eq f.2 x).choose_spec

@[simp]
theorem sectionsLinearEquivTwistingSheafZero_apply_apply (U : (Proj 𝒜).Opens) (a : Γ(Proj 𝒜, U))
    (x : U) : (sectionsLinearEquivTwistingSheafZero 𝒜 U a).1 x = (a.1 x).val :=
  (rfl)

/-- The inverse of the degree-zero comparison preserves the value in each localization. -/
@[simp]
theorem sectionsLinearEquivTwistingSheafZero_symm_apply_val (U : (Proj 𝒜).Opens)
    (s : Γ(twistingSheaf 𝒜 0, U)) (x : U) :
    (((sectionsLinearEquivTwistingSheafZero 𝒜 U).symm s).1 x).val = s.1 x := by
  exact congrArg (fun t : Γ(twistingSheaf 𝒜 0, U) ↦ t.1 x)
    ((sectionsLinearEquivTwistingSheafZero 𝒜 U).apply_symm_apply s)

/-- Multiplying by the section of `𝒪(0)` corresponding to a section `a` of the structure sheaf
is the scalar multiplication by `a`, pointwise in the localizations. -/
theorem mul_sectionsLinearEquivTwistingSheafZero_apply (a : Γ(Proj 𝒜, U))
    (t : Γ(twistingSheaf 𝒜 n, U)) (x : U) :
    (mul 𝒜 U 0 n (sectionsLinearEquivTwistingSheafZero 𝒜 U a) t).1 x = (a • t).1 x :=
  (rfl)

variable (𝒜) in
/-- **The twisting sheaf `𝒪(0)` is the structure sheaf of `Proj`.** -/
def unitIsoTwistingSheafZero : SheafOfModules.unit (Proj 𝒜).ringCatSheaf ≅ twistingSheaf 𝒜 0 :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk
    (fun U ↦ (sectionsLinearEquivTwistingSheafZero 𝒜 U.unop).toModuleIso) fun _ _ _ ↦ rfl

@[simp]
theorem unitIsoTwistingSheafZero_hom_app_apply (U : (Proj 𝒜).Opens) (a : Γ(Proj 𝒜, U)) :
    Scheme.Modules.Hom.app (unitIsoTwistingSheafZero 𝒜).hom U a =
      sectionsLinearEquivTwistingSheafZero 𝒜 U a :=
  (rfl)

@[simp]
theorem unitIsoTwistingSheafZero_inv_app_apply (U : (Proj 𝒜).Opens)
    (f : Γ(twistingSheaf 𝒜 0, U)) :
    Scheme.Modules.Hom.app (unitIsoTwistingSheafZero 𝒜).inv U f =
      (sectionsLinearEquivTwistingSheafZero 𝒜 U).symm f :=
  (rfl)

end Proj

end AlgebraicGeometry
end
end
end TAF_LiteralSource_0317

section TAF_LiteralSource_0318
/- Original module: TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Sections of twisting sheaves over standard opens

Let `f` be a homogeneous element of positive degree `d` of an `ℕ`-graded commutative ring `A`.
This file computes the sections of the twisting sheaf `𝒪(n)` over the standard open `D₊(f)`:
every section is a fraction `r / fᵏ` with `r` homogeneous of degree `k * d + n`
(`AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen`), and two fractions agree on
`D₊(f)` exactly when they agree in the localization `A_f`
(`AlgebraicGeometry.Proj.twistingSheaf.const_eq_const_iff`). Together these identify
`Γ(D₊(f), 𝒪(n))` with the degree-`n` part of the `ℤ`-graded ring `A_f`. As `D₊(f) ∩ D₊(g)` is the
standard open `D₊(f g)`, they are the key input for describing the restriction maps between
standard opens as localizations, and hence for proving that `𝒪(n)` is quasi-coherent.

For `n = 0`, Mathlib obtains `Γ(D₊(f), 𝒪) = A_{(f)}` from the isomorphism
`D₊(f) ≅ Spec A_{(f)}` (`AlgebraicGeometry.Proj.basicOpenIsoSpec`). Here we argue directly with
local fractions, which works for every twist `n`, including those not divisible by `d`. The
proofs follow Mathlib's computation of the sections of the structure sheaf of `Spec` over basic
opens (`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_injective`,
`AlgebraicGeometry.StructureSheaf.exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const` and
`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_surjective` in
`Mathlib/AlgebraicGeometry/StructureSheaf.lean`): the fractions describing a section near the
points of the quasi-compact open `D₊(f)` are brought to a common form over a finite subcover, and
are then glued by `ProjectiveSpectrum.exists_mul_eq_pow_mul`, which writes a power of `f` as a
combination of their denominators through the homogeneous Nullstellensatz.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.const_eq_zero_iff`: a fraction `r / s` vanishes on a
  standard open `D₊(g)` iff `r` is killed by a power of `g`.
* `AlgebraicGeometry.Proj.twistingSheaf.const_eq_const_iff`: two fractions agree on `D₊(g)` iff
  they agree in `A_g`.
* `AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen`: every section of `𝒪(n)` over
  `D₊(f)` is a fraction `r / fᵏ`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.11.
* [Stacks, Lemma 27.10.3 (01MM)](https://stacks.math.columbia.edu/tag/01MM)
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj.twistingSheaf

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {n : ℤ} {U : (Proj 𝒜).Opens}

variable {g : A}

/-- **Fractions vanishing on a standard open.** For `g` in the irrelevant ideal, for instance
homogeneous of positive degree, the section `r / s` of `𝒪(n)` vanishes on `D₊(g)` iff `r` is
killed by a power of `g`, that is iff `r / s` vanishes in the localization `A_g`. -/
theorem const_eq_zero_iff (hg : g ∈ HomogeneousIdeal.irrelevant 𝒜) {i j : ℕ}
    (h : (j : ℤ) = i + n) {r s : A} (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : basicOpen 𝒜 g ≤ basicOpen 𝒜 s) :
    const h r s hr hs _ hU = 0 ↔ ∃ N, g ^ N * r = 0 := by
  refine ⟨fun h0 ↦ ProjectiveSpectrum.exists_pow_mul_eq_zero hg hr fun x hx ↦ ?_,
    fun ⟨N, hN⟩ ↦ ext fun x ↦ ?_⟩
  · have e := (const_apply ..).symm.trans (congr($h0.1 ⟨x, hx⟩).trans (zero_apply _))
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at e
    obtain ⟨⟨c, hc⟩, hcr⟩ := e
    exact ⟨c, hc, hcr⟩
  · refine (const_apply ..).trans (Eq.trans ?_ (zero_apply x).symm)
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨g ^ N, fun hgN ↦ x.2 (x.1.isPrime.mem_of_pow_mem N hgN)⟩, hN⟩

/-- **Equality of fractions on a standard open.** For `g` in the irrelevant ideal, for instance
homogeneous of positive degree, the sections `r / s` and `r' / s'` of `𝒪(n)` agree on `D₊(g)` iff
`s' * r - s * r'` is killed by a power of `g`, that is iff `r / s = r' / s'` in the localization
`A_g`. -/
theorem const_eq_const_iff (hg : g ∈ HomogeneousIdeal.irrelevant 𝒜) {i j i' j' : ℕ}
    (h : (j : ℤ) = i + n) (h' : (j' : ℤ) = i' + n) {r s r' s' : A} (hr : r ∈ 𝒜 j)
    (hs : s ∈ 𝒜 i) (hr' : r' ∈ 𝒜 j') (hs' : s' ∈ 𝒜 i') (hU : basicOpen 𝒜 g ≤ basicOpen 𝒜 s)
    (hU' : basicOpen 𝒜 g ≤ basicOpen 𝒜 s') :
    const h r s hr hs _ hU = const h' r' s' hr' hs' _ hU' ↔ ∃ N, g ^ N * (s' * r - s * r') = 0 := by
  rw [← sub_eq_zero, const_sub_const, const_eq_zero_iff hg]

/-- **Sections of `𝒪(n)` over a standard open.** For `f` homogeneous of positive degree `d`,
every section of `𝒪(n)` over `D₊(f)` is a fraction `r / fᵏ` with `r` homogeneous of degree
`k * d + n`. -/
theorem exists_eq_const_basicOpen {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 f)) :
    ∃ (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (r : A) (hr : r ∈ 𝒜 j),
      s = const h r (f ^ k) hr (by simpa [mul_comm] using SetLike.pow_mem_graded k hf)
        (basicOpen 𝒜 f) (fun x hx ↦ fun hfk ↦ hx (x.isPrime.mem_of_pow_mem k hfk)) := by
  -- near each point `x` of `D₊(f)`, the section `s` is a fraction `r x / g x` on `D₊(g x)`
  choose i j h r g hr hg iU hi hxg H using
    fun x : basicOpen 𝒜 f ↦ locally_const_basicOpen s x.1 x.2
  -- on `D₊(g x * g y)`, the fractions `r x / g x` and `r y / g y` agree
  have hN (x y : basicOpen 𝒜 f) : ∃ N, (g x * g y) ^ N * (g y * r x - g x * r y) = 0 := by
    have hle := (basicOpen_mul 𝒜 (g x) (g y)).le
    have e : (twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_left)).op
        ((twistingSheaf 𝒜 n).presheaf.map (iU x).op s) =
        (twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_right)).op
          ((twistingSheaf 𝒜 n).presheaf.map (iU y).op s) :=
      ext fun _ ↦ rfl
    rwa [H x, H y, res_const, res_const, const_eq_const_iff
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (by have := hi x; omega)
        (SetLike.mul_mem_graded (hg x) (hg y)))] at e
  choose N hN using hN
  -- finitely many `D₊(g x)` cover `D₊(f)`; over them, normalize to a common exponent `M`
  obtain ⟨t, ht⟩ := (isAffineOpen_basicOpen 𝒜 f hf hd).isCompact.elim_finite_subcover
    (fun x ↦ (basicOpen 𝒜 (g x) : Set (Proj 𝒜))) (fun _ ↦ (basicOpen 𝒜 _).2)
    (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  have hcover (y : basicOpen 𝒜 f) : ∃ x : t, y.1 ∈ basicOpen 𝒜 (g x) := by
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht y.2)
    exact ⟨⟨x, hxt⟩, hyx⟩
  let M := (t ×ˢ t).sup fun p ↦ N p.1 p.2
  have hnorm (x z : t) :
      g x ^ (M + 1) * (g z ^ M * r z) = g z ^ (M + 1) * (g x ^ M * r x) := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
      ((t ×ˢ t).le_sup (f := fun p ↦ N p.1 p.2) (b := ⟨z, x⟩) (by simp))
    rw [show M = N z x + c from hc]
    linear_combination (g z * g x) ^ c * hN z x
  -- the normalized fractions `(g x ^ M * r x) / g x ^ (M + 1)` glue to a fraction `R / fᵏ`
  obtain ⟨k, J, hJ, R, hR, hgR⟩ := ProjectiveSpectrum.exists_mul_eq_pow_mul (n := n) hf hd (ι := t)
    (i := fun x ↦ (M + 1) * i x) (j := fun x ↦ M * i x + j x)
    (fun x ↦ by push_cast; rw [h x]; ring)
    (fun x ↦ by simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded M (hg x)) (hr x))
    (fun x ↦ by simpa using SetLike.pow_mem_graded (M + 1) (hg x))
    (fun y hfy ↦ (hcover ⟨y, hfy⟩).imp fun x hx hgx ↦ hx (y.isPrime.mem_of_pow_mem _ hgx))
    hnorm
  refine ⟨k, J, hJ, R, hR, ext fun y ↦ ?_⟩
  obtain ⟨x, hyx⟩ := hcover y
  -- both values are fractions in the localization at `y`, by `res_apply` and `const_apply`
  have e := res_apply (iU x) s ⟨y.1, hyx⟩
  rw [H x, const_apply] at e
  refine e.symm.trans (Eq.trans ?_ (const_apply hJ R (f ^ k) hR _ _ y).symm)
  refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2
    ⟨⟨g x ^ M, fun hgM ↦ hyx (y.1.isPrime.mem_of_pow_mem M hgM)⟩, ?_⟩)
  linear_combination (hgR x).symm

end AlgebraicGeometry.Proj.twistingSheaf
end
end
end TAF_LiteralSource_0318

section TAF_LiteralSource_0319
/- Original module: PaperVerification.RegularPairProjectiveSections -/


/-!
# Genuine global sections from a degree-one regular pair

This file concerns the actual twisting sheaves on the actual projective
spectrum of a graded ring.  A cover by regular degree-one elements and a
regular pair among them imply that every global section is represented by
one homogeneous element of the original ring.  Equality of local fractions
is the existing localization equality for those sheaves; power divisibility
is the regular-pair theorem in the literal principal-ideal quotient.

The canonical maps are bijective in every nonnegative degree and preserve
the actual multiplication of twisting-sheaf sections.  Negative-degree
global sections vanish.  These statements do not replace sections by a new
algebraic definition and do not assume the desired section-ring comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.RegularPairProjectiveSections

open CategoryTheory AlgebraicGeometry
open PaperVerification.RegularPairLocalizationIntersection

universe u
variable {A : Type u} {σ I : Type*} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (x : I → A) (hx : ∀ i,x i∈𝒜 1) (hregular : ∀ i,IsRegular (x i))

include hx hregular

/-- Equality of the two restrictions gives literal cross multiplication,
because the overlap denominator is a regular element of the original ring. -/
theorem mul_eq_mul_of_restrict_eq {n : ℤ} {i j : I}
    {kᵢ kⱼ jᵢ jⱼ : ℕ}
    (hᵢ : (jᵢ : ℤ)=(kᵢ*1 : ℕ)+n) (hⱼ : (jⱼ : ℤ)=(kⱼ*1 : ℕ)+n)
    {rᵢ rⱼ : A} (hrᵢ : rᵢ∈𝒜 jᵢ) (hrⱼ : rⱼ∈𝒜 jⱼ)
    (hsᵢ : x i^kᵢ∈𝒜 (kᵢ*1)) (hsⱼ : x j^kⱼ∈𝒜 (kⱼ*1))
    (hUᵢ : Proj.basicOpen 𝒜 (x i)≤Proj.basicOpen 𝒜 (x i^kᵢ))
    (hUⱼ : Proj.basicOpen 𝒜 (x j)≤Proj.basicOpen 𝒜 (x j^kⱼ))
    (s : Γ(Proj.twistingSheaf 𝒜 n,⊤))
    (eᵢ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s=
      Proj.twistingSheaf.const hᵢ rᵢ _ hrᵢ hsᵢ _ hUᵢ)
    (eⱼ : (Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s=
      Proj.twistingSheaf.const hⱼ rⱼ _ hrⱼ hsⱼ _ hUⱼ) :
    x j^kⱼ*rᵢ=x i^kᵢ*rⱼ := by
  have hle := (Proj.basicOpen_mul 𝒜 (x i) (x j)).le
  have e : (Proj.twistingSheaf 𝒜 n).presheaf.map
      (homOfLE (hle.trans inf_le_left)).op
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s)=
      (Proj.twistingSheaf 𝒜 n).presheaf.map
      (homOfLE (hle.trans inf_le_right)).op
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s) :=
    Proj.twistingSheaf.ext fun _ ↦ rfl
  rw [eᵢ,eⱼ,Proj.twistingSheaf.res_const,Proj.twistingSheaf.res_const,
    Proj.twistingSheaf.const_eq_const_iff
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 two_pos
        (SetLike.mul_mem_graded (hx i) (hx j)))] at e
  obtain ⟨N,hN⟩ := e
  exact sub_eq_zero.mp ((((hregular i).mul (hregular j)).pow N).left.mul_left_eq_zero_iff.mp hN)

variable (hcover : (⨆ i,Proj.basicOpen 𝒜 (x i))=⊤)
  (i j : I)
  (hpair : IsRegular (Ideal.Quotient.mk (Ideal.span ({x i} : Set A)) (x j)))

include hcover hpair

/-- Every actual global section has a denominator-one representation at
every point.  A single regular pair removes the denominator globally. -/
theorem exists_forall_apply_eq {n : ℤ} (s : Γ(Proj.twistingSheaf 𝒜 n,⊤)) :
    ∃ (k d : ℕ) (_ : (d : ℤ)=k+n) (q : A),
      x i^k*q∈𝒜 d ∧ ∀ y,s.1 y=Localization.mk q 1 := by
  choose k d h r hr H using fun l : I ↦
    Proj.twistingSheaf.exists_eq_const_basicOpen (hx l) one_pos
      ((Proj.twistingSheaf 𝒜 n).presheaf.map (homOfLE le_top).op s)
  have hrel (l l' : I) : x l'^k l'*r l=x l^k l*r l' :=
    mul_eq_mul_of_restrict_eq 𝒜 x hx hregular
      (h l) (h l') (hr l) (hr l') _ _ _ _ s (H l) (H l')
  obtain ⟨q,hq⟩ :=
    (pow_dvd_pow_mul_iff (hregular i) hpair (k i) (k j) (r i)).mp
      ⟨r j,hrel i j⟩
  have hrq (l : I) : r l=x l^k l*q :=
    ((hregular i).pow (k i)).left (by
      beta_reduce
      rw [←hrel,hq]
      ring)
  refine ⟨k i,d i,by simpa using h i,q,hq ▸ hr i,fun y ↦ ?_⟩
  obtain ⟨l,hl⟩ : ∃ l,y.1∈Proj.basicOpen 𝒜 (x l) := by
    have hy : y.1∈⨆ l,Proj.basicOpen 𝒜 (x l) := by rw [hcover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  have e := Proj.twistingSheaf.res_apply
    (homOfLE (le_top (a := Proj.basicOpen 𝒜 (x l)))) s ⟨y.1,hl⟩
  rw [H l] at e
  refine e.symm.trans ((Proj.twistingSheaf.const_apply ..).trans
    (Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1,?_⟩)))
  simp [hrq l,mul_comm]

/-- All negative twists have zero actual global sections under the same
regular-pair hypotheses. -/
theorem twistingSheaf_top_eq_zero_of_neg {n : ℤ} (hn : n<0)
    (s : Γ(Proj.twistingSheaf 𝒜 n,⊤)) : s=0 := by
  obtain ⟨k,d,hd,q,hq,hs⟩ :=
    exists_forall_apply_eq 𝒜 x hx hregular hcover i j hpair s
  have hpow : x i^k∈𝒜 k := by
    simpa using SetLike.pow_mem_graded k (hx i)
  have hq0 : x i^k*q=0 := by
    rw [←DirectSum.decompose_of_mem_same 𝒜 hq,
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hpow (by omega)]
  apply Proj.twistingSheaf.ext
  intro y
  rw [hs,((hregular i).pow k).left.mul_left_eq_zero_iff.mp hq0,Localization.mk_zero]
  exact (Proj.twistingSheaf.zero_apply y).symm

/-- In every nonnegative degree the canonical original-element-to-section
map, for the actual twisting sheaf on Proj, is bijective. -/
theorem bijective_toTwistingSheaf_top (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  have hpow (k : ℕ) : x i^k∈𝒜 k := by
    simpa using SetLike.pow_mem_graded k (hx i)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_,fun s ↦ ?_⟩
  · have e := congrArg ((Proj.twistingSheaf 𝒜 d).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 (x i)))).op) hr
    rw [Proj.res_toTwistingSheaf,map_zero,Proj.toTwistingSheaf_eq_const,
      Proj.twistingSheaf.const_eq_zero_iff
        (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos (hx i))] at e
    obtain ⟨N,hN⟩ := e
    exact Subtype.ext (((hregular i).pow N).left.mul_left_eq_zero_iff.mp hN)
  · obtain ⟨k,d',hd',q,hq,hs⟩ :=
      exists_forall_apply_eq 𝒜 x hx hregular hcover i j hpair s
    have hqd : q=DirectSum.decompose 𝒜 q d := by
      refine ((hregular i).pow k).left ?_
      beta_reduce
      rw [←DirectSum.decompose_of_mem_same 𝒜 hq,
        DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 (hpow k) (by omega),
        show d'-k=d by omega]
    refine ⟨⟨q,hqd ▸ (DirectSum.decompose 𝒜 q d).2⟩,
      Proj.twistingSheaf.ext fun y ↦ ?_⟩
    exact (Proj.toTwistingSheaf_apply_apply ..).trans (hs y).symm

/-- The component isomorphism is the canonical map r ↦ r/1, not a
noncanonical isomorphism obtained by counting dimensions. -/
def homogeneousGlobalSectionsEquiv (d : ℕ) :
    𝒜 d ≃+ Γ(Proj.twistingSheaf 𝒜 d,⊤) :=
  AddEquiv.ofBijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)
    (bijective_toTwistingSheaf_top 𝒜 x hx hregular hcover i j hpair d)

@[simp] theorem homogeneousGlobalSectionsEquiv_apply (d : ℕ) (r : 𝒜 d) :
    homogeneousGlobalSectionsEquiv 𝒜 x hx hregular hcover i j hpair d r=
      Proj.toTwistingSheaf 𝒜 rfl ⊤ r := rfl

omit hx hregular hcover hpair in
/-- The component comparison respects the actual multiplication of
sections of the two twisting sheaves, in all pairs of degrees. -/
theorem toTwistingSheaf_top_mul (a b : ℕ) (r : 𝒜 a) (s : 𝒜 b) :
    Proj.twistingSheaf.mul 𝒜 ⊤ (a : ℤ) (b : ℤ)
      (Proj.toTwistingSheaf 𝒜 rfl ⊤ r)
      (Proj.toTwistingSheaf 𝒜 rfl ⊤ s)=
    Proj.toTwistingSheaf 𝒜 (by omega : ((a+b : ℕ) : ℤ)=(a : ℤ)+(b : ℤ)) ⊤
      ⟨r*s,SetLike.mul_mem_graded r.2 s.2⟩ :=
  Proj.mul_toTwistingSheaf (𝒜 := 𝒜) rfl rfl ⊤ r s

end PaperVerification.RegularPairProjectiveSections
end
end
end TAF_LiteralSource_0319

section TAF_LiteralSource_0320
/- Original module: PaperVerification.SingleGeneratorProjectiveSections -/


/-!
# Actual complete sections for a homogeneous one-generator ring

This is the projective-point boundary of the regular-pair argument.  If a
regular degree-one element covers Proj and every degree-d component is a
multiple of its d-th power by a degree-zero element, the canonical map to
actual global sections of O(d) is bijective for every d >= 0.  No vanishing
for negative twists is claimed: such a statement would be false for a point.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.SingleGeneratorProjectiveSections

open CategoryTheory AlgebraicGeometry

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (x : A) (hx : x∈𝒜 1) (hregular : IsRegular x)
  (hcover : Proj.basicOpen 𝒜 x=⊤)
  (hpieces : ∀ (d : ℕ) (r : A),r∈𝒜 d → ∃ c,c∈𝒜 0 ∧ r=c*x^d)

include hx hregular hcover hpieces

set_option backward.isDefEq.respectTransparency false in
/-- The actual degree-d section map is bijective, including degree zero. -/
theorem bijective_toTwistingSheaf_top (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun r hr ↦ ?_,fun s ↦ ?_⟩
  · have e := congrArg ((Proj.twistingSheaf 𝒜 d).presheaf.map
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 x))).op) hr
    rw [Proj.res_toTwistingSheaf,map_zero,Proj.toTwistingSheaf_eq_const,
      Proj.twistingSheaf.const_eq_zero_iff
        (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos hx)] at e
    obtain ⟨N,hN⟩ := e
    exact Subtype.ext ((hregular.pow N).left.mul_left_eq_zero_iff.mp hN)
  · obtain ⟨k,j,hj,r,hr,H⟩ := Proj.twistingSheaf.exists_eq_const_basicOpen hx one_pos
      ((Proj.twistingSheaf 𝒜 d).presheaf.map (homOfLE le_top).op s)
    obtain ⟨c,hc,hrc⟩ := hpieces j r hr
    have hj' : j=k+d := by omega
    let q := c*x^d
    have hq : q∈𝒜 d := by
      have hpow : x^d∈𝒜 d := by simpa using SetLike.pow_mem_graded d hx
      simpa only [zero_add] using SetLike.mul_mem_graded hc hpow
    have hrq : r=x^k*q := by
      rw [hrc,hj',pow_add]
      dsimp only [q]
      ring
    refine ⟨⟨q,hq⟩,Proj.twistingSheaf.ext fun y ↦ ?_⟩
    have hy : y.1∈Proj.basicOpen 𝒜 x := by rw [hcover]; trivial
    have e := Proj.twistingSheaf.res_apply
      (homOfLE (le_top (a := Proj.basicOpen 𝒜 x))) s ⟨y.1,hy⟩
    rw [H] at e
    erw [Proj.twistingSheaf.const_apply] at e
    erw [Proj.toTwistingSheaf_apply_apply]
    refine Eq.trans ?_ e
    apply Localization.mk_eq_mk_iff.mpr
    apply Localization.r_iff_exists.mpr
    refine ⟨1, ?_⟩
    simp [hrq,mul_comm]

/-- The component equivalence is the original element divided by one. -/
def homogeneousGlobalSectionsEquiv (d : ℕ) :
    𝒜 d ≃+ Γ(Proj.twistingSheaf 𝒜 d,⊤) :=
  AddEquiv.ofBijective (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)
    (bijective_toTwistingSheaf_top 𝒜 x hx hregular hcover hpieces d)

end PaperVerification.SingleGeneratorProjectiveSections
end
end
end TAF_LiteralSource_0320

section TAF_LiteralSource_0321
/- Original module: PaperVerification.PolynomialQuotientProjectiveSections -/


/-!
# Complete sections for the original one-plane polynomial quotient

The quotient ideal is proved to be zero at the application.  For at least
two variables, distinct original variables form a regular pair.  For a
single variable, homogeneous polynomials are literal scalar multiples of
its powers and the one-chart argument applies.  Thus every nonempty set
of polynomial coordinates, including a projective point, is covered.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.PolynomialQuotientProjectiveSections

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type*} [Field K]

/-- QuotientRing homogeneous polynomial in one variable is its one possible monomial. -/
theorem homogeneous_eq_single_variable [Subsingleton σ] (i : σ) (p : (MvPolynomial σ K)) (d : ℕ)
    (hp : p.IsHomogeneous d) : p=C (p.coeff (Finsupp.single i d))*X i^d := by
  classical
  rw [C_mul_X_pow_eq_monomial]
  ext m
  by_cases hm : m=Finsupp.single i d
  · subst m
    simp
  · have hdegree : m.degree≠d := by
      intro hd
      have he : m=Finsupp.single i (m i) := by
        ext j
        have hji : j=i := Subsingleton.elim _ _
        subst j
        simp
      have hmi : m i=d := by
        have hmdeg := congrArg Finsupp.degree he
        rw [Finsupp.degree_single] at hmdeg
        exact hmdeg.symm.trans hd
      exact hm (he.trans (congrArg (Finsupp.single i) hmi))
    simp only [hp.coeff_eq_zero hdegree,coeff_monomial,if_neg (Ne.symm hm)]

variable (Q : Ideal (MvPolynomial σ K)) (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
  (hbot : Q=⊥)

local notation "QuotientRing" => (MvPolynomial σ K)⧸Q
local notation "𝒜" => HomogeneousQuotientProjective.grading (K := K) Q hQ
local notation "φ" => Ideal.Quotient.mkₐ K Q

include hbot in
/-- The quotient map for the proved zero ideal is injective. -/
theorem quotientMap_injective : Function.Injective φ := by
  apply (injective_iff_map_eq_zero φ).mpr
  intro p hp
  have h : p∈Q := Ideal.Quotient.eq_zero_iff_mem.mp hp
  simpa only [hbot,Ideal.mem_bot] using h

include hbot in
theorem coordinate_ne_zero (i : σ) : φ (X i)≠0 := by
  intro h
  exact X_ne_zero i (quotientMap_injective Q hbot (h.trans (map_zero φ).symm))

include hbot in
theorem coordinate_regular (i : σ) : IsRegular (φ (X i)) := by
  haveI : Q.IsPrime := by rw [hbot]; infer_instance
  exact isRegular_iff_ne_zero.mpr (coordinate_ne_zero Q hbot i)

include hbot in
theorem coordinate_dvd_cancel (i j : σ) (hij : i≠j) (z : QuotientRing)
    (hz : φ (X i)∣φ (X j)*z) : φ (X i)∣z := by
  obtain ⟨q,hq⟩ := hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective K Q z
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mkₐ_surjective K Q q
  have he : X j*p=X i*r := quotientMap_injective Q hbot (by simpa only [map_mul] using hq)
  have hdiv : (X i : (MvPolynomial σ K))∣p := by
    rcases X_dvd_mul_iff.mp (show (X i : (MvPolynomial σ K))∣X j*p from ⟨r,he⟩) with h | h
    · exact (hij (X_dvd_X.mp h)).elim
    · exact h
  obtain ⟨r,hr⟩ := hdiv
  exact ⟨φ r,by rw [hr,map_mul]⟩

include hbot in
theorem coordinate_regular_mod (i j : σ) (hij : i≠j) :
    IsRegular (Ideal.Quotient.mk (Ideal.span ({φ (X i)} : Set QuotientRing)) (φ (X j))) := by
  let U : Ideal QuotientRing := Ideal.span ({φ (X i)} : Set QuotientRing)
  change IsRegular (Ideal.Quotient.mk U (φ (X j)))
  apply (Commute.isRegular_iff
    (fun a : QuotientRing⧸U ↦ Commute.all (Ideal.Quotient.mk U (φ (X j))) a)).mpr
  change IsSMulRegular (QuotientRing⧸U) (Ideal.Quotient.mk U (φ (X j)))
  apply IsSMulRegular.of_right_eq_zero_of_smul
    (R := QuotientRing⧸U) (M := QuotientRing⧸U)
    (r := Ideal.Quotient.mk U (φ (X j)))
  intro z hz
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply coordinate_dvd_cancel Q hbot i j hij w
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul,smul_eq_mul] using hz

theorem coordinate_cover : (⨆ i : σ,Proj.basicOpen (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (φ (X i)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    (K := K) (σ := σ) (τ := σ) Q hQ (Ideal.Quotient.mkₐ K Q)
    (Ideal.Quotient.mkₐ_surjective K Q)
    (fun i : σ ↦ by
      change Ideal.Quotient.mk Q (X i)∈𝒜 1
      exact HomogeneousQuotientProjective.quotient_X_mem_one Q hQ i)

theorem singleton_piece [Subsingleton σ] (i : σ) (d : ℕ) (r : QuotientRing) (hr : r∈𝒜 d) :
    ∃ c : QuotientRing,c∈𝒜 0 ∧ r=c*φ (X i)^d := by
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hr
  obtain ⟨p,hp,rfl⟩ := hr
  change ∃ c : QuotientRing,c∈𝒜 0 ∧ φ p=c*φ (X i)^d
  refine ⟨φ (C (p.coeff (Finsupp.single i d))),?_,?_⟩
  · rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨C _,isHomogeneous_C σ _,rfl⟩
  · have he := congrArg (fun z : MvPolynomial σ K ↦ φ z)
      (homogeneous_eq_single_variable i p d hp)
    simpa only [map_mul,map_pow] using he

set_option backward.isDefEq.respectTransparency false in
theorem singleton_coordinate_cover [Subsingleton σ] (i : σ) :
    Proj.basicOpen (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (φ (X i))=⊤ := by
  exact (ciSup_subsingleton i (fun j : σ ↦ Proj.basicOpen (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (φ (X j)))).symm.trans
    (coordinate_cover Q hQ)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
include K σ Q hQ hbot in
theorem singleton_bijective [Subsingleton σ] (i : σ) (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  exact SingleGeneratorProjectiveSections.bijective_toTwistingSheaf_top
    (A := QuotientRing) (σ := Submodule K QuotientRing)
    𝒜 (φ (X i))
    (HomogeneousQuotientProjective.quotient_X_mem_one (K := K) (σ := σ) Q hQ i)
    (coordinate_regular (K := K) (σ := σ) Q hbot i)
    (singleton_coordinate_cover (K := K) (σ := σ) Q hQ i)
    (singleton_piece (K := K) (σ := σ) Q hQ i) d

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
include K σ Q hQ hbot in
theorem pair_bijective (i j : σ) (hij : i≠j) (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  exact RegularPairProjectiveSections.bijective_toTwistingSheaf_top
    (A := QuotientRing) (σ := Submodule K QuotientRing) (I := σ)
    𝒜 (fun l : σ ↦ φ (X l))
    (HomogeneousQuotientProjective.quotient_X_mem_one (K := K) (σ := σ) Q hQ)
    (coordinate_regular (K := K) (σ := σ) Q hbot)
    (coordinate_cover (K := K) (σ := σ) Q hQ) i j
    (coordinate_regular_mod (K := K) (σ := σ) Q hbot i j hij) d

set_option backward.isDefEq.respectTransparency false in
include K σ Q hQ hbot in
/-- The genuine all-degree section comparison, including one polynomial variable. -/
theorem bijective_toTwistingSheaf_top [Nonempty σ] (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (A := QuotientRing) (σ := Submodule K QuotientRing) 𝒜 (rfl : (d : ℤ)=d) ⊤) := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty σ)
  rcases subsingleton_or_nontrivial σ with hsub | hnontrivial
  · letI := hsub
    exact singleton_bijective Q hQ hbot i d
  · letI := hnontrivial
    obtain ⟨j,hji⟩ := exists_ne i
    exact pair_bijective Q hQ hbot i j (Ne.symm hji) d

end PaperVerification.PolynomialQuotientProjectiveSections
end
end
end TAF_LiteralSource_0321

section TAF_LiteralSource_0322
/- Original module: PaperVerification.AlternatingFormsOnePlaneSections -/


/-!
# Complete sections in the original one-plane Plucker boundary

The actual one-row Plucker ideal is zero, as proved by the inverse minor
map.  The original homogeneous quotient grading therefore satisfies the
all-variable polynomial section theorem.  This includes k=0, when Proj
is a point, and every nonnegative Plucker degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

/-- Homogeneity of the actual one-plane kernel follows from its proved
vanishing; no higher-plane chart or dimension argument is needed. -/
theorem onePlane_matrixPluckerIdeal_isHomogeneous (n : ℕ) :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex 1 n) K) := by
  rw [onePlane_matrixPluckerIdeal]
  exact Ideal.IsHomogeneous.bot _

/-- The original homogeneous quotient grading for one-plane Plucker coordinates. -/
def onePlaneProjectiveGrading (k : ℕ) : ℕ → Submodule K
    (MvPolynomial (PluckerIndex 1 (2*k+1)) K⧸matrixPluckerIdeal) :=
  HomogeneousQuotientProjective.grading _ (onePlane_matrixPluckerIdeal_isHomogeneous (2*k+1))

instance onePlaneProjectiveGradedAlgebra (k : ℕ) :
    GradedAlgebra (onePlaneProjectiveGrading (K := K) k) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

/-- The canonical map to complete actual twisting-sheaf sections is an
isomorphism in every degree, for every odd ambient dimension including one. -/
theorem onePlane_bijective_toTwistingSheaf_top (k d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
      (rfl : (d : ℤ)=d) ⊤) := by
  letI : Nonempty (PluckerIndex 1 (2*k+1)) := ⟨onePlaneIndex (0 : Fin (2*k+1))⟩
  exact PolynomialQuotientProjectiveSections.bijective_toTwistingSheaf_top
    (Q := matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (hQ := onePlane_matrixPluckerIdeal_isHomogeneous (2*k+1))
    (hbot := onePlane_matrixPluckerIdeal (K := K) (n := 2*k+1)) d

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0322

section TAF_LiteralSource_0323
/- Original module: PaperVerification.HomogeneousChartOverlap -/


/-!
# Actual Proj restrictions in normalized homogeneous coordinates

For arbitrary naturally graded commutative rings, the intersection of the
actual degree-one basic opens is the localization of the normalized chart
at the second normalized coordinate. The comparison is induced by the
existing homogeneous-localization restriction map. Its compatibility with
the actual Proj structure-sheaf restriction is proved explicitly.

The other chart's homogeneous coordinates become the literal unit ratios.
All rings, quotients and localizations here retain nilpotents. This is an
uncompiled source candidate and does not assert a paper-level theorem.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousChartOverlap

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PaperVerification.HomogeneousChartDehomogenization

universe u v
variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

/-- The actual normalized chart localized at the other coordinate. -/
abbrev OverlapRing (f g : A) := Localization.Away (quotientMap f g)

/-- The original homogeneous coordinate map into this literal overlap. -/
def coordinateMap (f g : A) : A →+* OverlapRing f g :=
  (algebraMap (NormalizedRing f) (OverlapRing f g)).comp (quotientMap f)

@[simp] theorem coordinateMap_pivot (f g : A) : coordinateMap f g f = 1 := by
  rw [coordinateMap, RingHom.comp_apply, quotientMap_pivot, map_one]

/-- The second coordinate is a unit by the actual localization property. -/
theorem coordinateMap_other_isUnit (f g : A) : IsUnit (coordinateMap f g g) :=
  IsLocalization.Away.algebraMap_isUnit (S := OverlapRing f g) (quotientMap f g)

/-- The first coordinate remains the literal unit after localization. -/
theorem coordinateMap_pivot_isUnit (f g : A) : IsUnit (coordinateMap f g f) := by
  rw [coordinateMap_pivot]
  exact isUnit_one

/-- Hence the actual product basic open receives this coordinate map. -/
theorem coordinateMap_product_isUnit (f g : A) : IsUnit (coordinateMap f g (f * g)) := by
  rw [map_mul]
  exact (coordinateMap_pivot_isUnit f g).mul (coordinateMap_other_isUnit f g)

/-- Degree-one normalization sends the genuine localization element g/f
exactly to the class of g in A/(f-1). -/
theorem dehomogenize_localizationElement :
    awayEquivNormalized 𝒜 hf (Away.isLocalizationElem hf hg) = quotientMap f g := by
  change awayEquivNormalized 𝒜 hf (Away.mk 𝒜 hf 1 (g ^ 1) _) = quotientMap f g
  simpa only [pow_one,fraction] using
    awayEquivNormalized_fraction 𝒜 hf 1 (⟨g, hg⟩ : 𝒜 1)

/-- The actual multiplicative sets are carried to each other. -/
theorem powers_dehomogenize :
    (Submonoid.powers (Away.isLocalizationElem hf hg)).map
        (awayEquivNormalized 𝒜 hf).toMonoidHom =
      Submonoid.powers (quotientMap f g) := by
  rw [Submonoid.map_powers]
  congr 1
  exact dehomogenize_localizationElement 𝒜 hf hg

/-- The actual product basic-open ring, with the original awayMap algebra
structure, is the localization of the actual normalized chart. -/
def overlapEquiv : Away 𝒜 (f * g) ≃+* OverlapRing f g := by
  letI := (awayMap 𝒜 hg (rfl : f * g = f * g)).toAlgebra
  letI := Away.isLocalization_mul hf hg (rfl : f * g = f * g) one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv (Away 𝒜 (f * g)) (OverlapRing f g)
    (awayEquivNormalized 𝒜 hf) (powers_dehomogenize 𝒜 hf hg)

/-- On the original chart, this equivalence carries the genuine Proj
restriction to the canonical ordinary localization map. -/
theorem overlapEquiv_restriction (z : Away 𝒜 f) :
    overlapEquiv 𝒜 hf hg (awayMap 𝒜 hg (rfl : f * g = f * g) z) =
      algebraMap (NormalizedRing f) (OverlapRing f g) (awayEquivNormalized 𝒜 hf z) := by
  letI := (awayMap 𝒜 hg (rfl : f * g = f * g)).toAlgebra
  letI := Away.isLocalization_mul hf hg (rfl : f * g = f * g) one_ne_zero
  exact IsLocalization.ringEquivOfRingEquiv_eq (powers_dehomogenize 𝒜 hf hg) z

/-- The overlap equivalence is also the literal homogeneous-coordinate
localization lift. This identifies it on every homogeneous fraction. -/
theorem overlapEquiv_eq_lift :
    (overlapEquiv 𝒜 hf hg).toRingHom =
      Away.lift 𝒜 (coordinateMap f g) (coordinateMap_product_isUnit f g) := by
  letI := (awayMap 𝒜 hg (rfl : f * g = f * g)).toAlgebra
  letI := Away.isLocalization_mul hf hg (rfl : f * g = f * g) one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers (Away.isLocalizationElem hf hg))
  ext z
  change overlapEquiv 𝒜 hf hg (awayMap 𝒜 hg (rfl : f * g = f * g) z) =
    Away.lift 𝒜 (coordinateMap f g) (coordinateMap_product_isUnit f g)
      (awayMap 𝒜 hg (rfl : f * g = f * g) z)
  rw [overlapEquiv_restriction]
  have hfirst := RingHom.congr_fun
    ((algebraMap (NormalizedRing f) (OverlapRing f g)).comp_homogeneousLocalizationAwayLift
      (quotientMap f) (quotientMap_pivot_isUnit f)) z
  have hsecond := RingHom.congr_fun
    (Away.lift_comp_awayMap (𝒜 := 𝒜) (coordinateMap f g) hg (rfl : f * g = f * g)
      (coordinateMap_product_isUnit f g) (coordinateMap_pivot_isUnit f g)) z
  exact hfirst.trans hsecond.symm

/-- Restrict a normalized coordinate from the other chart by the actual
homogeneous-localization restriction, followed by the proved overlap comparison. -/
def otherRestriction : NormalizedRing g →+* OverlapRing f g :=
  (overlapEquiv 𝒜 hf hg).toRingHom.comp
    ((awayMap 𝒜 hf (mul_comm f g)).comp (fromQuotient 𝒜 hg))

/-- Every homogeneous coordinate has the literal ratio formula. No
restriction to field-valued points or to reduced algebras is made. -/
theorem otherRestriction_homogeneous {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    otherRestriction 𝒜 hf hg (quotientMap g a) =
      coordinateMap f g a *
        (↑((coordinateMap_other_isUnit f g).unit ^ n)⁻¹ : OverlapRing f g) := by
  change overlapEquiv 𝒜 hf hg
    (awayMap 𝒜 hf (mul_comm f g)
      (fromQuotient 𝒜 hg (quotientMap g a))) = _
  rw [fromQuotient_quotientMap, normalize_of_mem 𝒜 hg ha]
  have he := RingHom.congr_fun (overlapEquiv_eq_lift 𝒜 hf hg)
    (awayMap 𝒜 hf (mul_comm f g) (fraction 𝒜 hg n ⟨a, ha⟩))
  refine he.trans ?_
  have hr := RingHom.congr_fun
    (Away.lift_comp_awayMap (𝒜 := 𝒜) (coordinateMap f g) hf (mul_comm f g)
      (coordinateMap_product_isUnit f g) (coordinateMap_other_isUnit f g))
    (fraction 𝒜 hg n ⟨a, ha⟩)
  refine hr.trans ?_
  exact Away.lift_mk (𝒜 := 𝒜) (coordinateMap f g)
    (coordinateMap_other_isUnit f g) hg n a (by simpa using ha)

/-- Clearing the actual unit denominator gives an equality in the entire
localized ring, including its possible nilpotents. -/
theorem otherRestriction_homogeneous_mul {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    otherRestriction 𝒜 hf hg (quotientMap g a) * coordinateMap f g g ^ n =
      coordinateMap f g a := by
  rw [otherRestriction_homogeneous 𝒜 hf hg ha]
  have hu : (↑((coordinateMap_other_isUnit f g).unit ^ n) : OverlapRing f g) =
      coordinateMap f g g ^ n := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [← hu, mul_assoc, Units.inv_mul, mul_one]

/-- In particular, the chart change on degree-one coordinates is division
by the second coordinate, with the unit actually supplied by localization. -/
theorem otherRestriction_degreeOne {a : A} (ha : a ∈ 𝒜 1) :
    otherRestriction 𝒜 hf hg (quotientMap g a) =
      (↑(coordinateMap_other_isUnit f g).unit⁻¹ : OverlapRing f g) *
        coordinateMap f g a := by
  rw [otherRestriction_homogeneous 𝒜 hf hg ha]
  simp only [pow_one, mul_comm]

/-- The inverse pivot is a unit in the other chart's actual overlap map. -/
theorem otherRestriction_pivot_isUnit :
    IsUnit (otherRestriction 𝒜 hf hg (quotientMap g f)) := by
  rw [otherRestriction_degreeOne 𝒜 hf hg hf, coordinateMap_pivot, mul_one]
  exact ((coordinateMap_other_isUnit f g).unit⁻¹).isUnit

/-- The genuine Proj overlap therefore induces a ring homomorphism on
both ordinary localized normalized-chart rings. -/
def overlapTransition : OverlapRing g f →+* OverlapRing f g :=
  IsLocalization.Away.lift (S := OverlapRing g f) (quotientMap g f)
    (otherRestriction_pivot_isUnit 𝒜 hf hg)

/-- Its value on every original normalized coordinate is the same literal
ratio, now as an equality of maps between the actual affine overlap rings. -/
theorem overlapTransition_coordinate {a : A} (ha : a ∈ 𝒜 1) :
    overlapTransition 𝒜 hf hg
        (algebraMap (NormalizedRing g) (OverlapRing g f) (quotientMap g a)) =
      (↑(coordinateMap_other_isUnit f g).unit⁻¹ : OverlapRing f g) *
        coordinateMap f g a := by
  rw [overlapTransition, IsLocalization.Away.lift_eq]
  exact otherRestriction_degreeOne 𝒜 hf hg ha

/-- The actual Proj overlap is the spectrum of the literal ordinary
localized normalized chart. -/
def projectiveOverlapIso :
    (Proj.basicOpen 𝒜 (f * g)).toScheme ≅ Spec (CommRingCat.of (OverlapRing f g)) :=
  Proj.basicOpenIsoSpec 𝒜 (f * g) (SetLike.mul_mem_graded hf hg) (by decide) ≪≫
    Scheme.Spec.mapIso (overlapEquiv 𝒜 hf hg).symm.toCommRingCatIso.op

/-- Normalized-chart sections are actual sections of the Proj structure sheaf. -/
def chartSections : CommRingCat.of (NormalizedRing f) ⟶
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) :=
  CommRingCat.ofHom (fromQuotient 𝒜 hf) ≫ Proj.awayToSection 𝒜 f

/-- The analogous actual section map on the overlap. -/
def overlapSections : CommRingCat.of (OverlapRing f g) ⟶
    Γ(Proj 𝒜, Proj.basicOpen 𝒜 (f * g)) :=
  CommRingCat.ofHom (overlapEquiv 𝒜 hf hg).symm.toRingHom ≫
    Proj.awayToSection 𝒜 (f * g)

/-- The actual structure-sheaf restriction is the ordinary localization map
under the normalized-chart identifications. -/
theorem chartSections_restrict :
    chartSections 𝒜 hf ≫ (Proj 𝒜).presheaf.map
        (homOfLE (Proj.basicOpen_mono 𝒜 f (f * g) (dvd_mul_right f g))).op =
      CommRingCat.ofHom (algebraMap (NormalizedRing f) (OverlapRing f g)) ≫
        overlapSections 𝒜 hf hg := by
  rw [chartSections, Category.assoc, ← Proj.awayMap_awayToSection 𝒜 hg rfl,
    overlapSections, ← Category.assoc, ← Category.assoc]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change awayMap 𝒜 hg (rfl : f * g = f * g) (fromQuotient 𝒜 hf z) =
    (overlapEquiv 𝒜 hf hg).symm
      (algebraMap (NormalizedRing f) (OverlapRing f g) z)
  apply (overlapEquiv 𝒜 hf hg).injective
  rw [RingEquiv.apply_symm_apply, overlapEquiv_restriction]
  exact congrArg (algebraMap (NormalizedRing f) (OverlapRing f g))
    (toQuotient_fromQuotient 𝒜 hf z)

/-- The other actual structure-sheaf restriction is exactly the proved
unit-ratio map into the same overlap sections. -/
theorem otherChartSections_restrict :
    chartSections 𝒜 hg ≫ (Proj 𝒜).presheaf.map
        (homOfLE (Proj.basicOpen_mono 𝒜 g (f * g) (dvd_mul_left g f))).op =
      CommRingCat.ofHom (otherRestriction 𝒜 hf hg) ≫ overlapSections 𝒜 hf hg := by
  rw [chartSections, Category.assoc,
    ← Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g),
    overlapSections, ← Category.assoc, ← Category.assoc]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change awayMap 𝒜 hf (mul_comm f g) (fromQuotient 𝒜 hg z) =
    (overlapEquiv 𝒜 hf hg).symm
      (overlapEquiv 𝒜 hf hg (awayMap 𝒜 hf (mul_comm f g) (fromQuotient 𝒜 hg z)))
  exact ((overlapEquiv 𝒜 hf hg).symm_apply_apply _).symm

end PaperVerification.HomogeneousChartOverlap
end
end
end TAF_LiteralSource_0323

section TAF_LiteralSource_0324
/- Original module: PaperVerification.NormalizedHomogeneousChart -/


/-!
# Normalized homogeneous charts on arbitrary coefficient algebras

The points here have values in every commutative algebra, including rings
with nilpotents. A homogeneous equation is evaluated literally; its zero
locus is never replaced by its radical or by field-valued points. On the
overlap where a second coordinate is a unit, rescaling by that unit gives
the other normalized chart. The inverse, naturality under algebra maps,
and the three-chart cocycle are proved from actual coordinate identities.

This is the functor-of-points overlap construction. Identifying these
functors with particular quotient/localization algebras, and identifying
those algebras with row-isotropy charts, are separate obligations.
This new source candidate has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.NormalizedHomogeneousChart

universe u v w uA uB
variable {K : Type u} [CommRing K] {ι : Type v} {η : Type w}

/-- Literal homogeneous equations, with their proved degrees. -/
structure System (K : Type u) [CommRing K] (ι : Type v) (η : Type w) where
  degree : η → ℕ
  equation : η → MvPolynomial ι K
  homogeneous : ∀ j, (equation j).IsHomogeneous (degree j)

variable (E : System K ι η)

/-- An arbitrary-algebra point satisfying the original equations and the
literal normalization `x_p = 1`. -/
structure ChartPoint (p : ι) (A : Type uA) [CommRing A] [Algebra K A] where
  coordinate : ι → A
  normalized : coordinate p = 1
  vanishes : ∀ j, MvPolynomial.aeval coordinate (E.equation j) = 0

namespace ChartPoint

variable {E} {p : ι} {A : Type uA} [CommRing A] [Algebra K A]

@[ext] theorem ext {x y : ChartPoint E p A}
    (h : ∀ i, x.coordinate i = y.coordinate i) : x = y := by
  have hc : x.coordinate = y.coordinate := funext h
  cases x
  cases y
  cases hc
  rfl

/-- Every algebra homomorphism acts on the actual coordinates and equations. -/
def map {B : Type uB} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (x : ChartPoint E p A) : ChartPoint E p B where
  coordinate i := φ (x.coordinate i)
  normalized := by rw [x.normalized, map_one]
  vanishes j := by
    rw [← MvPolynomial.comp_aeval_apply, x.vanishes, map_zero]

@[simp] theorem map_coordinate {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : ChartPoint E p A) (i : ι) :
    (x.map φ).coordinate i = φ (x.coordinate i) := rfl

@[simp] theorem map_id (x : ChartPoint E p A) : x.map (AlgHom.id K A) = x := by
  ext i
  rfl

@[simp] theorem map_comp {B : Type uB} [CommRing B] [Algebra K B]
    {D : Type*} [CommRing D] [Algebra K D]
    (φ : A →ₐ[K] B) (ψ : B →ₐ[K] D) (x : ChartPoint E p A) :
    (x.map φ).map ψ = x.map (ψ.comp φ) := by
  ext i
  rfl

end ChartPoint

/-- The overlap remembers the unique unit whose value is the other pivot.
The unit is data only to give a literal denominator in every algebra. -/
structure Overlap (p q : ι) (A : Type uA) [CommRing A] [Algebra K A]
    extends ChartPoint E p A where
  pivot : Aˣ
  pivot_eq : (pivot : A) = coordinate q

namespace Overlap

variable {E} {p q : ι} {A : Type uA} [CommRing A] [Algebra K A]

@[ext] theorem ext {x y : Overlap E p q A}
    (h : ∀ i, x.coordinate i = y.coordinate i) : x = y := by
  have hp : x.toChartPoint = y.toChartPoint := ChartPoint.ext h
  cases x with
  | mk x u hu =>
    cases y with
    | mk y v hv =>
      cases hp
      have huv : u = v := Units.ext (hu.trans hv.symm)
      cases huv
      rfl

/-- Change to the other normalized chart by dividing every coordinate by
its actual unit-valued pivot. -/
def transition (x : Overlap E p q A) : Overlap E q p A where
  coordinate i := (↑x.pivot⁻¹ : A) * x.coordinate i
  normalized := by rw [← x.pivot_eq]; simp
  vanishes j := by
    change MvPolynomial.eval₂ (algebraMap K A)
      (fun i => (↑x.pivot⁻¹ : A) * x.coordinate i) (E.equation j) = 0
    rw [(E.homogeneous j).eval₂_const_mul]
    change (↑x.pivot⁻¹ : A) ^ E.degree j *
      MvPolynomial.aeval x.coordinate (E.equation j) = 0
    rw [x.vanishes, mul_zero]
  pivot := x.pivot⁻¹
  pivot_eq := by rw [x.normalized, mul_one]

@[simp] theorem transition_coordinate (x : Overlap E p q A) (i : ι) :
    x.transition.coordinate i = (↑x.pivot⁻¹ : A) * x.coordinate i := rfl

@[simp] theorem transition_pivot (x : Overlap E p q A) :
    x.transition.pivot = x.pivot⁻¹ := rfl

@[simp] theorem transition_transition (x : Overlap E p q A) :
    x.transition.transition = x := by
  ext i
  simp only [transition_coordinate, transition_pivot, inv_inv, ← mul_assoc]
  simp

/-- The complete normalized overlap equivalence, without a reducedness or
field hypothesis. -/
def transitionEquiv : Overlap E p q A ≃ Overlap E q p A where
  toFun := transition
  invFun := transition
  left_inv := transition_transition
  right_inv := transition_transition

/-- The overlap functor acts on units by the actual induced unit homomorphism. -/
def map {B : Type uB} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (x : Overlap E p q A) : Overlap E p q B where
  toChartPoint := x.toChartPoint.map φ
  pivot := Units.map (φ : A →* B) x.pivot
  pivot_eq := by
    simpa only [Units.coe_map, AlgHom.coe_toMonoidHom, ChartPoint.map_coordinate]
      using congrArg φ x.pivot_eq

@[simp] theorem map_coordinate {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : Overlap E p q A) (i : ι) :
    (x.map φ).coordinate i = φ (x.coordinate i) := rfl

/-- The chart change commutes with every algebra homomorphism, so it is an
isomorphism of the full algebra-valued point functors. -/
theorem transition_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : Overlap E p q A) :
    (Overlap.map φ x).transition = Overlap.map φ x.transition := by
  ext i
  change (↑(Units.map (φ : A →* B) x.pivot)⁻¹ : B) * φ (x.coordinate i) =
    φ ((↑x.pivot⁻¹ : A) * x.coordinate i)
  simp only [Units.coe_map_inv, AlgHom.coe_toMonoidHom, map_mul]

end Overlap

/-- An actual point on the common overlap of three normalized charts. -/
structure TripleOverlap (p q r : ι) (A : Type uA) [CommRing A] [Algebra K A]
    extends ChartPoint E p A where
  qPivot : Aˣ
  rPivot : Aˣ
  qPivot_eq : (qPivot : A) = coordinate q
  rPivot_eq : (rPivot : A) = coordinate r

namespace TripleOverlap

variable {E} {p q r : ι} {A : Type uA} [CommRing A] [Algebra K A]

/-- The first overlap in the three-chart calculation. -/
def first (x : TripleOverlap E p q r A) : Overlap E p q A :=
  ⟨x.toChartPoint, x.qPivot, x.qPivot_eq⟩

/-- The direct overlap from the first chart to the third. -/
def direct (x : TripleOverlap E p q r A) : Overlap E p r A :=
  ⟨x.toChartPoint, x.rPivot, x.rPivot_eq⟩

/-- In the intermediate normalized chart, the third pivot is the literal
ratio `x_r/x_q`, represented by `qPivot⁻¹ * rPivot`. -/
def second (x : TripleOverlap E p q r A) : Overlap E q r A where
  toChartPoint := x.first.transition.toChartPoint
  pivot := x.qPivot⁻¹ * x.rPivot
  pivot_eq := by
    change ((x.qPivot⁻¹ * x.rPivot : Aˣ) : A) =
      (↑x.qPivot⁻¹ : A) * x.coordinate r
    rw [Units.val_mul, x.rPivot_eq]

/-- The actual ratio cocycle: the two successive normalizations give exactly
the same third-chart coordinates as the direct normalization. -/
theorem cocycle (x : TripleOverlap E p q r A) :
    x.second.transition.toChartPoint = x.direct.transition.toChartPoint := by
  apply ChartPoint.ext
  intro i
  change (↑((x.qPivot⁻¹ * x.rPivot)⁻¹) : A) *
      ((↑x.qPivot⁻¹ : A) * x.coordinate i) =
    (↑x.rPivot⁻¹ : A) * x.coordinate i
  rw [← mul_assoc, ← Units.val_mul]
  congr 1
  apply congrArg Units.val
  simp [mul_assoc]

end TripleOverlap
end PaperVerification.NormalizedHomogeneousChart
end
end
end TAF_LiteralSource_0324

section TAF_LiteralSource_0325
/- Original module: PaperVerification.NormalizedHomogeneousChartRings -/


/-!
# Actual coordinate rings representing normalized homogeneous charts

The normalized chart is the literal polynomial quotient by the original
homogeneous equations and `X_p - 1`. Its overlap is the actual localization
away from the class of `X_q`. Both universal properties are proved as
bijections on points over every commutative coefficient algebra, naturally
in that algebra. In particular this construction retains nilpotents.

These results provide the quotient/localization interpretation of the
coordinate transitions in `NormalizedHomogeneousChart`. Identifying a
particular system with Plucker or common-isotropic equations remains a
separate specialization. This source candidate has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.NormalizedHomogeneousChart

universe u v w uA uB
variable {K : Type u} [CommRing K] {ι : Type v} {η : Type w}
variable (E : System K ι η)

/-- The full defining ideal of the actual normalized chart. -/
def chartIdeal (p : ι) : Ideal (MvPolynomial ι K) :=
  Ideal.span (Set.range E.equation) ⊔ Ideal.span {MvPolynomial.X p - 1}

/-- The actual normalized polynomial quotient, without radicalization. -/
abbrev ChartRing (p : ι) := MvPolynomial ι K ⧸ chartIdeal E p

/-- The canonical polynomial quotient homomorphism. -/
def quotientMap (p : ι) : MvPolynomial ι K →ₐ[K] ChartRing E p :=
  Ideal.Quotient.mkₐ K (chartIdeal E p)

/-- A literal coordinate in the normalized quotient. -/
def coordinate (p i : ι) : ChartRing E p := quotientMap E p (MvPolynomial.X i)

@[simp] theorem quotient_equation (p : ι) (j : η) :
    quotientMap E p (E.equation j) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_range_self j))

@[simp] theorem coordinate_normalized (p : ι) : coordinate E p p = 1 := by
  apply sub_eq_zero.mp
  change quotientMap E p (MvPolynomial.X p) - 1 = 0
  rw [← map_one (quotientMap E p), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))

/-- Substituting the quotient coordinates is exactly the quotient map. -/
theorem aeval_coordinate (p : ι) :
    MvPolynomial.aeval (coordinate E p) = quotientMap E p := by
  ext i
  exact MvPolynomial.aeval_X (coordinate E p) i

variable {E} {p q : ι} {A : Type uA} [CommRing A] [Algebra K A]

/-- Every actual normalized point annihilates the entire defining ideal. -/
theorem chartIdeal_le_ker (x : ChartPoint E p A) :
    chartIdeal E p ≤ RingHom.ker (MvPolynomial.aeval x.coordinate).toRingHom := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact x.vanishes j
  · apply Ideal.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    change MvPolynomial.aeval x.coordinate (MvPolynomial.X p - 1) = 0
    rw [map_sub, MvPolynomial.aeval_X, map_one, x.normalized, sub_self]

/-- The homomorphism defined by a normalized point, via the actual quotient
universal property. -/
def pointToHom (x : ChartPoint E p A) : ChartRing E p →ₐ[K] A :=
  Ideal.Quotient.liftₐ (chartIdeal E p) (MvPolynomial.aeval x.coordinate)
    (fun f hf => chartIdeal_le_ker x hf)

@[simp] theorem pointToHom_quotient (x : ChartPoint E p A) (f : MvPolynomial ι K) :
    pointToHom x (quotientMap E p f) = MvPolynomial.aeval x.coordinate f := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (chartIdeal E p)
      (MvPolynomial.aeval x.coordinate) (fun f hf => chartIdeal_le_ker x hf)) f

@[simp] theorem pointToHom_coordinate (x : ChartPoint E p A) (i : ι) :
    pointToHom x (coordinate E p i) = x.coordinate i := by
  rw [coordinate, pointToHom_quotient, MvPolynomial.aeval_X]

/-- Reading the coordinates of any homomorphism from the quotient produces
an actual normalized point satisfying the original equations. -/
def homToPoint (f : ChartRing E p →ₐ[K] A) : ChartPoint E p A where
  coordinate i := f (coordinate E p i)
  normalized := by rw [coordinate_normalized, map_one]
  vanishes j := by
    rw [← MvPolynomial.comp_aeval_apply, aeval_coordinate, quotient_equation, map_zero]

@[simp] theorem homToPoint_coordinate (f : ChartRing E p →ₐ[K] A) (i : ι) :
    (homToPoint f).coordinate i = f (coordinate E p i) := rfl

@[simp] theorem homToPoint_pointToHom (x : ChartPoint E p A) :
    homToPoint (pointToHom x) = x := by
  ext i
  exact pointToHom_coordinate x i

@[simp] theorem pointToHom_homToPoint (f : ChartRing E p →ₐ[K] A) :
    pointToHom (homToPoint f) = f := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change pointToHom (homToPoint f) (coordinate E p i) = f (coordinate E p i)
  rw [pointToHom_coordinate, homToPoint_coordinate]

/-- Representability of the complete normalized point functor by the
literal quotient ring, for every commutative coefficient algebra. -/
def chartPointEquiv (E : System K ι η) (p : ι) (A : Type uA)
    [CommRing A] [Algebra K A] :
    ChartPoint E p A ≃ (ChartRing E p →ₐ[K] A) where
  toFun := pointToHom
  invFun := homToPoint
  left_inv := homToPoint_pointToHom
  right_inv := pointToHom_homToPoint

/-- The quotient representation commutes with every coefficient algebra map. -/
theorem pointToHom_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : ChartPoint E p A) :
    pointToHom (x.map φ) = φ.comp (pointToHom x) := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change pointToHom (x.map φ) (coordinate E p i) =
    φ (pointToHom x (coordinate E p i))
  rw [pointToHom_coordinate, ChartPoint.map_coordinate, pointToHom_coordinate]

@[simp] theorem homToPoint_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (f : ChartRing E p →ₐ[K] A) :
    homToPoint (φ.comp f) = (homToPoint f).map φ := by
  ext i
  rfl

/-- The actual affine overlap ring is localization at the other coordinate. -/
abbrev OverlapRing (E : System K ι η) (p q : ι) :=
  Localization.Away (coordinate E p q)

/-- The canonical map from the normalized chart ring to its overlap. -/
def overlapMap (E : System K ι η) (p q : ι) :
    ChartRing E p →ₐ[K] OverlapRing E p q :=
  Algebra.algHom K (ChartRing E p) (OverlapRing E p q)

/-- The original unit-valued pivot gives exactly the invertibility required
by the localization universal property. -/
theorem pointToHom_pivot_isUnit (x : Overlap E p q A) :
    IsUnit (pointToHom x.toChartPoint (coordinate E p q)) := by
  rw [pointToHom_coordinate, ← x.pivot_eq]
  exact x.pivot.isUnit

/-- The actual localization homomorphism induced by an overlap point. -/
def overlapToHom (x : Overlap E p q A) : OverlapRing E p q →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (S := OverlapRing E p q)
    (coordinate E p q) (pointToHom_pivot_isUnit x)

@[simp] theorem overlapToHom_base (x : Overlap E p q A) (z : ChartRing E p) :
    overlapToHom x (overlapMap E p q z) = pointToHom x.toChartPoint z := by
  exact IsLocalization.Away.lift_eq (S := OverlapRing E p q)
    (coordinate E p q) (pointToHom_pivot_isUnit x) z

/-- The image of the localized coordinate is a unit under every algebra map. -/
theorem localized_pivot_isUnit (f : OverlapRing E p q →ₐ[K] A) :
    IsUnit (f (overlapMap E p q (coordinate E p q))) :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := OverlapRing E p q) (coordinate E p q)).map f

/-- Read a literal overlap point from a homomorphism out of its localization. -/
def homToOverlap (f : OverlapRing E p q →ₐ[K] A) : Overlap E p q A where
  toChartPoint := homToPoint (f.comp (overlapMap E p q))
  pivot := (localized_pivot_isUnit f).unit
  pivot_eq := (localized_pivot_isUnit f).unit_spec

@[simp] theorem homToOverlap_coordinate (f : OverlapRing E p q →ₐ[K] A) (i : ι) :
    (homToOverlap f).coordinate i = f (overlapMap E p q (coordinate E p i)) := rfl

@[simp] theorem homToOverlap_overlapToHom (x : Overlap E p q A) :
    homToOverlap (overlapToHom x) = x := by
  ext i
  rw [homToOverlap_coordinate, overlapToHom_base, pointToHom_coordinate]

@[simp] theorem overlapToHom_homToOverlap (f : OverlapRing E p q →ₐ[K] A) :
    overlapToHom (homToOverlap f) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coordinate E p q))
  apply Ideal.Quotient.algHom_ext K
  ext i
  change overlapToHom (homToOverlap f) (overlapMap E p q (coordinate E p i)) =
    f (overlapMap E p q (coordinate E p i))
  rw [overlapToHom_base, pointToHom_coordinate, homToOverlap_coordinate]

/-- The full overlap point functor is represented by the actual Away
localization, including its nonreduced coefficient algebras. -/
def overlapPointEquiv (E : System K ι η) (p q : ι) (A : Type uA)
    [CommRing A] [Algebra K A] :
    Overlap E p q A ≃ (OverlapRing E p q →ₐ[K] A) where
  toFun := overlapToHom
  invFun := homToOverlap
  left_inv := homToOverlap_overlapToHom
  right_inv := overlapToHom_homToOverlap

/-- Naturality of the actual localization representation. -/
theorem overlapToHom_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : Overlap E p q A) :
    overlapToHom (x.map φ) = φ.comp (overlapToHom x) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coordinate E p q))
  apply Ideal.Quotient.algHom_ext K
  ext i
  change overlapToHom (x.map φ) (overlapMap E p q (coordinate E p i)) =
    φ (overlapToHom x (overlapMap E p q (coordinate E p i)))
  rw [overlapToHom_base, pointToHom_coordinate, Overlap.map_coordinate,
    overlapToHom_base, pointToHom_coordinate]

@[simp] theorem homToOverlap_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (f : OverlapRing E p q →ₐ[K] A) :
    homToOverlap (φ.comp f) = (homToOverlap f).map φ := by
  ext i
  rfl

/-- The actual contravariant algebra map between the two coordinate rings
of the same overlap, obtained by normalizing the universal point. -/
def transitionHom (E : System K ι η) (p q : ι) :
    OverlapRing E q p →ₐ[K] OverlapRing E p q :=
  overlapToHom
    ((homToOverlap (AlgHom.id K (OverlapRing E p q))).transition)

/-- The ring map represents exactly the already-proved point transition. -/
theorem transitionHom_natural (f : OverlapRing E p q →ₐ[K] A) :
    overlapToHom (homToOverlap f).transition = f.comp (transitionHom E p q) := by
  have h : homToOverlap f =
      (homToOverlap (AlgHom.id K (OverlapRing E p q))).map f := by
    ext i
    rfl
  rw [h, Overlap.transition_natural]
  exact overlapToHom_natural f _

/-- The two actual transition ring maps are inverse. -/
theorem transitionHom_comp (E : System K ι η) (p q : ι) :
    (transitionHom E p q).comp (transitionHom E q p) =
      AlgHom.id K (OverlapRing E p q) := by
  rw [← transitionHom_natural (E := E) (p := q) (q := p) (transitionHom E p q)]
  simp only [transitionHom, homToOverlap_overlapToHom,
    Overlap.transition_transition, overlapToHom_homToOverlap]

/-- An actual algebra equivalence of the localized chart rings; the map on
all algebra-valued points is the literal unit-ratio normalization. -/
def transitionRingEquiv (E : System K ι η) (p q : ι) :
    OverlapRing E q p ≃ₐ[K] OverlapRing E p q :=
  AlgEquiv.ofAlgHom (transitionHom E p q) (transitionHom E q p)
    (transitionHom_comp E p q) (transitionHom_comp E q p)

/-- The overlap ring morphism has the promised literal ratio on coordinates. -/
theorem transitionHom_coordinate (E : System K ι η) (p q i : ι) :
    transitionHom E p q (overlapMap E q p (coordinate E q i)) =
      (↑(homToOverlap (AlgHom.id K (OverlapRing E p q))).pivot⁻¹ : OverlapRing E p q) *
        overlapMap E p q (coordinate E p i) := by
  simp only [transitionHom, overlapToHom_base, pointToHom_coordinate,
    Overlap.transition_coordinate, homToOverlap_coordinate, AlgHom.id_apply]

end PaperVerification.NormalizedHomogeneousChart
end
end
end TAF_LiteralSource_0325

section TAF_LiteralSource_0326
/- Original module: PaperVerification.NormalizedHomogeneousProjOverlap -/


/-!
# The genuine Proj overlap maps are the normalized-coordinate transitions

A homogeneous system is interpreted in its literal polynomial quotient.
The actual Proj overlap restriction, transported by the proved ordinary
quotient and localization equivalences, is exactly transitionHom from the
normalized all-algebra point construction. Equality is proved on the full
coordinate rings, using the original polynomial generators and coefficients.
It consequently retains all nilpotents and every commutative test algebra.

This source is an uncompiled candidate. No comparison is postulated and no
paper-level verification is asserted here.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.NormalizedHomogeneousProjOverlap

open MvPolynomial
open PaperVerification

universe u v w
variable {K : Type u} [Field K] {ι : Type v} {η : Type w}
variable (E : NormalizedHomogeneousChart.System K ι η)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original homogeneous equations generate the actual projective ideal. -/
def equationIdeal : Ideal (MvPolynomial ι K) := Ideal.span (Set.range E.equation)

/-- Its homogeneity follows from the specified degrees of the actual equations. -/
theorem equationIdeal_isHomogeneous :
    (equationIdeal E).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K) := by
  apply Ideal.homogeneous_span
  rintro a ⟨j, rfl⟩
  exact ⟨E.degree j, E.homogeneous j⟩

/-- The actual homogeneous quotient ring. -/
abbrev HomogeneousRing := MvPolynomial ι K ⧸ equationIdeal E

/-- Its canonical grading consists of images of the original polynomial pieces. -/
abbrev grading : ℕ → Submodule K (HomogeneousRing E) :=
  HomogeneousQuotientProjective.grading (equationIdeal E) (equationIdeal_isHomogeneous E)

/-- The original homogeneous coordinate in the quotient ring. -/
def homogeneousCoordinate (i : ι) : HomogeneousRing E :=
  Ideal.Quotient.mk (equationIdeal E) (MvPolynomial.X i)

 theorem homogeneousCoordinate_mem_one (i : ι) :
    homogeneousCoordinate E i ∈ grading E 1 :=
  HomogeneousQuotientProjective.quotient_X_mem_one _ _ i

/-- Double quotient identifies the genuine normalization of the original
homogeneous ring with the literal normalized-equation chart ring. -/
def normalizedEquiv (p : ι) :
    HomogeneousChartDehomogenization.NormalizedRing (homogeneousCoordinate E p) ≃+*
      NormalizedHomogeneousChart.ChartRing E p :=
  HomogeneousQuotientCharts.normalizedQuotientEquiv (equationIdeal E) p

@[simp] theorem normalizedEquiv_class (p : ι) (a : MvPolynomial ι K) :
    normalizedEquiv E p
      (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E p)
        (Ideal.Quotient.mk (equationIdeal E) a)) =
      NormalizedHomogeneousChart.quotientMap E p a :=
  HomogeneousQuotientCharts.normalizedQuotientEquiv_class (equationIdeal E) p a

/-- In particular, the second homogeneous coordinate becomes the literal
second coordinate of the normalized chart. -/
theorem normalizedEquiv_coordinate (p q : ι) :
    normalizedEquiv E p
      (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E p)
        (homogeneousCoordinate E q)) =
      NormalizedHomogeneousChart.coordinate E p q :=
  normalizedEquiv_class E p (MvPolynomial.X q)

/-- Ordinary localization transports this same double-quotient equivalence. -/
def localizedEquiv (p q : ι) :
    HomogeneousChartOverlap.OverlapRing (homogeneousCoordinate E p) (homogeneousCoordinate E q) ≃+*
      NormalizedHomogeneousChart.OverlapRing E p q :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (HomogeneousChartDehomogenization.quotientMap
      (homogeneousCoordinate E p) (homogeneousCoordinate E q)))
    (T := Submonoid.powers (NormalizedHomogeneousChart.coordinate E p q))
    _ _ (normalizedEquiv E p) (by
    rw [Submonoid.map_powers]
    congr 1 <;> exact normalizedEquiv_coordinate E p q)

/-- This comparison is the actual ordinary localization map on every
normalized polynomial class. -/
theorem localizedEquiv_class (p q : ι) (a : MvPolynomial ι K) :
    localizedEquiv E p q
      (algebraMap _ (HomogeneousChartOverlap.OverlapRing
        (homogeneousCoordinate E p) (homogeneousCoordinate E q))
        (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E p)
          (Ideal.Quotient.mk (equationIdeal E) a))) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.quotientMap E p a) := by
  rw [localizedEquiv, IsLocalization.ringEquivOfRingEquiv_eq, normalizedEquiv_class]
  rfl

/-- The transition obtained from the actual Proj restriction maps, conjugated
by the two proven normalized overlap equivalences. -/
def actualTransition (p q : ι) :
    NormalizedHomogeneousChart.OverlapRing E q p →+*
      NormalizedHomogeneousChart.OverlapRing E p q :=
  (localizedEquiv E p q).toRingHom.comp
    ((HomogeneousChartOverlap.overlapTransition (grading E)
      (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)).comp
      (localizedEquiv E q p).symm.toRingHom)

/-- Its value on a normalized polynomial class uses exactly the genuine
other-chart restriction, not a separately imposed coordinate rule. -/
theorem actualTransition_class (p q : ι) (a : MvPolynomial ι K) :
    actualTransition E p q
      (NormalizedHomogeneousChart.overlapMap E q p
        (NormalizedHomogeneousChart.quotientMap E q a)) =
      localizedEquiv E p q
        (HomogeneousChartOverlap.otherRestriction (grading E)
          (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)
          (HomogeneousChartDehomogenization.quotientMap (homogeneousCoordinate E q)
            (Ideal.Quotient.mk (equationIdeal E) a))) := by
  rw [← localizedEquiv_class E q p a]
  change localizedEquiv E p q
    (HomogeneousChartOverlap.overlapTransition (grading E)
      (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)
      ((localizedEquiv E q p).symm (localizedEquiv E q p _))) = _
  rw [RingEquiv.symm_apply_apply, HomogeneousChartOverlap.overlapTransition,
    IsLocalization.Away.lift_eq]

/-- A degree-zero coefficient is unchanged by the actual transition. -/
theorem actualTransition_constant (p q : ι) (c : K) :
    actualTransition E p q
      (NormalizedHomogeneousChart.overlapMap E q p
        (NormalizedHomogeneousChart.quotientMap E q (MvPolynomial.C c))) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.quotientMap E p (MvPolynomial.C c)) := by
  rw [actualTransition_class]
  have hc : Ideal.Quotient.mk (equationIdeal E) (MvPolynomial.C c) ∈ grading E 0 := by
    rw [grading,HomogeneousQuotientProjective.grading_eq_piece]
    refine ⟨MvPolynomial.C c, ?_, rfl⟩
    change (MvPolynomial.C c : MvPolynomial ι K) ∈ MvPolynomial.homogeneousSubmodule ι K 0
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_C ι c
  rw [HomogeneousChartOverlap.otherRestriction_homogeneous (grading E)
    (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q) hc]
  simp only [pow_zero, inv_one, Units.val_one, mul_one]
  exact localizedEquiv_class E p q (MvPolynomial.C c)

/-- Clearing the localized coordinate in the actual Proj transition gives
the original normalized coordinate. This equality is in the full ring. -/
theorem actualTransition_coordinate_mul (p q i : ι) :
    actualTransition E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i)) *
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p q) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p i) := by
  simp only [NormalizedHomogeneousChart.coordinate]
  rw [actualTransition_class]
  have hm := congrArg (localizedEquiv E p q)
    (HomogeneousChartOverlap.otherRestriction_homogeneous_mul (grading E)
      (homogeneousCoordinate_mem_one E p) (homogeneousCoordinate_mem_one E q)
      (homogeneousCoordinate_mem_one E i))
  rw [map_mul, pow_one] at hm
  have hcoordinate (j : ι) :
      localizedEquiv E p q
        (HomogeneousChartOverlap.coordinateMap (homogeneousCoordinate E p)
          (homogeneousCoordinate E q) (homogeneousCoordinate E j)) =
        NormalizedHomogeneousChart.overlapMap E p q
          (NormalizedHomogeneousChart.coordinate E p j) :=
    localizedEquiv_class E p q (MvPolynomial.X j)
  rw [hcoordinate q,hcoordinate i] at hm
  exact hm

/-- The universal normalized-coordinate transition satisfies the identical
actual equality after clearing the unit pivot. -/
theorem normalizedTransition_coordinate_mul (p q i : ι) :
    NormalizedHomogeneousChart.transitionHom E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i)) *
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p q) =
      NormalizedHomogeneousChart.overlapMap E p q
        (NormalizedHomogeneousChart.coordinate E p i) := by
  let x := NormalizedHomogeneousChart.homToOverlap
    (AlgHom.id K (NormalizedHomogeneousChart.OverlapRing E p q))
  rw [NormalizedHomogeneousChart.transitionHom_coordinate]
  change ((↑x.pivot⁻¹ : NormalizedHomogeneousChart.OverlapRing E p q) * x.coordinate i) *
    x.coordinate q = x.coordinate i
  rw [← x.pivot_eq, mul_right_comm, Units.inv_mul, one_mul]

set_option maxRecDepth 2048 in
/-- The actual Proj transition and the previously constructed all-algebra
point transition are the same homomorphism of complete overlap rings. -/
theorem actualTransition_eq_transitionHom (p q : ι) :
    actualTransition E p q = (NormalizedHomogeneousChart.transitionHom E p q).toRingHom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (NormalizedHomogeneousChart.coordinate E q p))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change actualTransition E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.quotientMap E q (MvPolynomial.C c))) =
      NormalizedHomogeneousChart.transitionHom E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.quotientMap E q (MvPolynomial.C c)))
    rw [actualTransition_constant]
    change algebraMap K (NormalizedHomogeneousChart.OverlapRing E p q) c =
      NormalizedHomogeneousChart.transitionHom E p q
        (algebraMap K (NormalizedHomogeneousChart.OverlapRing E q p) c)
    exact (AlgHom.commutes (NormalizedHomogeneousChart.transitionHom E p q) c).symm
  · intro i
    change actualTransition E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i)) =
      NormalizedHomogeneousChart.transitionHom E p q
        (NormalizedHomogeneousChart.overlapMap E q p
          (NormalizedHomogeneousChart.coordinate E q i))
    apply (IsLocalization.Away.algebraMap_isUnit
      (S := NormalizedHomogeneousChart.OverlapRing E p q)
      (NormalizedHomogeneousChart.coordinate E p q)).mul_right_cancel
    exact (actualTransition_coordinate_mul E p q i).trans
      (normalizedTransition_coordinate_mul E p q i).symm

/-- In particular, the actual transition induces exactly the original
unit-ratio map on every commutative coefficient algebra, including rings
with nilpotents. -/
theorem actualTransition_on_all_algebra_points {B : Type*} [CommRing B] [Algebra K B]
    (p q : ι) (φ : NormalizedHomogeneousChart.OverlapRing E p q →ₐ[K] B) :
    φ.toRingHom.comp (actualTransition E p q) =
      (NormalizedHomogeneousChart.overlapToHom
        (NormalizedHomogeneousChart.homToOverlap φ).transition).toRingHom := by
  rw [actualTransition_eq_transitionHom]
  exact congrArg AlgHom.toRingHom
    (NormalizedHomogeneousChart.transitionHom_natural φ).symm

end PaperVerification.NormalizedHomogeneousProjOverlap
end
end
end TAF_LiteralSource_0326

section TAF_LiteralSource_0327
/- Original module: PaperVerification.HomogeneousIdealChartSystem -/


/-!
# The normalized chart system of the original homogeneous ideal

Every homogeneous element of Q is used as a literal equation, together with
its degree.  Homogeneity proves that these equations generate exactly Q.
Thus the generic normalized-chart and genuine Proj-overlap constructions
apply to the original ideal, without replacing it by its radical or by an
ideal inferred from field-valued points.  The original quotient, grading,
projective scheme, and normalized chart rings are compared explicitly.

This is an uncompiled source candidate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousIdealChartSystem

open MvPolynomial AlgebraicGeometry CategoryTheory
open PaperVerification

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K ι : Type*} [Field K]
  (Q : Ideal (MvPolynomial ι K))
  (hQ : Q.IsHomogeneous (homogeneousSubmodule ι K))

local notation "P" => MvPolynomial ι K

/-- Every equation remembers both its literal polynomial and a proved degree. -/
def EquationIndex := Σ d : ℕ, {p : P // p∈Q ∧ p.IsHomogeneous d}

/-- The canonical system of original homogeneous equations. -/
def system : NormalizedHomogeneousChart.System K ι (EquationIndex Q) where
  degree j := j.1
  equation j := j.2.val
  homogeneous j := j.2.property.2

include hQ in
/-- The full original homogeneous ideal, without any saturation or reduction,
is generated by these actual equations. -/
theorem equationIdeal_eq :
    NormalizedHomogeneousProjOverlap.equationIdeal (system Q)=Q := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨j,rfl⟩
    exact j.2.property.1
  · obtain ⟨S,hS⟩ :=
      (Ideal.IsHomogeneous.iff_exists (homogeneousSubmodule ι K) Q).mp hQ
    calc
      Q=Ideal.span ((↑) '' S) := hS
      _≤NormalizedHomogeneousProjOverlap.equationIdeal (system Q) := by
        apply Ideal.span_le.mpr
        rintro p ⟨a,ha,rfl⟩
        obtain ⟨d,hd⟩ := a.property
        have haQ : (a : P)∈Q := by
          rw [hS]
          exact Ideal.subset_span ⟨a,ha,rfl⟩
        exact Ideal.subset_span ⟨⟨d,⟨a,haQ,hd⟩⟩,rfl⟩

include hQ in
/-- Vanishing of the displayed system means annihilating the entire original
ideal, over every commutative coefficient algebra. -/
theorem equations_vanish_iff {R : Type*} [CommRing R] [Algebra K R]
    (x : ι → R) :
    (∀ j,MvPolynomial.aeval x ((system Q).equation j)=0) ↔
      Q≤RingHom.ker (MvPolynomial.aeval x).toRingHom := by
  constructor
  · intro hx
    rw [←equationIdeal_eq Q hQ]
    apply Ideal.span_le.mpr
    rintro p ⟨j,rfl⟩
    exact hx j
  · intro hx j
    exact hx j.2.property.1

/-- The homogeneous quotient comparison preserves every polynomial class. -/
def quotientEquiv :
    NormalizedHomogeneousProjOverlap.HomogeneousRing (system Q) ≃ₐ[K] (P⧸Q) :=
  Ideal.quotientEquivAlgOfEq K (equationIdeal_eq Q hQ)

@[simp] theorem quotientEquiv_class (p : P) :
    quotientEquiv Q hQ
      (Ideal.Quotient.mk
        (NormalizedHomogeneousProjOverlap.equationIdeal (system Q)) p)=
      Ideal.Quotient.mk Q p :=
  Ideal.quotientEquivAlgOfEq_mk K (equationIdeal_eq Q hQ) p

/-- The comparison respects precisely the original homogeneous pieces. -/
theorem quotientEquiv_mem_degree_iff (d : ℕ)
    (x : NormalizedHomogeneousProjOverlap.HomogeneousRing (system Q)) :
    quotientEquiv Q hQ x∈HomogeneousQuotientProjective.grading Q hQ d ↔
      x∈NormalizedHomogeneousProjOverlap.grading (system Q) d := by
  change quotientEquiv Q hQ x∈HomogeneousQuotientProjective.grading Q hQ d ↔
    x∈HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece,
    HomogeneousQuotientProjective.grading_eq_piece]
  constructor
  · rintro ⟨p,hp,he⟩
    refine ⟨p,hp,(quotientEquiv Q hQ).injective ?_⟩
    change quotientEquiv Q hQ (Ideal.Quotient.mk _ p)=quotientEquiv Q hQ x
    rw [quotientEquiv_class]
    exact he
  · rintro ⟨p,hp,rfl⟩
    change quotientEquiv Q hQ (Ideal.Quotient.mk _ p)∈HomogeneousIdealPieces.piece Q d
    rw [quotientEquiv_class]
    exact ⟨p,hp,rfl⟩

/-- Equality holds already for the homogeneous ideals with their full
structure, so their actual projective spectra are the same scheme. -/
theorem projectiveScheme_eq :
    Proj (NormalizedHomogeneousProjOverlap.grading (system Q))=
      Proj (HomogeneousQuotientProjective.grading Q hQ) := by
  have hI :
      (⟨NormalizedHomogeneousProjOverlap.equationIdeal (system Q),
        NormalizedHomogeneousProjOverlap.equationIdeal_isHomogeneous (system Q)⟩ :
        HomogeneousIdeal (homogeneousSubmodule ι K))=⟨Q,hQ⟩ := by
    ext1
    exact equationIdeal_eq Q hQ
  let F : HomogeneousIdeal (homogeneousSubmodule ι K) → Scheme := fun I ↦
    Proj (HomogeneousQuotientProjective.grading I.toIdeal I.isHomogeneous)
  change F ⟨NormalizedHomogeneousProjOverlap.equationIdeal (system Q),
    NormalizedHomogeneousProjOverlap.equationIdeal_isHomogeneous (system Q)⟩=F ⟨Q,hQ⟩
  exact congrArg F hI

def projectiveSchemeIso :
    Proj (NormalizedHomogeneousProjOverlap.grading (system Q)) ≅
      Proj (HomogeneousQuotientProjective.grading Q hQ) :=
  eqToIso (projectiveScheme_eq Q hQ)

include hQ in
/-- The normalized equations also retain the exact original chart ideal. -/
theorem chartIdeal_eq (p : ι) :
    NormalizedHomogeneousChart.chartIdeal (system Q) p=
      Q⊔Ideal.span {X p-1} := by
  change NormalizedHomogeneousProjOverlap.equationIdeal (system Q)⊔_=Q⊔_
  rw [equationIdeal_eq Q hQ]

def chartEquiv (p : ι) :
    NormalizedHomogeneousChart.ChartRing (system Q) p ≃ₐ[K]
      (P⧸(Q⊔Ideal.span {X p-1})) :=
  Ideal.quotientEquivAlgOfEq K (chartIdeal_eq Q hQ p)

@[simp] theorem chartEquiv_class (p : ι) (a : P) :
    chartEquiv Q hQ p (NormalizedHomogeneousChart.quotientMap (system Q) p a)=
      Ideal.Quotient.mk (Q⊔Ideal.span {X p-1}) a :=
  Ideal.quotientEquivAlgOfEq_mk K (chartIdeal_eq Q hQ p) a

/-- The arbitrary-algebra point representation uses the literal original
normalized quotient, not a reduced coordinate ring. -/
def chartPointEquiv (p : ι) (R : Type*) [CommRing R] [Algebra K R] :
    NormalizedHomogeneousChart.ChartPoint (system Q) p R ≃
      ((P⧸(Q⊔Ideal.span {X p-1})) →ₐ[K] R) :=
  (NormalizedHomogeneousChart.chartPointEquiv (system Q) p R).trans
    (AlgEquiv.arrowCongr (chartEquiv Q hQ p) (AlgEquiv.refl : R ≃ₐ[K] R))

/-- The actual Proj restriction maps for this exact system induce its
literal normalized coordinate ratios over every commutative test algebra. -/
theorem actualTransition_on_all_algebra_points
    {R : Type*} [CommRing R] [Algebra K R] (p q : ι)
    (φ : NormalizedHomogeneousChart.OverlapRing (system Q) p q →ₐ[K] R) :
    φ.toRingHom.comp
        (NormalizedHomogeneousProjOverlap.actualTransition (system Q) p q)=
      (NormalizedHomogeneousChart.overlapToHom
        (NormalizedHomogeneousChart.homToOverlap φ).transition).toRingHom :=
  NormalizedHomogeneousProjOverlap.actualTransition_on_all_algebra_points
    (system Q) p q φ

end PaperVerification.HomogeneousIdealChartSystem
end
end
end TAF_LiteralSource_0327

section TAF_LiteralSource_0328
/- Original module: PaperVerification.AlternatingFormsIsotropicAtlas -/


/-!
# The original common-isotropic atlas and its genuine Proj transitions

The homogeneous system below generates exactly the original Plucker and
isotropy ideal. Its actual projective scheme is identified with the Proj
used for the complete-section comparison. On every affine chart, the
normalized coordinates represent the original row-isotropic matrices over
every commutative coefficient algebra; each coordinate is proved to be the
corresponding maximal minor. The generic actual-Proj overlap comparison
therefore applies to these literal coordinates, including nilpotents.

The one-plane boundary uses the actual one-row Plucker charts and their
cover. Alternating restrictions on these rows vanish identically.
This source candidate has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K] [CharZero K] {t n m : ℕ}
  (forms : Fin m → StrictPairs n → K)

/-- Literal homogeneous generators of the entire original isotropy ideal. -/
abbrev isotropicHomogeneousSystem :=
  HomogeneousIdealChartSystem.system
    (isotropicPluckerIdeal (K := K) (t := t) forms)

theorem isotropicHomogeneousSystem_ideal_eq :
    NormalizedHomogeneousProjOverlap.equationIdeal
      (isotropicHomogeneousSystem (t := t) forms)=
      isotropicPluckerIdeal forms :=
  HomogeneousIdealChartSystem.equationIdeal_eq _
    (isotropicPluckerIdeal_isHomogeneous forms)

/-- The system's actual Proj is the original projective scheme; no change
of ideal, radical, saturation, or underlying point set occurs. -/
theorem isotropicHomogeneousSystem_projectiveScheme_eq :
    Proj (NormalizedHomogeneousProjOverlap.grading
      (isotropicHomogeneousSystem (t := t) forms))=
      Proj (isotropicProjectiveGrading (t := t) forms) :=
  HomogeneousIdealChartSystem.projectiveScheme_eq _
    (isotropicPluckerIdeal_isHomogeneous forms)

/-- This equivalence retains the complete original row-isotropy ideal. -/
def normalizedIsotropicChartEquiv (p : PluckerIndex (t+2) n) :
    NormalizedHomogeneousChart.ChartRing (isotropicHomogeneousSystem forms) p ≃ₐ[K]
      IsotropicChartRing p forms :=
  (HomogeneousIdealChartSystem.chartEquiv _
    (isotropicPluckerIdeal_isHomogeneous forms) p).trans
      (isotropicPluckerBigCellEquiv p forms)

@[simp] theorem normalizedIsotropicChartEquiv_class
    (p : PluckerIndex (t+2) n) (a : MvPolynomial (PluckerIndex (t+2) n) K) :
    normalizedIsotropicChartEquiv forms p
      (NormalizedHomogeneousChart.quotientMap (isotropicHomogeneousSystem forms) p a)=
      isotropicChartEvaluation p forms a := by
  have h₀ := HomogeneousIdealChartSystem.chartEquiv_class
    (isotropicPluckerIdeal (K := K) (t := t) forms)
    (isotropicPluckerIdeal_isHomogeneous forms) p a
  have h₁ := Ideal.quotientEquivAlgOfEq_mk K
    (isotropicChartEvaluation_kernel p forms).symm a
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := isotropicChartEvaluation p forms)
    (isotropicChartEvaluation_surjective p forms) a
  have hcell : isotropicPluckerBigCellEquiv p forms (Ideal.Quotient.mk _ a)=
      isotropicChartEvaluation p forms a :=
    (congrArg (Ideal.quotientKerAlgEquivOfSurjective
      (f := isotropicChartEvaluation p forms)
      (isotropicChartEvaluation_surjective p forms)) h₁).trans h₂
  exact (congrArg (isotropicPluckerBigCellEquiv p forms) h₀).trans hcell

/-- Universal normalized Plucker points and original isotropic row charts
are equivalent over every commutative test algebra, with no field or
reducedness assumption on that algebra. -/
def normalizedPointEquivIsotropicPoint (p : PluckerIndex (t+2) n)
    (R : Type*) [CommRing R] [Algebra K R] :
    NormalizedHomogeneousChart.ChartPoint (isotropicHomogeneousSystem forms) p R ≃
      IsotropicChartPoint p forms R :=
  (NormalizedHomogeneousChart.chartPointEquiv
    (isotropicHomogeneousSystem forms) p R).trans
    ((AlgEquiv.arrowCongr (normalizedIsotropicChartEquiv forms p)
      (AlgEquiv.refl : R ≃ₐ[K] R)).trans (isotropicChartPointEquiv p forms))

/-- The coordinate interpretation is the actual maximal minor of the
original normalized matrix, not an arbitrary labeling of chart points. -/
theorem normalizedPointEquivIsotropicPoint_minor
    {R : Type*} [CommRing R] [Algebra K R]
    (p I : PluckerIndex (t+2) n) (A : IsotropicChartPoint p forms R) :
    ((normalizedPointEquivIsotropicPoint forms p R).symm A).coordinate I=
      Matrix.det (A.matrix.submatrix id I.val) := by
  change A.toAlgHom (normalizedIsotropicChartEquiv forms p
    (NormalizedHomogeneousChart.quotientMap (isotropicHomogeneousSystem forms) p (X I)))=_
  rw [normalizedIsotropicChartEquiv_class]
  change (A.toAlgHom.comp (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms)))
    (matrixMinorEvaluation (pluckerChartMatrix p) (X I))=_
  rw [matrixMinorEvaluation,aeval_X,AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change A.toAlgHom (Ideal.Quotient.mk (isotropicChartIdeal p forms)
    (pluckerChartMatrix p i (I.val j)))=A.matrix i (I.val j)
  exact IsotropicChartPoint.toAlgHom_entry A i (I.val j)

/-- The actual restriction of the same Proj scheme is the literal
normalized ratio transition for all coefficient algebras. Combined with
the preceding maximal-minor formula, this is the transition on the original
Plucker coordinates of the common-isotropic row charts. -/
theorem isotropic_actualTransition_on_all_algebra_points
    {R : Type*} [CommRing R] [Algebra K R]
    (p q : PluckerIndex (t+2) n)
    (φ : NormalizedHomogeneousChart.OverlapRing
      (isotropicHomogeneousSystem forms) p q →ₐ[K] R) :
    φ.toRingHom.comp
        (NormalizedHomogeneousProjOverlap.actualTransition
          (isotropicHomogeneousSystem forms) p q)=
      (NormalizedHomogeneousChart.overlapToHom
        (NormalizedHomogeneousChart.homToOverlap φ).transition).toRingHom :=
  NormalizedHomogeneousProjOverlap.actualTransition_on_all_algebra_points
    (isotropicHomogeneousSystem forms) p q φ

/-- The literal one-plane basic open is its original row-coordinate affine
space. This includes ambient dimension one. -/
def onePlaneProjBasicOpenIso (k : ℕ) (p : PluckerIndex 1 (2*k+1)) :
    (Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)) :=
  HomogeneousQuotientCharts.projectiveBasicOpenIsoNormalized
      matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1)) p ≪≫
    Scheme.Spec.mapIso (pluckerBigCellEquiv (K := K) p).symm.toRingEquiv.toCommRingCatIso.op

theorem onePlaneProjBasicOpen_cover (k : ℕ) :
    (⨆ p : PluckerIndex 1 (2*k+1),
      Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
        (Ideal.Quotient.mk matrixPluckerIdeal (X p)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover
    matrixPluckerIdeal (matrixPluckerIdeal_isHomogeneous (by decide : 0<1))
    (Ideal.Quotient.mkₐ K matrixPluckerIdeal) Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0328

section TAF_LiteralSource_0329
/- Original module: PaperVerification.AlternatingFormsExtremeRegularity -/


/-! Exact graded and projective comparison maps. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi

section NormalSupport

variable {s n : ℕ} (α β : Fin s → Fin n)

/-- Adjoining a universally comparable index preserves a chain support. -/
theorem normalMonomial_single_add (I : IntervalIndex α β)
    (hI : ∀ J : IntervalIndex α β,I≤J ∨ J≤I)
    (a : IntervalIndex α β →₀ ℕ) (ha : NormalMonomial α β a) :
    NormalMonomial α β (Finsupp.single I 1+a) := by
  classical
  intro J hJ L hL
  have hJ' := Finset.mem_union.mp (Finsupp.support_add hJ)
  have hL' := Finset.mem_union.mp (Finsupp.support_add hL)
  rcases hJ' with hJ' | hJ'
  · have eJ : J=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hJ')
    subst J
    exact hI L
  · rcases hL' with hL' | hL'
    · have eL : L=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hL')
      subst L
      exact (hI J).symm
    · exact ha J hJ' L hL'

/-- Multiplication by an extreme coordinate does not require straightening. -/
theorem normalSupport_X_mul {K : Type*} [Field K]
    (I : IntervalIndex α β) (hI : ∀ J : IntervalIndex α β,I≤J ∨ J≤I)
    (p : MvPolynomial (IntervalIndex α β) K)
    (hp : ∀ a∈p.support,NormalMonomial α β a) :
    ∀ a∈(X I*p).support,NormalMonomial α β a := by
  classical
  intro a ha
  rw [support_X_mul] at ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
  exact normalMonomial_single_add α β I hI b (hp b hb)

/-- A single variable is a normal polynomial. -/
theorem normalSupport_X {K : Type*} [Field K] (I : IntervalIndex α β) :
    ∀ a∈(X I : MvPolynomial (IntervalIndex α β) K).support,
      NormalMonomial α β a := by
  classical
  intro a ha
  have ha' : a=Finsupp.single I 1 :=
    Finset.mem_singleton.mp (support_monomial_subset ha)
  subst a
  intro J hJ L hL
  have eJ : J=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hJ)
  have eL : L=I := Finset.mem_singleton.mp (Finsupp.support_single_subset hL)
  exact Or.inl (by rw [eJ,eL])

end NormalSupport

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "A" => MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q
local notation "φ" => oddGoodMap (K := K) k t hs

/-- Every good coordinate survives in the literal original quotient. -/
theorem oddGoodCoordinate_ne_zero (I : IntervalIndex α β) : φ (X I)≠0 := by
  intro h
  exact X_ne_zero I (oddGood_normal_polynomial_eq_zero k t hs (X I)
    (normalSupport_X α β I) h)

/-- Divisibility by one extreme coordinate is not introduced by multiplying
by a different extreme coordinate in the actual Plucker quotient. -/
theorem oddGoodCoordinate_dvd_of_dvd_mul
    (I J : IntervalIndex α β) (hIJ : I≠J)
    (hI : ∀ L : IntervalIndex α β,I≤L ∨ L≤I)
    (hJ : ∀ L : IntervalIndex α β,J≤L ∨ L≤J)
    (z : A) (hz : φ (X I)∣φ (X J)*z) : φ (X I)∣z := by
  classical
  obtain ⟨r,hr⟩ := hz
  obtain ⟨p,rfl⟩ := oddGoodMap_surjective k t hs z
  obtain ⟨q,rfl⟩ := oddGoodMap_surjective k t hs r
  let p' := oddGoodNormalForm (K := K) k t hs p
  let q' := oddGoodNormalForm (K := K) k t hs q
  have hp : ∀ a∈p'.support,NormalMonomial α β a :=
    oddGoodNormalForm_normal k t hs p
  have hq : ∀ a∈q'.support,NormalMonomial α β a :=
    oddGoodNormalForm_normal k t hs q
  have he : X J*p'=X I*q' := by
    apply sub_eq_zero.mp
    apply oddGood_normal_polynomial_eq_zero k t hs (X J*p'-X I*q')
    · intro a ha
      rcases Finset.mem_union.mp (support_sub _ _ _ ha) with ha | ha
      · exact normalSupport_X_mul α β J hJ p' hp a ha
      · exact normalSupport_X_mul α β I hI q' hq a ha
    · simp only [map_sub,map_mul,p',q',oddGoodMap_normalForm]
      exact sub_eq_zero.mpr hr
  have hdiv : (X I : MvPolynomial (IntervalIndex α β) K)∣p' := by
    have hmul : (X I : MvPolynomial (IntervalIndex α β) K)∣X J*p' := ⟨q',he⟩
    rcases X_dvd_mul_iff.mp hmul with h | h
    · exact False.elim (hIJ (X_dvd_X.mp h))
    · exact h
  obtain ⟨w,hw⟩ := hdiv
  refine ⟨φ w,?_⟩
  calc
    φ p = φ p' := (oddGoodMap_normalForm k t hs p).symm
    _ = φ (X I)*φ w := by rw [hw,map_mul]

/-- The regularity condition is in the ordinary principal-ideal quotient. -/
theorem oddGoodCoordinate_regular_mod
    (I J : IntervalIndex α β) (hIJ : I≠J)
    (hI : ∀ L : IntervalIndex α β,I≤L ∨ L≤I)
    (hJ : ∀ L : IntervalIndex α β,J≤L ∨ L≤J) :
    IsRegular (Ideal.Quotient.mk (Ideal.span ({φ (X I)} : Set A)) (φ (X J))) := by
  let U : Ideal A := Ideal.span ({φ (X I)} : Set A)
  apply (Commute.isRegular_iff (R := A⧸U)
    (a := Ideal.Quotient.mk U (φ (X J))) (fun a ↦ Commute.all _ a)).mpr
  change IsSMulRegular (A⧸U) (Ideal.Quotient.mk U (φ (X J)))
  apply IsSMulRegular.of_right_eq_zero_of_smul (R := A⧸U) (M := A⧸U)
  intro z hz
  obtain ⟨w,rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply oddGoodCoordinate_dvd_of_dvd_mul k t hs I J hIJ hI hJ w
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul,smul_eq_mul] using hz

/-- The actual lower endpoint, regarded as a good coordinate. -/
def oddLeastGoodIndex : IntervalIndex α β :=
  ⟨⟨α,oddIntervalLower_strictMono k (t+2) hs⟩,
    fun i ↦ ⟨le_rfl,oddIntervalLower_le_upper k (t+2) hs i⟩⟩

/-- The actual upper endpoint, regarded as a good coordinate. -/
def oddGreatestGoodIndex : IntervalIndex α β :=
  ⟨⟨β,oddIntervalUpper_strictMono k (t+2) hs⟩,
    fun i ↦ ⟨oddIntervalLower_le_upper k (t+2) hs i,le_rfl⟩⟩

theorem oddLeastGoodIndex_le (I : IntervalIndex α β) : oddLeastGoodIndex k t hs≤I :=
  fun i ↦ (I.property i).1

theorem le_oddGreatestGoodIndex (I : IntervalIndex α β) : I≤oddGreatestGoodIndex k t hs :=
  fun i ↦ (I.property i).2

theorem oddLeastGoodIndex_ne_greatest (hstrict : t+2<k+1) :
    oddLeastGoodIndex k t hs≠oddGreatestGoodIndex k t hs := by
  intro h
  have he := congrArg (fun I : IntervalIndex α β ↦ (I.val.val (0 : Fin (t+2))).val) h
  change 2*0=2*(k+1-(t+2)+0) at he
  omega

/-- In every positive-dimensional interval, the two extremal good coordinates
form a genuine regular pair in the original common-isotropic ring. -/
theorem odd_extremeCoordinates_regularPair (hstrict : t+2<k+1) :
    IsRegular (φ (X (oddLeastGoodIndex k t hs))) ∧
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({φ (X (oddLeastGoodIndex k t hs))} : Set A))
      (φ (X (oddGreatestGoodIndex k t hs)))) := by
  letI : (Q).IsPrime := odd_isotropicPluckerIdeal_isPrime k t hs
  exact ⟨isRegular_iff_ne_zero.mpr (oddGoodCoordinate_ne_zero k t hs _),
    oddGoodCoordinate_regular_mod k t hs _ _
      (oddLeastGoodIndex_ne_greatest k t hs hstrict)
      (fun I ↦ Or.inl (oddLeastGoodIndex_le k t hs I))
      (fun I ↦ Or.inr (le_oddGreatestGoodIndex k t hs I))⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0329

section TAF_LiteralSource_0330
/- Original module: PaperVerification.AlternatingFormsProjectiveSections -/


/-! Exact graded and projective comparison maps. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi AlgebraicGeometry

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "φ" => oddGoodMap (K := K) k t hs

/-- The original ordinary homogeneous grading on the original isotropic
Plucker quotient, with its verified internal decomposition. -/
def oddProjectiveGrading : ℕ → Submodule K
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q) :=
  HomogeneousQuotientProjective.grading Q (isotropicPluckerIdeal_isHomogeneous _)

instance oddProjectiveGradedAlgebra : GradedAlgebra (oddProjectiveGrading (K := K) k t) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra Q _

theorem odd_goodCoordinate_degree_one (I : IntervalIndex α β) :
    φ (X I)∈oddProjectiveGrading (K := K) k t 1 := by
  rw [oddGoodMap_X]
  exact HomogeneousQuotientProjective.quotient_X_mem_one Q _ I.val

theorem odd_goodCoordinate_basicOpen_cover :
    (⨆ I : IntervalIndex α β,
      Proj.basicOpen (oddProjectiveGrading (K := K) k t) (φ (X I)))=⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover Q _ φ
    (oddGoodMap_surjective k t hs) (odd_goodCoordinate_degree_one k t hs)

theorem odd_goodCoordinate_isRegular (I : IntervalIndex α β) : IsRegular (φ (X I)) := by
  letI : (Q).IsPrime := odd_isotropicPluckerIdeal_isPrime k t hs
  exact isRegular_iff_ne_zero.mpr (oddGoodCoordinate_ne_zero k t hs I)

include hs in
/-- All nonnegative-degree complete sections on the actual Proj are the
original homogeneous coordinate elements, in every distinct-endpoint case. -/
theorem odd_bijective_toTwistingSheaf_top (hstrict : t+2<k+1) (d : ℕ) :
    Function.Bijective
      (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
        (rfl : (d : ℤ)=d) ⊤) :=
  RegularPairProjectiveSections.bijective_toTwistingSheaf_top
    (oddProjectiveGrading (K := K) k t) (fun I : IntervalIndex α β ↦ φ (X I))
    (odd_goodCoordinate_degree_one k t hs) (odd_goodCoordinate_isRegular k t hs)
    (odd_goodCoordinate_basicOpen_cover k t hs)
    (oddLeastGoodIndex k t hs) (oddGreatestGoodIndex k t hs)
    (odd_extremeCoordinates_regularPair k t hs hstrict).2 d

set_option synthInstance.maxHeartbeats 80000 in
/-- The canonical component isomorphisms preserve literal sheaf-section
multiplication; they are the degreewise comparison for the complete section ring. -/
theorem odd_toTwistingSheaf_top_mul (a b : ℕ)
    (r : oddProjectiveGrading (K := K) k t a)
    (s : oddProjectiveGrading (K := K) k t b) :
    Proj.twistingSheaf.mul (oddProjectiveGrading (K := K) k t) ⊤ (a : ℤ) (b : ℤ)
      (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t) rfl ⊤ r)
      (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t) rfl ⊤ s)=
    Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
      (by omega : ((a+b : ℕ) : ℤ)=(a : ℤ)+(b : ℤ)) ⊤
      ⟨(r : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q)*
        (s : MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q),SetLike.mul_mem_graded r.2 s.2⟩ :=
  Proj.mul_toTwistingSheaf (𝒜 := oddProjectiveGrading (K := K) k t) rfl rfl ⊤ r s

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0330

section TAF_LiteralSource_0331
/- Original module: PaperVerification.AlternatingFormsPointSections -/


/-!
# Complete Plucker sections at the singleton interval endpoint

At s=k+1 the lower and upper good-index bounds coincide.  Every length-d
standard chain is therefore the constant chain, and the actual original
degree-d quotient has its basis vector equal to the d-th power of the
surviving coordinate.  The single standard chart covers the actual Proj.
This gives the genuine complete-section comparison in the boundary case
where a two-element regular sequence is unavailable.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.AlternatingForms

open MvPolynomial Hibi AlgebraicGeometry

variable {K : Type*} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "α" => oddIntervalLower k (t+2) hs
local notation "β" => oddIntervalUpper k (t+2) hs
local notation "Q" => isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "A" => MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸Q
local notation "φ" => oddGoodMap (K := K) k t hs
local notation "x" => φ (X (oddLeastGoodIndex k t hs))

/-- The constant lower-endpoint chain exists in every degree, including zero. -/
def oddLowerConstantChain (d : ℕ) : BandChain α β d :=
  ⟨fun _ ↦ α,fun _ ↦ oddIntervalLower_strictMono k (t+2) hs,
    (fun _ a ↦ ⟨le_rfl,oddIntervalLower_le_upper k (t+2) hs a⟩),monotone_const⟩

theorem odd_endpoint_bounds_eq (he : t+2=k+1) : α=β := by
  funext a
  apply Fin.ext
  dsimp only [oddIntervalLower,oddIntervalUpper]
  omega

theorem odd_endpoint_index_eq (he : t+2=k+1) (I : IntervalIndex α β) :
    I=oddLeastGoodIndex k t hs := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  apply le_antisymm
  · change I.val.val a ≤ α a
    simpa only [←odd_endpoint_bounds_eq k t hs he] using (I.property a).2
  · exact (I.property a).1

theorem odd_endpoint_chain_eq (he : t+2=k+1) (d : ℕ) (C : BandChain α β d) :
    C=oddLowerConstantChain k t hs d := by
  apply Subtype.ext
  funext j a
  apply le_antisymm
  · change C.val j a ≤ α a
    simpa only [←odd_endpoint_bounds_eq k t hs he] using (C.property.2.1 j a).2
  · exact (C.property.2.1 j a).1

theorem odd_lowerConstantChain_product (d : ℕ) :
    Ideal.Quotient.mk Q (chainPluckerProduct α β (oddLowerConstantChain k t hs d))=x^d := by
  change Ideal.Quotient.mk Q
    (∏ _ : Fin d, X (oddLeastGoodIndex k t hs).val) = x^d
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,map_pow,oddGoodMap_X]

/-- Every actual homogeneous element is a degree-zero multiple of the
power of the original surviving coordinate. -/
theorem odd_endpoint_piece (he : t+2=k+1) (d : ℕ) (r : A)
    (hr : r∈oddProjectiveGrading k t d) :
    ∃ c : A,c∈oddProjectiveGrading k t 0 ∧ r=c*x^d := by
  classical
  let B := oddPluckerDegreeBasis (K := K) k t hs d
  let C₀ := oddLowerConstantChain k t hs d
  have hr' : r∈oddPluckerDegree k t d := by
    simpa only [oddProjectiveGrading,HomogeneousQuotientProjective.grading_eq_piece,
      oddPluckerDegree] using hr
  let z : oddPluckerDegree (K := K) k t d := ⟨r,hr'⟩
  have hsum : (B.repr z C₀) • B C₀=z := by
    have h := B.sum_repr z
    rw [Finset.sum_eq_single C₀] at h
    · exact h
    · intro C hC hne
      exact (hne (odd_endpoint_chain_eq k t hs he d C)).elim
    · intro hC
      exact (hC (Finset.mem_univ C₀)).elim
  refine ⟨algebraMap K A (B.repr z C₀),?_,?_⟩
  · rw [oddProjectiveGrading,HomogeneousQuotientProjective.grading_eq_piece,
      homogeneousQuotient_degree_zero]
    exact Submodule.mem_one.mpr ⟨B.repr z C₀,rfl⟩
  · have hz := congrArg (fun v : oddPluckerDegree (K := K) k t d ↦ (v : A)) hsum
    have hz' : (B.repr z C₀) • (x ^ d : A)=r := by
      simpa only [Submodule.coe_smul,B,oddPluckerDegreeBasis_apply,C₀,
        odd_lowerConstantChain_product,z] using hz
    exact hz'.symm.trans (Algebra.smul_def (R := K) (B.repr z C₀) (x ^ d))

theorem odd_endpoint_basicOpen (he : t+2=k+1) :
    Proj.basicOpen (oddProjectiveGrading k t) x=⊤ := by
  have hcover := odd_goodCoordinate_basicOpen_cover (K := K) k t hs
  calc
    Proj.basicOpen (oddProjectiveGrading k t) x=
        ⨆ I : IntervalIndex α β,Proj.basicOpen (oddProjectiveGrading k t) (φ (X I)) := by
      apply le_antisymm
      · exact le_iSup (fun I : IntervalIndex α β ↦
          Proj.basicOpen (oddProjectiveGrading k t) (φ (X I))) _
      · apply iSup_le
        intro I
        rw [odd_endpoint_index_eq k t hs he I]
    _ = ⊤ := hcover

include hs in
/-- The singleton interval has complete original Plucker sections in every
nonnegative degree, with no missing boundary case. -/
theorem odd_endpoint_bijective_toTwistingSheaf_top (he : t+2=k+1) (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
      (rfl : (d : ℤ)=d) ⊤) :=
  SingleGeneratorProjectiveSections.bijective_toTwistingSheaf_top
    (oddProjectiveGrading k t) x (odd_goodCoordinate_degree_one k t hs _)
    (odd_goodCoordinate_isRegular k t hs _) (odd_endpoint_basicOpen k t hs he)
    (odd_endpoint_piece k t hs he) d

include hs in
/-- All sizes 2 <= s <= k+1 now have the actual complete-section comparison;
the two mutually exclusive endpoint cases are joined without weakening the range. -/
theorem odd_allSizes_bijective_toTwistingSheaf_top (d : ℕ) :
    Function.Bijective (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
      (rfl : (d : ℤ)=d) ⊤) := by
  rcases hs.lt_or_eq with hlt | he
  · exact odd_bijective_toTwistingSheaf_top k t hs hlt d
  · exact odd_endpoint_bijective_toTwistingSheaf_top k t hs he d

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0331

section TAF_LiteralSource_0332
/- Original module: PaperVerification.ProjectiveSectionRing -/


/-!
# The actual complete section ring of a projective spectrum

The degree-d piece is the existing group of global sections of the
actual twisting sheaf O(d).  These groups are additive subgroups of the
same product of localization rings.  Their pointwise multiplication
therefore defines the complete section ring independently of any
comparison with the original graded ring.

The canonical map sends a homogeneous element r to the actual section
r/1.  If its component maps are bijective, the resulting canonical ring
map is an isomorphism.  No multiplication is transported from the desired
conclusion, and no section is replaced by a polynomial surrogate.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.ProjectiveSectionRing

open AlgebraicGeometry
open scoped DirectSum
open ProjectiveSpectrum.TwistingSheaf

universe u
variable {A : Type u} {σ : Type*} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The existing actual global-section subgroup, in nonnegative degree. -/
abbrev sectionPiece (d : ℕ) :
    AddSubgroup (∀ x : (⊤ : (Proj 𝒜).Opens),Localizations 𝒜 x.1) :=
  sectionsAddSubgroup 𝒜 (d : ℤ) ⊤

/-- This is literally the actual global section group of the twisting
sheaf, with its existing addition. -/
def sectionPieceEquiv (d : ℕ) :
    sectionPiece 𝒜 d ≃+ Γ(Proj.twistingSheaf 𝒜 (d : ℤ),⊤) :=
  AddEquiv.refl _

set_option backward.isDefEq.respectTransparency false in
instance sectionPieceGradedMonoid : SetLike.GradedMonoid (sectionPiece 𝒜) where
  one_mem := by
    change (isLocallyFraction 𝒜 (0 : ℤ)).pred
      (fun x : (⊤ : (Proj 𝒜).Opens) => (1 : Localizations 𝒜 x.1))
    convert (isLocallyFraction_val (𝒜 := 𝒜) (1 : Γ(Proj 𝒜,⊤))) using 1 <;>
      funext x <;> simp only [Proj.one_apply,HomogeneousLocalization.val_one]
  mul_mem := by
    intro a b f g hf hg
    change (isLocallyFraction 𝒜 ((a+b : ℕ) : ℤ)).pred (f*g)
    simpa only [Nat.cast_add] using isLocallyFraction_mul hf hg

/-- The actual complete section ring, with independently defined
pointwise homogeneous products. -/
abbrev SectionRing := ⨁ d : ℕ,sectionPiece 𝒜 d

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Multiplication of homogeneous elements is the literal product of
their values in the localizations. -/
theorem of_mul_of (a b : ℕ) (s : sectionPiece 𝒜 a) (t : sectionPiece 𝒜 b) :
    DirectSum.of (fun d ↦ sectionPiece 𝒜 d) a s *
      DirectSum.of (fun d ↦ sectionPiece 𝒜 d) b t =
    DirectSum.of (fun d ↦ sectionPiece 𝒜 d) (a+b)
      ⟨s.1*t.1,by
        change (isLocallyFraction 𝒜 ((a+b : ℕ) : ℤ)).pred (s.1*t.1)
        simpa only [Nat.cast_add] using isLocallyFraction_mul s.2 t.2⟩ :=
  by
    classical
    refine (DirectSum.of_mul_of
      (A := fun d : ℕ ↦ ↥(sectionPiece 𝒜 d)) s t).trans ?_
    apply congrArg (DirectSum.of (fun d : ℕ ↦ ↥(sectionPiece 𝒜 d)) (a+b))
    exact Subtype.ext rfl

/-- The canonical component map is the existing r/1 section map. -/
abbrev componentMap (d : ℕ) : 𝒜 d →+ sectionPiece 𝒜 d :=
  Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤

@[simp] theorem componentMap_apply (d : ℕ) (r : 𝒜 d)
    (x : (⊤ : (Proj 𝒜).Opens)) :
    (componentMap 𝒜 d r).1 x=Localization.mk (r : A) 1 := rfl

/-- Extend the actual canonical component maps to the external direct sum. -/
def directSumMap : (⨁ d : ℕ,𝒜 d) →+* SectionRing 𝒜 :=
  DirectSum.toSemiring
    (fun d ↦ (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d).comp
      (componentMap 𝒜 d))
    (by
      change DirectSum.of (fun j ↦ sectionPiece 𝒜 j) 0
        (componentMap 𝒜 0 ⟨1,SetLike.GradedOne.one_mem⟩)=1
      rw [DirectSum.one_def]
      apply congrArg (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) 0)
      apply Subtype.ext
      funext x
      change Localization.mk (1 : A) 1=1
      simp only [Localization.mk_one_eq_algebraMap,map_one])
    (by
      intro a b r s
      change DirectSum.of (fun j ↦ sectionPiece 𝒜 j) (a+b)
          (componentMap 𝒜 (a+b) ⟨(r : A)*(s : A),SetLike.mul_mem_graded r.2 s.2⟩)=
        DirectSum.of (fun j ↦ sectionPiece 𝒜 j) a (componentMap 𝒜 a r) *
          DirectSum.of (fun j ↦ sectionPiece 𝒜 j) b (componentMap 𝒜 b s)
      rw [DirectSum.of_mul_of]
      apply congrArg (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) (a+b))
      apply Subtype.ext
      funext x
      change Localization.mk ((r : A)*(s : A)) 1=
        Localization.mk (r : A) 1*Localization.mk (s : A) 1
      simp only [Localization.mk_one_eq_algebraMap,map_mul])

@[simp] theorem directSumMap_of (d : ℕ) (r : 𝒜 d) :
    directSumMap 𝒜 (DirectSum.of (fun j ↦ 𝒜 j) d r)=
      DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d (componentMap 𝒜 d r) :=
  DirectSum.toSemiring_of _ _ _ _ _

theorem directSumMap_toAddMonoidHom :
    (directSumMap 𝒜).toAddMonoidHom=DirectSum.map (componentMap 𝒜) := by
  apply DirectSum.addHom_ext
  intro d r
  change directSumMap 𝒜 (DirectSum.of (fun j ↦ 𝒜 j) d r)=_
  rw [directSumMap_of,DirectSum.map_of]

/-- The canonical coordinate-ring to complete-section-ring map. -/
def canonicalMap : A →+* SectionRing 𝒜 :=
  (directSumMap 𝒜).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- On every homogeneous element this map is exactly the corresponding
actual global section r/1 placed in its own degree. -/
theorem canonicalMap_homogeneous (d : ℕ) (r : 𝒜 d) :
    canonicalMap 𝒜 (r : A)=
      DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d
        (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤ r) := by
  change directSumMap 𝒜 (DirectSum.decompose 𝒜 (r : A))=_
  rw [DirectSum.decompose_coe,directSumMap_of]
  rfl

/-- Componentwise completeness proves bijectivity of the canonical map
to the already-defined actual section ring. -/
theorem canonicalMap_bijective
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) :
    Function.Bijective (canonicalMap 𝒜) := by
  have hm : Function.Bijective (DirectSum.map (componentMap 𝒜)) :=
    ⟨(DirectSum.map_injective _).2 (fun d ↦ (h d).1),
      (DirectSum.map_surjective _).2 (fun d ↦ (h d).2)⟩
  have hd : Function.Bijective (directSumMap 𝒜) := by
    change Function.Bijective (directSumMap 𝒜).toAddMonoidHom
    rw [directSumMap_toAddMonoidHom]
    exact hm
  exact hd.comp (DirectSum.decomposeRingEquiv 𝒜).bijective

/-- The canonical isomorphism with the actual complete section ring,
once the actual section comparison is proved in every degree. -/
def completeSectionRingEquiv
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) :
    A ≃+* SectionRing 𝒜 :=
  RingEquiv.ofBijective (canonicalMap 𝒜) (canonicalMap_bijective 𝒜 h)

@[simp] theorem completeSectionRingEquiv_apply
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) (r : A) :
    completeSectionRingEquiv 𝒜 h r=canonicalMap 𝒜 r := rfl

theorem completeSectionRingEquiv_homogeneous
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤))
    (d : ℕ) (r : 𝒜 d) :
    completeSectionRingEquiv 𝒜 h (r : A)=
      DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d
        (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤ r) :=
  canonicalMap_homogeneous 𝒜 d r

/-- The canonical comparison identifies each original homogeneous piece
with exactly the corresponding actual direct-sum section piece, in both
directions.  This records the grading, not only the abstract ring. -/
theorem completeSectionRingEquiv_mem_degree_iff
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤))
    (d : ℕ) (x : SectionRing 𝒜) :
    (∃ r : 𝒜 d,completeSectionRingEquiv 𝒜 h (r : A)=x) ↔
      ∃ s : sectionPiece 𝒜 d,DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d s=x := by
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨componentMap 𝒜 d r,(completeSectionRingEquiv_homogeneous 𝒜 h d r).symm⟩
  · rintro ⟨s,rfl⟩
    obtain ⟨r,hr⟩ := (h d).surjective s
    refine ⟨r,?_⟩
    rw [completeSectionRingEquiv_homogeneous]
    exact congrArg (DirectSum.of (fun j ↦ sectionPiece 𝒜 j) d) hr


section Scalars

variable {K : Type*} [CommRing K] [Algebra K A]

/-- Scalars act by their canonical constant sections.  This algebra
structure is defined before and independently of any completeness proof. -/
instance sectionRingAlgebra : Algebra K (SectionRing 𝒜) :=
  ((canonicalMap 𝒜).comp (algebraMap K A)).toAlgebra

/-- The canonical coordinate map also preserves its original scalars. -/
def canonicalAlgHom : A →ₐ[K] SectionRing 𝒜 where
  toRingHom := canonicalMap 𝒜
  commutes' _ := rfl

/-- For degree-zero scalars the algebra map is exactly their actual
constant section, in degree zero of the complete section ring. -/
theorem algebraMap_eq_degreeZero_section (c : K)
    (hc : algebraMap K A c∈𝒜 0) :
    algebraMap K (SectionRing 𝒜) c=
      DirectSum.of (fun d ↦ sectionPiece 𝒜 d) 0
        (Proj.toTwistingSheaf 𝒜 (rfl : (0 : ℤ)=0) ⊤ ⟨algebraMap K A c,hc⟩) :=
  canonicalMap_homogeneous 𝒜 0 ⟨algebraMap K A c,hc⟩

/-- The canonical complete-section comparison is an isomorphism over
the original scalar ring, not merely an abstract ring isomorphism. -/
def completeSectionAlgEquiv
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) :
    A ≃ₐ[K] SectionRing 𝒜 where
  toRingEquiv := completeSectionRingEquiv 𝒜 h
  commutes' _ := rfl

@[simp] theorem completeSectionAlgEquiv_apply
    (h : ∀ d : ℕ,Function.Bijective
      (Proj.toTwistingSheaf 𝒜 (rfl : (d : ℤ)=d) ⊤)) (r : A) :
    completeSectionAlgEquiv (K := K) 𝒜 h r=canonicalMap 𝒜 r := rfl

end Scalars

end PaperVerification.ProjectiveSectionRing
end
end
end TAF_LiteralSource_0332

section TAF_LiteralSource_0333
/- Original module: PaperVerification.AlternatingFormsOnePlaneCompleteSectionRing -/


/-!
# Complete section algebra of the one-plane Plucker quotient

The polynomial boundary is treated independently of the higher-plane
argument. The target is the actual graded algebra of global twisting-sheaf
sections, with its original multiplication and its canonical degree maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry MvPolynomial
open PaperVerification.ProjectiveSectionRing

variable {K : Type*} [Field K] [CharZero K]

/-- The same canonical comparison in the one-plane boundary, including
ambient dimension one and all nonnegative section degrees. -/
def onePlaneCompleteSectionRingEquiv (k : ℕ) :
    (MvPolynomial (PluckerIndex 1 (2*k+1)) K ⧸ matrixPluckerIdeal) ≃ₐ[K]
    SectionRing (onePlaneProjectiveGrading (K := K) k) :=
  completeSectionAlgEquiv (onePlaneProjectiveGrading (K := K) k)
    (onePlane_bijective_toTwistingSheaf_top k)

theorem onePlaneCompleteSectionRingEquiv_homogeneous (k d : ℕ)
    (r : onePlaneProjectiveGrading (K := K) k d) :
    onePlaneCompleteSectionRingEquiv (K := K) k r=
      DirectSum.of (fun j ↦ sectionPiece (onePlaneProjectiveGrading (K := K) k) j) d
        (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
          (rfl : (d : ℤ)=d) ⊤ r) :=
  canonicalMap_homogeneous (onePlaneProjectiveGrading (K := K) k) d r

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0333

section TAF_LiteralSource_0334
/- Original module: PaperVerification.AlternatingFormsCompleteSectionRing -/


/-!
# The actual complete Plucker section rings in every odd-pencil size

The target is the external direct sum of the actual global twisting-sheaf
sections on the original homogeneous quotient's projective spectrum.
Its homogeneous product is their literal pointwise product in the
localization rings, and its scalars are the actual constant sections.

The component proofs include every positive size: the one-plane
polynomial boundary, the strict good interval, and the singleton
maximal-size interval.  The resulting algebra isomorphisms are canonical
and send every homogeneous coordinate element r to the section r/1.
The separate chart comparison identifies this actual Proj with the
original common-isotropic atlas.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry MvPolynomial
open PaperVerification.ProjectiveSectionRing

variable {K : Type*} [Field K] [CharZero K]

/-- The canonical scalar-preserving comparison with the actual complete
section ring for every original odd-pencil size at least two. -/
def oddCompleteSectionRingEquiv (k t : ℕ) (hs : t+2≤k+1) :
    (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) ≃ₐ[K]
    SectionRing (oddProjectiveGrading (K := K) k t) :=
  completeSectionAlgEquiv (oddProjectiveGrading (K := K) k t)
    (odd_allSizes_bijective_toTwistingSheaf_top k t hs)

/-- Every homogeneous coordinate element retains its original geometric
meaning under the complete-section comparison. -/
theorem oddCompleteSectionRingEquiv_homogeneous (k t : ℕ) (hs : t+2≤k+1)
    (d : ℕ) (r : oddProjectiveGrading (K := K) k t d) :
    oddCompleteSectionRingEquiv (K := K) k t hs r=
      DirectSum.of (fun j ↦ sectionPiece (oddProjectiveGrading (K := K) k t) j) d
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (d : ℤ)=d) ⊤ r) :=
  canonicalMap_homogeneous (oddProjectiveGrading (K := K) k t) d r

/-- The two displayed comparisons cover exactly all positive sizes in
the paper's odd-pencil range; there is no excluded endpoint. -/
theorem positive_size_cases (k s : ℕ) (hs : 1≤s) (hsk : s≤k+1) :
    s=1 ∨ ∃ t : ℕ,s=t+2 ∧ t+2≤k+1 := by
  by_cases h : s=1
  · exact Or.inl h
  · exact Or.inr ⟨s-2,by omega,by omega⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0334

section TAF_LiteralSource_0335
/- Original module: PaperVerification.AlternatingFormsBarEquivTransport -/


/-!
# Actual Tor under an isomorphism of augmented algebras

The basis on the second algebra is the image of the first actual basis.
Its multiplication coefficients are equal to the original coefficients,
so the normalized reduced bar complexes have an explicit identity-on-words
isomorphism.  The ordinary Tor comparison on both sides then gives an
isomorphism of the actual derived functor objects.

The comparison preserves every subcomplex of words, in particular those
defined by the sum of the original homogeneous degrees.  This is a proved
comparison of actual complexes and actual Tor, not an invariance assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarEquivTransport

open CategoryTheory HomologicalComplex
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A D I : Type u} [CommRing K] [CommRing A] [CommRing D]
  [Algebra K A] [Algebra K D]
  (e : A ≃ₐ[K] D) (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)

/-- The actual original augmentation composed with the inverse algebra
isomorphism. -/
def augmentation : D →ₐ[K] K := ε.comp e.symm.toAlgHom

/-- The actual positive algebra basis, with the same indexing set. -/
def basis : Module.Basis (Option I) K D := B.map e.toLinearEquiv

@[simp] theorem basis_apply (i : Option I) : basis e B i=e (B i) := rfl

@[simp] theorem augmentation_image (x : A) : augmentation e ε (e x)=ε x := by
  change ε (e.symm (e x))=ε x
  rw [e.symm_apply_apply]

theorem basis_unit (hunit : B none=1) : basis e B none=1 := by
  rw [basis_apply,hunit,map_one]

theorem augmentation_positive (hε : ∀ i,ε (B (some i))=0) (i : I) :
    augmentation e ε (basis e B (some i))=0 := by
  rw [basis_apply,augmentation_image,hε]

@[simp] theorem basis_repr_image (x : A) :
    (basis e B).repr (e x)=B.repr x := by
  change B.repr (e.symm (e x))=B.repr x
  rw [e.symm_apply_apply]

/-- Actual multiplication has exactly the same positive-basis
coefficients after transport. -/
theorem productCoefficients_eq (i j : I) :
    productCoefficients (basis e B) i j=productCoefficients B i j := by
  apply Finsupp.ext
  intro a
  change (basis e B).repr (basis e B (some i)*basis e B (some j)) (some a)=
    B.repr (B (some i)*B (some j)) (some a)
  rw [basis_apply,basis_apply,←map_mul,basis_repr_image]

theorem mergeBasis_eq (i : I) (L : List I) :
    PaperVerification.ReducedBarBasis.mergeBasis (basis e B) i L=
      PaperVerification.ReducedBarBasis.mergeBasis B i L := by
  cases L with
  | nil => rfl
  | cons j L =>
      change PaperVerification.ReducedBarBasis.appendTail L
          (productCoefficients (basis e B) i j)=
        PaperVerification.ReducedBarBasis.appendTail L (productCoefficients B i j)
      rw [productCoefficients_eq]

theorem merge_eq (i : I) :
    PaperVerification.ReducedBarBasis.merge (basis e B) i=
      PaperVerification.ReducedBarBasis.merge B i := by
  unfold PaperVerification.ReducedBarBasis.merge
  congr 1
  funext L
  exact mergeBasis_eq e B i L

theorem differentialBasis_eq (L : List I) :
    PaperVerification.ReducedBarBasis.differentialBasis (basis e B) L=
      PaperVerification.ReducedBarBasis.differentialBasis B L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      change PaperVerification.ReducedBarBasis.merge (basis e B) i (Finsupp.single L 1)-
          PaperVerification.ReducedBarBasis.prepend i
            (PaperVerification.ReducedBarBasis.differentialBasis (basis e B) L)=
        PaperVerification.ReducedBarBasis.merge B i (Finsupp.single L 1)-
          PaperVerification.ReducedBarBasis.prepend i
            (PaperVerification.ReducedBarBasis.differentialBasis B L)
      rw [merge_eq,ih]

theorem differential_eq :
    PaperVerification.ReducedBarBasis.differential (basis e B)=
      PaperVerification.ReducedBarBasis.differential B := by
  unfold PaperVerification.ReducedBarBasis.differential
  congr 1
  funext L
  exact differentialBasis_eq e B L

theorem reducedDegreeDifferential_eq (r : ℕ) :
    BarFree.reducedDegreeDifferential (basis e B) r=
      BarFree.reducedDegreeDifferential B r := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change PaperVerification.ReducedBarBasis.differential (basis e B) z.val=
    PaperVerification.ReducedBarBasis.differential B z.val
  rw [differential_eq]

theorem negativeReducedDegreeDifferential_eq (r : ℕ) :
    BarFree.negativeReducedDegreeDifferential (basis e B) r=
      BarFree.negativeReducedDegreeDifferential B r := by
  apply LinearMap.ext
  intro z
  change -(BarFree.reducedDegreeDifferential (basis e B) r z)=
    -(BarFree.reducedDegreeDifferential B r z)
  rw [reducedDegreeDifferential_eq]

variable (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine normalized bar complexes are isomorphic by the identity
on every coefficient word.  No chain-map identity is assumed. -/
def reducedComplexIso :
    BarFree.reducedComplex ε B hunit hε ≅
      BarFree.reducedComplex (augmentation e ε) (basis e B)
        (basis_unit e B hunit) (augmentation_positive e ε B hε) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ Iso.refl (ModuleCat.of K (BarFree.lengthPiece I K r))) (by
    intro i j hij
    change j+1=i at hij
    subst i
    rw [BarFree.reducedComplex_d,BarFree.reducedComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change BarFree.negativeReducedDegreeDifferential (basis e B) j z=
      BarFree.negativeReducedDegreeDifferential B j z
    rw [negativeReducedDegreeDifferential_eq])

@[simp] theorem reducedComplexIso_hom_f_apply (r : ℕ)
    (z : BarFree.lengthPiece I K r) :
    ((reducedComplexIso e ε B hunit hε).hom.f r) z=z := rfl

@[simp] theorem reducedComplexIso_inv_f_apply (r : ℕ)
    (z : BarFree.lengthPiece I K r) :
    ((reducedComplexIso e ε B hunit hε).inv.f r) z=z := rfl

/-- Every degree condition on the actual coefficient words is preserved
in both directions, because the comparison keeps those words literally. -/
theorem reducedComplexIso_mem_iff (r : ℕ)
    (P : Submodule K (BarFree.lengthPiece I K r))
    (z : BarFree.lengthPiece I K r) :
    ((reducedComplexIso e ε B hunit hε).hom.f r) z∈P ↔ z∈P := Iff.rfl

/-- Ordinary derived Tor for the actual two augmented algebras, compared
through their explicit normalized free bar resolutions. -/
def torIso (r : ℕ) :
    BarFree.TorOverCoefficients ε r ≅
      BarFree.TorOverCoefficients (augmentation e ε) r :=
  BarFree.reducedBarTorIso ε B hunit hε r ≪≫
    HomologicalComplex.homologyMapIso (reducedComplexIso e ε B hunit hε) r ≪≫
    (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
      (basis_unit e B hunit) (augmentation_positive e ε B hε) r).symm

/-- The actual Tor comparison is induced by the identity-on-words bar
map, after applying the actual source and target Tor comparisons. -/
theorem sourceComparison_inv_comp_torIso (r : ℕ) :
    (BarFree.reducedBarTorIso ε B hunit hε r).inv ≫
        (torIso e ε B hunit hε r).hom=
      HomologicalComplex.homologyMap (reducedComplexIso e ε B hunit hε).hom r ≫
        (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
          (basis_unit e B hunit) (augmentation_positive e ε B hε) r).inv := by
  simp only [torIso,Iso.trans_hom,Category.assoc,Iso.inv_hom_id_assoc,
    HomologicalComplex.homologyMapIso_hom,Iso.symm_hom]

theorem map_diagonal_submodule {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N)
    (P : Submodule K M) (i j : ℕ) (hP : P=if i=j then ⊤ else ⊥) :
    P.map f.toLinearMap=if i=j then ⊤ else ⊥ := by
  rw [hP]
  split_ifs
  · rw [Submodule.map_top,LinearEquiv.range]
  · exact Submodule.map_bot _

/-- Internal Tor pieces defined by actual bar subcomplexes are carried
to their actual images in the transported bar resolution. -/
theorem subcomplex_homology_image (r : ℕ)
    (C : ChainComplex (ModuleCat K) ℕ)
    (ι : C ⟶ BarFree.reducedComplex ε B hunit hε) :
    LinearMap.range
      ((HomologicalComplex.homologyMap
          (ι ≫ (reducedComplexIso e ε B hunit hε).hom) r ≫
        (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
          (basis_unit e B hunit) (augmentation_positive e ε B hε) r).inv).hom)=
      (LinearMap.range
        ((HomologicalComplex.homologyMap ι r ≫
          (BarFree.reducedBarTorIso ε B hunit hε r).inv).hom)).map
            (torIso e ε B hunit hε r).toLinearEquiv.toLinearMap := by
  rw [←LinearMap.range_comp]
  congr 1
  change (HomologicalComplex.homologyMap
      (ι ≫ (reducedComplexIso e ε B hunit hε).hom) r ≫
        (BarFree.reducedBarTorIso (augmentation e ε) (basis e B)
          (basis_unit e B hunit) (augmentation_positive e ε B hε) r).inv).hom=
    ((HomologicalComplex.homologyMap ι r ≫
      (BarFree.reducedBarTorIso ε B hunit hε r).inv) ≫
        (torIso e ε B hunit hε r).hom).hom
  apply congrArg (fun f : C.homology r ⟶
    BarFree.TorOverCoefficients (augmentation e ε) r ↦ f.hom)
  simp only [HomologicalComplex.homologyMap_comp,Category.assoc,
    sourceComparison_inv_comp_torIso]

end PaperVerification.AlternatingForms.BarEquivTransport
end
end
end TAF_LiteralSource_0335

section TAF_LiteralSource_0336
/- Original module: PaperVerification.AlternatingFormsSectionTor -/


/-!
# Ordinary Tor of the actual complete odd Plucker section ring

The coefficient algebra here is the independently defined direct sum of
actual global twisting-sheaf sections.  The canonical graded algebra
isomorphism carries the original augmented monomial basis to that ring.
Its literal bar complex therefore computes ordinary Tor for this actual
section ring.  The internal pieces below are images of the original
homogeneous bar subcomplexes, and their equality with the transported
original Tor pieces is proved rather than used as a definition.

Every size at least two is included, including the singleton maximal
interval.  The separate one-plane polynomial boundary must be joined
before this file can support an all-size principal statement.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory HomologicalComplex MvPolynomial
open PaperVerification.ProjectiveSectionRing

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "A" => MvPolynomial (PluckerIndex (t+2) (2*k+1)) K ⧸
  isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
local notation "S" => SectionRing (oddProjectiveGrading (K := K) k t)
local notation "e" => oddCompleteSectionRingEquiv (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "ε" => oddAugmentation (K := K) k t
local notation "I" => OddPositiveStandardIndex (K := K) k t hs

/-- The actual augmentation of the complete section ring, via the
proved canonical coordinate comparison. -/
def oddSectionAugmentation : S →ₐ[K] K :=
  BarEquivTransport.augmentation e ε

/-- The genuine unit-plus-positive basis of the actual complete section
ring.  Its vectors are the actual homogeneous global sections. -/
def oddSectionAugmentedBasis : Module.Basis (Option I) K S :=
  BarEquivTransport.basis e B

@[simp] theorem oddSectionAugmentedBasis_none :
    oddSectionAugmentedBasis (K := K) k t hs none=1 :=
  BarEquivTransport.basis_unit e B (oddAugmentedBasis_none k t hs)

@[simp] theorem oddSectionAugmentation_positive (i : I) :
    oddSectionAugmentation (K := K) k t hs (oddSectionAugmentedBasis (K := K) k t hs (some i))=0 :=
  BarEquivTransport.augmentation_positive e ε B
    (oddAugmentation_positive k t hs) i

/-- These submodules are identified below with exactly the actual
degree-d direct-sum section summands, not arbitrary transported labels. -/
def oddSectionDegree (d : ℕ) : Submodule K S :=
  (oddProjectiveGrading (K := K) k t d).map (e).toLinearEquiv.toLinearMap

theorem oddSectionDegree_mem_iff (d : ℕ) (x : S) :
    x∈oddSectionDegree (K := K) k t hs d ↔
      ∃ s : sectionPiece (oddProjectiveGrading (K := K) k t) d,
        DirectSum.of (fun j ↦ sectionPiece (oddProjectiveGrading (K := K) k t) j) d s=x := by
  constructor
  · rintro ⟨r,hr,he⟩
    exact (completeSectionRingEquiv_mem_degree_iff
      (oddProjectiveGrading (K := K) k t) (odd_allSizes_bijective_toTwistingSheaf_top k t hs)
      d x).mp ⟨⟨r,hr⟩,he⟩
  · intro hx
    obtain ⟨r,hr⟩ := (completeSectionRingEquiv_mem_degree_iff
      (oddProjectiveGrading (K := K) k t) (odd_allSizes_bijective_toTwistingSheaf_top k t hs)
      d x).mpr hx
    exact ⟨r,r.2,hr⟩

theorem oddSectionAugmentedBasis_homogeneous (i : I) :
    oddSectionAugmentedBasis (K := K) k t hs (some i)∈
      oddSectionDegree (K := K) k t hs (oddPositiveDegree k t hs i) := by
  refine ⟨B (some i),?_,rfl⟩
  change B (some i)∈HomogeneousQuotientProjective.grading _ _ _
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact oddAugmentedBasis_homogeneous k t hs i

/-- The residue used by actual Tor is the original coefficient field. -/
def oddSectionResidueEquivField :
    BarFree.Residue (oddSectionAugmentation (K := K) k t hs) ≃ₐ[K] K :=
  BarFree.residueEquivCoefficients (oddSectionAugmentation (K := K) k t hs)

/-- The actual original and complete-section bar complexes have the
proved identity-on-coefficient-words comparison. -/
def oddSectionBarIso :
    BarFree.reducedComplex ε B
        (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) ≅
      BarFree.reducedComplex (oddSectionAugmentation (K := K) k t hs)
        (oddSectionAugmentedBasis (K := K) k t hs) (oddSectionAugmentedBasis_none (K := K) k t hs)
        (oddSectionAugmentation_positive (K := K) k t hs) :=
  BarEquivTransport.reducedComplexIso e ε B
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs)

/-- Ordinary Tor over the actual section algebra, computed by its
genuine normalized free bar resolution. -/
def oddSectionNormalizedBarTorIso (r : ℕ) :
    BarFree.TorOverCoefficients (oddSectionAugmentation (K := K) k t hs) r ≅
      (BarFree.reducedComplex (oddSectionAugmentation (K := K) k t hs)
        (oddSectionAugmentedBasis (K := K) k t hs) (oddSectionAugmentedBasis_none (K := K) k t hs)
        (oddSectionAugmentation_positive (K := K) k t hs)).homology r :=
  BarFree.reducedBarTorIso _ _ _ _ r

/-- This is an isomorphism of the actual derived tensor objects for
the original quotient ring and the actual complete section ring. -/
def oddSectionTorIso (r : ℕ) :
    BarFree.TorOverCoefficients ε r ≅
      BarFree.TorOverCoefficients (oddSectionAugmentation (K := K) k t hs) r :=
  BarEquivTransport.torIso e ε B
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) r

/-- Inclusion of the original homogeneous-degree subcomplex into the
genuine normalized bar complex of the complete section ring. -/
def oddSectionInternalDegreeInclusionChain (N : ℕ) :
    oddInternalDegreeComplex (K := K) k t hs N ⟶
      BarFree.reducedComplex (oddSectionAugmentation (K := K) k t hs)
        (oddSectionAugmentedBasis (K := K) k t hs) (oddSectionAugmentedBasis_none (K := K) k t hs)
        (oddSectionAugmentation_positive (K := K) k t hs) :=
  oddInternalDegreeInclusionChain k t hs N ≫ (oddSectionBarIso (K := K) k t hs).hom

/-- Literal internal-degree images in the actual ordinary Tor of the
complete section ring.  The definition uses the actual bar subcomplex,
its actual inclusion, and the proved derived-functor comparison. -/
def oddSectionTorInternalPiece (r N : ℕ) :
    Submodule K (BarFree.TorOverCoefficients (oddSectionAugmentation (K := K) k t hs) r) :=
  LinearMap.range
    ((HomologicalComplex.homologyMap (oddSectionInternalDegreeInclusionChain (K := K) k t hs N) r ≫
      (oddSectionNormalizedBarTorIso (K := K) k t hs r).inv).hom)

/-- The two genuine definitions of the corresponding Tor piece agree
through the proved ordinary-Tor isomorphism. -/
theorem oddSectionTorInternalPiece_eq_map (r N : ℕ) :
    oddSectionTorInternalPiece (K := K) k t hs r N=
      (oddTorInternalPiece k t hs r N).map
        (oddSectionTorIso (K := K) k t hs r).toLinearEquiv.toLinearMap :=
  BarEquivTransport.subcomplex_homology_image e ε B
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) r
    (oddInternalDegreeComplex k t hs N) (oddInternalDegreeInclusionChain k t hs N)

set_option maxHeartbeats 4000000 in
/-- The standard homological Koszul conclusion for the actual complete
section ring, in every homological and internal degree. -/
theorem oddSection_actual_Tor_internal_degree (r N : ℕ) :
    oddSectionTorInternalPiece (K := K) k t hs r N=if N=r then ⊤ else ⊥ := by
  exact (oddSectionTorInternalPiece_eq_map (K := K) k t hs r N).trans
    (BarEquivTransport.map_diagonal_submodule
      (oddSectionTorIso (K := K) k t hs r).toLinearEquiv
      (oddTorInternalPiece (K := K) k t hs r N) N r
      (odd_actual_Tor_internal_degree (K := K) k t hs r N))

set_option maxHeartbeats 4000000 in
/-- These genuine internal-degree images exhaust the whole actual Tor
group, excluding a vacuous choice of purported degree pieces. -/
theorem oddSectionTorInternalPieces_iSup (r : ℕ) :
    (⨆ N,oddSectionTorInternalPiece (K := K) k t hs r N)=⊤ := by
  apply top_unique
  have hd : oddSectionTorInternalPiece (K := K) k t hs r r=⊤ := by
    simpa only [ite_true] using oddSection_actual_Tor_internal_degree (K := K) k t hs r r
  rw [←hd]
  exact le_iSup (fun N ↦ oddSectionTorInternalPiece (K := K) k t hs r N) r

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0336

section TAF_LiteralSource_0337
/- Original module: PaperVerification.AlternatingFormsOnePlaneSectionTor -/


/-!
# Actual graded Tor of the one-plane complete section ring

The original variable Koszul resolution is changed to the actual complete
section algebra through the proved canonical algebra isomorphism.  The
result is an actual projective resolution over that algebra.  Its free
internal degrees remain the degrees of the original coefficient monomials
plus the exterior degree, and the coefficient monomials become the actual
homogeneous global sections.  Tensor degree pieces are defined as images
of those actual free pieces under tensoring with the coefficient residue.

The tensor comparison keeps pure tensors unchanged.  It proves both the
vanishing of the actual differentials after tensoring and the asserted
internal-degree images.  Ordinary Tor concentration then follows through
the actual derived-functor comparison.  No abstract Koszul-invariance or
unproved section-ring comparison is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.AlternatingForms.OnePlaneSectionKoszul

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open PaperVerification.ProjectiveSectionRing

universe u

variable {K : Type u} [Field K] [CharZero K] (k : ℕ)

local notation "n" => 2*k+1
local notation "A" => OnePlaneKoszul.Ring K n
local notation "Q" => OnePlaneKoszul.Residue K n
local notation "S" => SectionRing (onePlaneProjectiveGrading (K := K) k)
local notation "e" => onePlaneCompleteSectionRingEquiv (K := K) k
local notation "E" => ModuleCatRingEquivTor.scalarChange
  (AlgEquiv.toRingEquiv (onePlaneCompleteSectionRingEquiv (K := K) k))
local notation "X" => ModuleCat.of A Q

/-- The actual coefficient residue, with its scalar action changed
through the canonical complete-section algebra isomorphism. -/
abbrev coefficientModule : ModuleCat S := (E).obj X

def coefficientAugmentation : S →ₐ[K] K :=
  ((OnePlaneKoszul.residueEquivField K n).toAlgHom.comp
    (Ideal.Quotient.mkₐ K (OnePlaneKoszul.augmentationIdeal K n))).comp (e).symm.toAlgHom

/-- This is exactly the scalar action of the section algebra on its
coefficient residue, expressed in the original coefficient field. -/
theorem coefficientModule_smul (s : S) (q : coefficientModule (K := K) k) :
    OnePlaneKoszul.residueEquivField K n (s • q)=
      coefficientAugmentation (K := K) k s*OnePlaneKoszul.residueEquivField K n q := by
  have h := ModuleCatRingEquivTor.scalarChange_quotient_smul (e).toRingEquiv
    (OnePlaneKoszul.augmentationIdeal K n) s (show Q from q)
  have h' := congrArg (fun x : Q => OnePlaneKoszul.residueEquivField K n x) h
  exact h'.trans (by rw [map_mul]; rfl)

/-- The actual coefficient module is isomorphic to the original field,
with the action specified in coefficientModule_smul. -/
def coefficientFieldEquiv :
    ((ModuleCat.restrictScalars (algebraMap K S)).obj (coefficientModule (K := K) k)) ≃ₗ[K] K :=
  (ModuleCatRingEquivTor.coefficientsIso e X).toLinearEquiv.symm.trans
    ((ModuleCatRingEquivTor.nativeScalarsEquiv (R := K) (T := A) Q).trans
      (OnePlaneKoszul.residueEquivField K n).toLinearEquiv)

/-- The actual variable resolution, now a projective resolution over
the actual complete section algebra. -/
def resolution : ProjectiveResolution (coefficientModule (K := K) k) :=
  ModuleCatRingEquivTor.resolution (e).toRingEquiv (OnePlaneKoszul.resolution K n)

def tensorComplex : ChainComplex (ModuleCat S) ℕ :=
  (((tensoringLeft (ModuleCat S)).obj (coefficientModule k)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (resolution (K := K) k).complex

/-- The genuine tensor differential vanishes, as proved in the original
variable resolution and transported through the actual tensor comparison. -/
theorem tensorComplex_d (i j : ℕ) : (tensorComplex (K := K) k).d i j=0 := by
  exact ModuleCatRingEquivTor.resolutionTensor_d_eq_zero (e).toRingEquiv X X
    (OnePlaneKoszul.resolution K n) (OnePlaneKoszul.residueTensorComplex_d K n) i j

def tensorHomologyIso (r : ℕ) :
    (tensorComplex (K := K) k).homology r ≅ (tensorComplex (K := K) k).X r :=
  ModuleCatRingEquivTor.homologyIsoOfZeroDifferentials (tensorComplex (K := K) k)
    (tensorComplex_d (K := K) k) r

abbrev freeTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K S)).obj ((resolution (K := K) k).complex.X r)

abbrev tensorTermOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K S)).obj ((tensorComplex (K := K) k).X r)

/-- This is the identity on the original coefficient vectors, with the
proved compatible original-field scalar action. -/
def freeTermIso (r : ℕ) :
    OnePlaneKoszul.freeTermOverK K n r ≅ freeTermOverK (K := K) k r :=
  ModuleCatRingEquivTor.coefficientsIso e ((OnePlaneKoszul.complex K n).X r)

def tensorTermIso (r : ℕ) :
    tensorTermOverK (K := K) k r ≅ OnePlaneKoszul.tensorTermOverK K n r :=
  ModuleCatRingEquivTor.tensorIsoOverCoefficients e X ((OnePlaneKoszul.complex K n).X r)

def freeGrading (r : ℕ) : TauCeti.InternalGrading K (freeTermOverK (K := K) k r) ℕ :=
  (OnePlaneKoszul.freeGrading K n r).map (freeTermIso k r).toLinearEquiv

/-- The actual changed free basis uses the corresponding original
coefficient monomial as a literal homogeneous global section. -/
theorem freeMonomial_image (r : ℕ) (d : Fin n →₀ ℕ)
    (I : Set.powersetCard (Fin n) r) :
    (freeTermIso (K := K) k r).hom (OnePlaneKoszul.freeMonomialBasis K n r (d,I))=
      e (OnePlaneKoszul.coordinateMonomial K n d) •
        (freeTermIso k r).hom (OnePlaneKoszul.freeBasis K n r I) := by
  rw [OnePlaneKoszul.freeMonomialBasis_apply]
  change OnePlaneKoszul.coordinateMonomial K n d • OnePlaneKoszul.freeBasis K n r I=
    (e).symm (e (OnePlaneKoszul.coordinateMonomial K n d)) • OnePlaneKoszul.freeBasis K n r I
  rw [(e).symm_apply_apply]

/-- Coefficient monomials really belong to the original homogeneous
pieces used to form the actual complete section ring. -/
theorem coordinateMonomial_mem_original_degree (d : Fin n →₀ ℕ) :
    OnePlaneKoszul.coordinateMonomial K n d∈onePlaneProjectiveGrading (K := K) k d.degree := by
  change OnePlaneKoszul.coordinateMonomial K n d∈HomogeneousQuotientProjective.grading _ _ _
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  simpa only [OnePlaneKoszul.coordinateBasis_apply,OnePlaneKoszul.originalDegree] using
    OnePlaneKoszul.coordinateBasis_mem_originalDegree K n d

def differentialOverK (r : ℕ) :
    freeTermOverK (K := K) k (r+1) →ₗ[K] freeTermOverK (K := K) k r :=
  ((ModuleCat.restrictScalars (algebraMap K S)).map
    ((resolution (K := K) k).complex.d (r+1) r)).hom

/-- The changed actual free resolution still preserves its original
internal degree in every homological degree. -/
theorem differentialOverK_homogeneous (r N : ℕ)
    (z : freeTermOverK (K := K) k (r+1))
    (hz : z∈(freeGrading k (r+1)).piece N) :
    differentialOverK k r z∈(freeGrading k r).piece N := by
  rw [freeGrading,TauCeti.InternalGrading.map_piece] at hz ⊢
  obtain ⟨w,hw,rfl⟩ := hz
  refine ⟨OnePlaneKoszul.differentialOverK K n r w,
    OnePlaneKoszul.differentialOverK_homogeneous K n r N w hw,?_⟩
  rfl

/-- Tensoring an actual free vector with the unit of the actual
coefficient residue, over the complete section algebra. -/
def specializeFree (r : ℕ) :
    freeTermOverK (K := K) k r →ₗ[K] tensorTermOverK (K := K) k r :=
  ((ModuleCat.restrictScalars (algebraMap K S)).map
    (ModuleCatRingEquivTor.tensorWithVector (coefficientModule (K := K) k)
      ((resolution (K := K) k).complex.X r)
      (show coefficientModule (K := K) k from (1 : Q)))).hom

theorem specializeFree_natural (r : ℕ) (z : OnePlaneKoszul.freeTermOverK K n r) :
    (tensorTermIso (K := K) k r).hom
        (specializeFree k r ((freeTermIso k r).hom z))=
      OnePlaneKoszul.specializeFree K n r z :=
  ModuleCatRingEquivTor.tensorIsoOverCoefficients_hom_tmul e X
    ((OnePlaneKoszul.complex K n).X r) (1 : Q) z

/-- The internal pieces are literal images of the homogeneous parts of
the actual changed free resolution. -/
def tensorDegreePiece (r N : ℕ) : Submodule K (tensorTermOverK (K := K) k r) :=
  ((freeGrading k r).piece N).map (specializeFree k r)

theorem map_tensorDegreePiece (r N : ℕ) :
    (tensorDegreePiece (K := K) k r N).map (tensorTermIso k r).hom.hom=
      OnePlaneKoszul.tensorDegreePiece K n r N := by
  unfold tensorDegreePiece freeGrading
  rw [TauCeti.InternalGrading.map_piece,←Submodule.map_comp,←Submodule.map_comp]
  change ((OnePlaneKoszul.freeGrading K n r).piece N).map _=
    ((OnePlaneKoszul.freeGrading K n r).piece N).map _
  congr 1

theorem tensorDegreePiece_eq (r N : ℕ) :
    tensorDegreePiece (K := K) k r N=if N=r then ⊤ else ⊥ := by
  apply Submodule.map_injective_of_injective
    (f := (tensorTermIso k r).hom.hom) (tensorTermIso k r).toLinearEquiv.injective
  rw [map_tensorDegreePiece,OnePlaneKoszul.tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr (tensorTermIso k r).toLinearEquiv.surjective).symm
  · simp only [if_neg h,Submodule.map_bot]

/-- Actual ordinary Tor over the actual complete section algebra. -/
def TorOverK (r : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K S)).obj
    (((Tor (ModuleCat S) r).obj (coefficientModule k)).obj (coefficientModule k))

/-- The actual changed resolution computes this actual derived Tor. -/
def torTermIso (r : ℕ) : TorOverK (K := K) k r ≅ tensorTermOverK (K := K) k r :=
  (ModuleCat.restrictScalars (algebraMap K S)).mapIso
    ((resolution k).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat S)).obj (coefficientModule k)) r ≪≫
        tensorHomologyIso k r)

/-- The ordinary Tor internal pieces come from the actual tensor images
above, using the actual derived-functor comparison. -/
def torInternalPiece (r N : ℕ) : Submodule K (TorOverK (K := K) k r) :=
  (tensorDegreePiece k r N).map (torTermIso k r).inv.hom

/-- Every homological and internal degree of the one-plane complete
section ring satisfies the usual homological Koszul concentration. -/
theorem actual_section_Tor_internal_degree (r N : ℕ) :
    torInternalPiece (K := K) k r N=if N=r then ⊤ else ⊥ := by
  rw [torInternalPiece,tensorDegreePiece_eq]
  by_cases h : N=r
  · simp only [if_pos h,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (torTermIso k r).toLinearEquiv.symm.surjective
  · simp only [if_neg h,Submodule.map_bot]

theorem torInternalPieces_iSup (r : ℕ) :
    (⨆ N,torInternalPiece (K := K) k r N)=⊤ := by
  apply top_unique
  have hd : torInternalPiece (K := K) k r r=⊤ := by
    simpa only [if_true] using actual_section_Tor_internal_degree (K := K) k r r
  rw [←hd]
  exact le_iSup (fun N ↦ torInternalPiece (K := K) k r N) r

end PaperVerification.AlternatingForms.OnePlaneSectionKoszul
end
end
end TAF_LiteralSource_0337

section TAF_LiteralSource_0338
/- Original module: PaperVerification.AlternatingFormsSectionPrincipal -/


/-!
# Theorem 1.3 with the actual complete Plucker section rings

The older coordinate-ring statement is retained in full. The additional
clauses identify its literal original Proj with the actual common-isotropic
normalized atlas, identify the original graded coordinate ring with the
direct sum of its actual global twisting-sheaf sections, and state the
degeneration and Koszul clauses for that actual section algebra.

The section-ring multiplication was defined independently by multiplying
actual local sections. The displayed polynomial maps use the corresponding
actual coordinate sections. Their kernels are proved to be exactly the
previous original coordinate ideals. Ordinary Tor here is genuinely Tor
over these complete section algebras, computed by their actual bar or
projective resolutions with the original homogeneous degrees.

This is a full-scope assembly candidate, not a verification certificate.
Its complete canonical module closure and actual proof bodies remain to be
checked. Every positive plane dimension, the one-plane boundary, and the
maximal singleton interval are included.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial AlgebraicGeometry CategoryTheory
open PaperVerification.ProjectiveSectionRing
open PaperVerification.WeightedInitialFiber

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Flatness and both fibers, with the original nonzero fiber identified
with the separately defined actual complete section algebra. -/
def WeightedFlatDegenerationTo {σ τ : Type*}
    (Q : Ideal (MvPolynomial σ K)) (w : σ → ℕ)
    (J : Ideal (MvPolynomial τ K))
    (S : Type*) [CommRing S] [Algebra K S] : Prop :=
  Module.Flat (Polynomial K) (reesAlgebra Q w) ∧
  Nonempty (ZeroFiber Q w ≃ₐ[K] (MvPolynomial τ K⧸J)) ∧
  ∀ c : K,c≠0 → Nonempty (ParameterFiber Q w c ≃ₐ[K] S)

/-- The original good coordinates, as actual degree-one global sections. -/
def oddSectionGoodMap (k t : ℕ) (hs : t+2≤k+1) :
    MvPolynomial (Hibi.IntervalIndex (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs)) K →ₐ[K]
      SectionRing (oddProjectiveGrading (K := K) k t) :=
  (oddCompleteSectionRingEquiv (K := K) k t hs).toAlgHom.comp (oddGoodMap (K := K) k t hs)

theorem oddSectionGoodMap_surjective (k t : ℕ) (hs : t+2≤k+1) :
    Function.Surjective (oddSectionGoodMap (K := K) k t hs) :=
  (oddCompleteSectionRingEquiv (K := K) k t hs).surjective.comp (oddGoodMap_surjective k t hs)

theorem oddSectionGoodMap_kernel (k t : ℕ) (hs : t+2≤k+1) :
    RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom=
      oddGoodIdeal (K := K) k t hs := by
  ext p
  change oddCompleteSectionRingEquiv (K := K) k t hs (oddGoodMap (K := K) k t hs p)=0 ↔
    oddGoodMap (K := K) k t hs p=0
  exact (oddCompleteSectionRingEquiv (K := K) k t hs).map_eq_zero_iff

theorem oddSectionGoodMap_coordinate (k t : ℕ) (hs : t+2≤k+1)
    (I : Hibi.IntervalIndex (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs)) :
    oddSectionGoodMap (K := K) k t hs (X I)=
      DirectSum.of (fun d ↦ ↥(sectionPiece (oddProjectiveGrading (K := K) k t) d)) 1
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (1 : ℤ)=1) ⊤
          ⟨oddGoodMap (K := K) k t hs (X I),odd_goodCoordinate_degree_one k t hs I⟩) :=
  oddCompleteSectionRingEquiv_homogeneous k t hs 1
    ⟨oddGoodMap (K := K) k t hs (X I),odd_goodCoordinate_degree_one k t hs I⟩

theorem oddSectionGoodMap_quadratic (k t : ℕ) (hs : t+2≤k+1) :
    HasQuadraticGroebnerBasis
      (RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom) := by
  rw [oddSectionGoodMap_kernel]
  exact (odd_higherPlane_conclusions k t hs).quadratic

theorem odd_section_richardson_flat (k t : ℕ) (hs : t+2≤k+1) :
    WeightedFlatDegenerationTo
      (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms (K := K) k))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k (t+2) hs)
        (oddIntervalUpper k (t+2) hs))
      (SectionRing (oddProjectiveGrading (K := K) k t)) :=
  ⟨(odd_richardson_flat_family k t hs).1,
    (odd_richardson_flat_family k t hs).2.1,
    fun c hc ↦ ⟨(oddRichardsonNonzeroFiberEquiv k t c hc).trans
      (oddCompleteSectionRingEquiv (K := K) k t hs)⟩⟩

/-- The actual one-plane coordinate sections. -/
def onePlaneSectionCoordinateMap (k : ℕ) :
    MvPolynomial (PluckerIndex 1 (2*k+1)) K →ₐ[K]
      SectionRing (onePlaneProjectiveGrading (K := K) k) :=
  (onePlaneCompleteSectionRingEquiv (K := K) k).toAlgHom.comp
    (Ideal.Quotient.mkₐ K matrixPluckerIdeal)

theorem onePlaneSectionCoordinateMap_surjective (k : ℕ) :
    Function.Surjective (onePlaneSectionCoordinateMap (K := K) k) :=
  (onePlaneCompleteSectionRingEquiv (K := K) k).surjective.comp Ideal.Quotient.mk_surjective

set_option maxHeartbeats 800000 in
theorem onePlaneSectionCoordinateMap_kernel (k : ℕ) :
    RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom=
      matrixPluckerIdeal := by
  change RingHom.ker
    ((onePlaneCompleteSectionRingEquiv (K := K) k).toRingHom.comp
      (Ideal.Quotient.mk matrixPluckerIdeal))=matrixPluckerIdeal
  exact (RingHom.ker_comp_of_injective (Ideal.Quotient.mk matrixPluckerIdeal)
    (onePlaneCompleteSectionRingEquiv (K := K) k).injective).trans Ideal.mk_ker

theorem onePlaneSectionCoordinateMap_quadratic (k : ℕ) :
    HasQuadraticGroebnerBasis
      (RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom) := by
  rw [onePlaneSectionCoordinateMap_kernel]
  exact (odd_onePlane_conclusions k).quadratic

theorem onePlane_section_richardson_flat (k : ℕ) :
    WeightedFlatDegenerationTo
      (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
      (pluckerVertexWeight (oddNatVertexWeight k))
      (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega)))
      (SectionRing (onePlaneProjectiveGrading (K := K) k)) :=
  ⟨(odd_onePlane_conclusions k).richardson.1,
    (odd_onePlane_conclusions k).richardson.2.1,
    fun c hc ↦ ⟨(nonzeroFiberEquiv _ _ c hc).trans
      (onePlaneCompleteSectionRingEquiv (K := K) k)⟩⟩

/-- The one-plane boundary, now including the actual complete section
algebra and its actual ordinary Tor in every internal degree. -/
structure OddOnePlaneSectionConclusions (k : ℕ) : Prop where
  original : OddOnePlaneConclusions (K := K) k
  complete : Nonempty
    (OnePlaneKoszul.Ring K (2*k+1) ≃ₐ[K]
      SectionRing (onePlaneProjectiveGrading (K := K) k))
  degree_comparison : ∀ d (r : onePlaneProjectiveGrading (K := K) k d),
    onePlaneCompleteSectionRingEquiv (K := K) k r=
      DirectSum.of (fun j ↦ ↥(sectionPiece (onePlaneProjectiveGrading (K := K) k) j)) d
        (Proj.toTwistingSheaf (onePlaneProjectiveGrading (K := K) k)
          (rfl : (d : ℤ)=d) ⊤ r)
  charts : ∀ p : PluckerIndex 1 (2*k+1),Nonempty
    ((Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p))).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (PluckerChartVariable p) K)))
  cover : (⨆ p : PluckerIndex 1 (2*k+1),
    Proj.basicOpen (onePlaneProjectiveGrading (K := K) k)
      (Ideal.Quotient.mk matrixPluckerIdeal (X p)))=⊤
  coordinates : Function.Surjective (onePlaneSectionCoordinateMap (K := K) k)
  coordinate_kernel : RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom=
    matrixPluckerIdeal
  quadratic : HasQuadraticGroebnerBasis
    (RingHom.ker (onePlaneSectionCoordinateMap (K := K) k).toRingHom)
  richardson : WeightedFlatDegenerationTo
    (matrixPluckerIdeal (K := K) (s := 1) (n := 2*k+1))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
      (oddIntervalUpper k 1 (by omega)))
    (SectionRing (onePlaneProjectiveGrading (K := K) k))
  tor_exhaustive : ∀ r,(⨆ N,OnePlaneSectionKoszul.torInternalPiece (K := K) k r N)=⊤
  koszul : ∀ r N,OnePlaneSectionKoszul.torInternalPiece (K := K) k r N=
    if N=r then ⊤ else ⊥

theorem odd_onePlane_section_conclusions (k : ℕ) :
    OddOnePlaneSectionConclusions (K := K) k :=
  ⟨odd_onePlane_conclusions k,⟨onePlaneCompleteSectionRingEquiv (K := K) k⟩,
    onePlaneCompleteSectionRingEquiv_homogeneous k,
    fun p ↦ ⟨onePlaneProjBasicOpenIso k p⟩,onePlaneProjBasicOpen_cover k,
    onePlaneSectionCoordinateMap_surjective k,onePlaneSectionCoordinateMap_kernel k,
    onePlaneSectionCoordinateMap_quadratic k,onePlane_section_richardson_flat k,
    OnePlaneSectionKoszul.torInternalPieces_iSup k,
    OnePlaneSectionKoszul.actual_section_Tor_internal_degree k⟩

/-- Every higher positive plane dimension, including the maximal singleton
interval, with the actual original scheme and actual complete section algebra. -/
structure OddHigherPlaneSectionConclusions (k t : ℕ) (hs : t+2≤k+1) : Prop where
  original : OddHigherPlaneConclusions (K := K) k t hs
  exact_equations : NormalizedHomogeneousProjOverlap.equationIdeal
    (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k))=
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)
  same_scheme : Proj (NormalizedHomogeneousProjOverlap.grading
    (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)))=
      Proj (oddProjectiveGrading (K := K) k t)
  charts : ∀ p : PluckerIndex (t+2) (2*k+1),Nonempty
    ((Proj.basicOpen (oddProjectiveGrading (K := K) k t)
      (Ideal.Quotient.mk (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) (X p))).toScheme ≅
      Spec (CommRingCat.of (IsotropicChartRing p (oddPluckerForms (K := K) k))))
  cover : (⨆ p : PluckerIndex (t+2) (2*k+1),
    Proj.basicOpen (oddProjectiveGrading (K := K) k t)
      (Ideal.Quotient.mk (isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) (X p)))=⊤
  genuine_transitions : ∀ p q : PluckerIndex (t+2) (2*k+1),
    NormalizedHomogeneousProjOverlap.actualTransition
        (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)) p q=
      (NormalizedHomogeneousChart.transitionHom
        (isotropicHomogeneousSystem (t := t) (oddPluckerForms (K := K) k)) p q).toRingHom
  complete : Nonempty
    ((MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
      isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) ≃ₐ[K]
      SectionRing (oddProjectiveGrading (K := K) k t))
  degree_comparison : ∀ d (r : oddProjectiveGrading (K := K) k t d),
    oddCompleteSectionRingEquiv (K := K) k t hs r=
      DirectSum.of (fun j ↦ ↥(sectionPiece (oddProjectiveGrading (K := K) k t) j)) d
        (Proj.toTwistingSheaf (oddProjectiveGrading (K := K) k t)
          (rfl : (d : ℤ)=d) ⊤ r)
  coordinates : Function.Surjective (oddSectionGoodMap (K := K) k t hs)
  coordinate_kernel : RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom=
    oddGoodIdeal (K := K) k t hs
  quadratic : HasQuadraticGroebnerBasis
    (RingHom.ker (oddSectionGoodMap (K := K) k t hs).toRingHom)
  richardson : WeightedFlatDegenerationTo
    (isotropicPluckerIdeal (K := K) (t := t) (oddPluckerForms (K := K) k))
    (pluckerVertexWeight (oddNatVertexWeight k))
    (intervalPluckerIdeal (oddIntervalLower k (t+2) hs)
      (oddIntervalUpper k (t+2) hs))
    (SectionRing (oddProjectiveGrading (K := K) k t))
  residue_field : Nonempty
    (BarFree.Residue (oddSectionAugmentation (K := K) k t hs) ≃ₐ[K] K)
  tor_exhaustive : ∀ r,(⨆ N,oddSectionTorInternalPiece (K := K) k t hs r N)=⊤
  koszul : ∀ r N,oddSectionTorInternalPiece (K := K) k t hs r N=
    if N=r then ⊤ else ⊥

theorem odd_higherPlane_section_conclusions (k t : ℕ) (hs : t+2≤k+1) :
    OddHigherPlaneSectionConclusions (K := K) k t hs :=
  ⟨odd_higherPlane_conclusions k t hs,
    isotropicHomogeneousSystem_ideal_eq (oddPluckerForms (K := K) k),
    isotropicHomogeneousSystem_projectiveScheme_eq (oddPluckerForms (K := K) k),
    fun p ↦ ⟨isotropicProjBasicOpenIso p (oddPluckerForms (K := K) k)⟩,
    isotropicProjBasicOpen_cover (oddPluckerForms (K := K) k),
    NormalizedHomogeneousProjOverlap.actualTransition_eq_transitionHom _,
    ⟨oddCompleteSectionRingEquiv (K := K) k t hs⟩,
    oddCompleteSectionRingEquiv_homogeneous k t hs,
    oddSectionGoodMap_surjective k t hs,oddSectionGoodMap_kernel k t hs,
    oddSectionGoodMap_quadratic k t hs,odd_section_richardson_flat k t hs,
    ⟨oddSectionResidueEquivField k t hs⟩,
    oddSectionTorInternalPieces_iSup k t hs,oddSection_actual_Tor_internal_degree k t hs⟩

/-- The literal full positive plane range. The excluded zero-plane case
is false and is never used by the positive-range theorem. -/
def OddCompleteSectionConclusions (k s : ℕ) (hs : s≤k+1) : Prop :=
  match s,hs with
  | 0,_ => False
  | 1,_ => OddOnePlaneSectionConclusions (K := K) k
  | t+2,h => OddHigherPlaneSectionConclusions (K := K) k t h

theorem odd_all_positive_section_conclusions (k s : ℕ)
    (hpos : 0<s) (hs : s≤k+1) : OddCompleteSectionConclusions (K := K) k s hs := by
  cases s with
  | zero => exact False.elim (Nat.not_lt_zero _ hpos)
  | succ s =>
    cases s with
    | zero => exact odd_onePlane_section_conclusions k
    | succ t => exact odd_higherPlane_section_conclusions k t hs

/-- The complete all-degree exterior-basis and all-positive-plane theorem,
with the literal complete section-ring form of every algebraic clause. -/
theorem paper_theorem_1_3_complete_section_ring (k : ℕ) :
    (∀ s,∃ B : Module.Basis (GoodOddIndex k s) K (OddExteriorQuotientDegree (K := K) k s),
      ∀ I,B I=Submodule.Quotient.mk
        (exteriorPower.ιMulti K s
          (fun i ↦ Pi.basisFun K (Fin (2*k+1)) (I.val.val i)))) ∧
    (∀ s (hpos : 0<s) (hs : s≤k+1),OddCompleteSectionConclusions (K := K) k s hs) :=
  ⟨paper_theorem_1_3_exterior_basis k,odd_all_positive_section_conclusions k⟩

end PaperVerification.AlternatingForms
end
end
end TAF_LiteralSource_0338

section TAF_LiteralSource_0339
/- Original module: TauCeti.Data.Sym.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Basic lemmas for symmetric powers

This file records small API extensions for Mathlib's symmetric powers, and the map
`TauCeti.Sym.ofFn` reading an ordered `n`-tuple `f : Fin n → α` as an unordered one.

`ofFn` presents `Sym α n` as a quotient of `Fin n → α`: it is surjective, and its fibres are the
orbits of the permutation action, by `TauCeti.Sym.ofFn_eq_ofFn_iff`. Nothing here is topological;
`TauCeti/Topology/Sym/Basic.lean` uses this to give `Sym α n` the quotient topology coinduced along
`ofFn`.

## Main declarations

* `TauCeti.Sym.ofFn`: the ordered tuple `f : Fin n → α` read as a point of `Sym α n`, and
  `TauCeti.Sym.ofFn_surjective`, that every unordered tuple arises this way.
* `TauCeti.Sym.map_ofFn`, `TauCeti.Sym.map_comp_ofFn` and `TauCeti.Sym.ofFn_fin_append`: `ofFn`
  intertwines postcomposition with `Sym.map`, and concatenation of ordered tuples with
  `Sym.append`.
* `TauCeti.Sym.ofFn_eq_ofFn_iff`: two ordered tuples have the same underlying unordered tuple
  exactly when one is a reindexing of the other by a permutation.
* `TauCeti.Sym.count_coe_ofFn`: the multiplicity of a value in an unordered tuple is the number
  of entries of the ordered tuple taking that value.
* `TauCeti.Sym.basepointDivisor` is the set of unordered tuples containing a fixed point;
  `TauCeti.Sym.range_cons` identifies it with the range of adjoining that point.
* `TauCeti.symFinTwoEquiv`: an unordered `d`-tuple over `Fin 2` is determined by how many of its
  entries are `0`, so there are `d + 1` of them.
-/

public section

namespace Sym

variable {X Y : Type*} {d e : ℕ}

/-- Mapping a function over an appended symmetric-power point is the append of the mapped
symmetric-power points. -/
@[simp]
theorem map_append (f : X → Y) (s : Sym X d) (t : Sym X e) :
    Sym.map f (s.append t) = (Sym.map f s).append (Sym.map f t) :=
  Subtype.ext <| by simp [Multiset.map_add]

end Sym

namespace TauCeti

namespace Sym

variable {α β : Type*} {m n : ℕ}

/-! ### Ordered tuples as unordered ones -/

/-- The ordered `n`-tuple `f : Fin n → α` read as an unordered `n`-tuple.

This is Mathlib's quotient map `Sym.ofVector` precomposed with `List.Vector.ofFn`; the `Fin n → α`
form is the one that carries a product topology, so it is the map that `Sym α n` carries the
quotient topology along in `TauCeti/Topology/Sym/Basic.lean`. -/
def ofFn (f : Fin n → α) : Sym α n :=
  Sym.ofVector (List.Vector.ofFn f)

/-- The multiset underlying `ofFn f` is the list of values of `f`. -/
@[simp]
theorem coe_ofFn (f : Fin n → α) : (ofFn f : Multiset α) = ↑(List.ofFn f) :=
  congrArg _ (List.Vector.toList_ofFn f)

/-- The multiplicity of a value in `ofFn f` is the number of entries of `f` equal to it. -/
theorem count_coe_ofFn [DecidableEq α] (f : Fin n → α) (a : α) :
    Multiset.count a (ofFn f : Multiset α) = (Finset.univ.filter fun i => f i = a).card := by
  have hmap : (ofFn f : Multiset α) = Multiset.map f Finset.univ.val := by
    simp [List.ofFn_eq_map, Finset.val_univ_fin]
  rw [hmap, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  simp only [eq_comm]

/-- The points of `ofFn f` are exactly the values of `f`. -/
@[simp]
theorem mem_ofFn {a : α} {f : Fin n → α} : a ∈ ofFn f ↔ ∃ i, f i = a := by
  rw [← _root_.Sym.mem_coe, coe_ofFn]
  simp

/-- Every unordered `n`-tuple is the image of an ordered one: `ofFn` is the quotient map
presenting `Sym α n` as a quotient of `Fin n → α`. -/
theorem ofFn_surjective : Function.Surjective (ofFn : (Fin n → α) → Sym α n) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, rfl⟩ : ∃ l : List α, (l : Multiset α) = s := ⟨s.toList, s.coe_toList⟩
  have hlen : l.length = n := by simpa using hs
  subst hlen
  exact ⟨l.get, Subtype.ext (by simp)⟩

/-- Prepending a point to an ordered tuple adjoins it to the unordered one. -/
@[simp]
theorem ofFn_cons (a : α) (f : Fin n → α) : ofFn (Fin.cons a f) = a ::ₛ ofFn f :=
  Subtype.ext <| by simp [Sym.coe_cons, List.ofFn_succ]

/-- Applying a function to every entry of an ordered tuple applies it to every point of the
unordered one. -/
@[simp]
theorem map_ofFn (f : α → β) (g : Fin n → α) : Sym.map f (ofFn g) = ofFn (f ∘ g) :=
  Sym.coe_injective <| by simp [Sym.coe_map]

/-- The compatibility of `Sym.map` with `ofFn`, as an equality of maps out of ordered tuples. -/
theorem map_comp_ofFn (f : α → β) :
    (Sym.map f : Sym α n → Sym β n) ∘ ofFn = ofFn ∘ Pi.map fun _ : Fin n => f := by
  funext g
  simp only [Function.comp_apply, map_ofFn]
  exact congrArg ofFn (funext fun _ => rfl)

/-- The range of the map on symmetric powers consists of the unordered tuples whose every point
lies in the range of the original map. -/
theorem mem_range_map (f : α → β) {w : Sym β n} :
    w ∈ Set.range (Sym.map f) ↔ ∀ b ∈ w, b ∈ Set.range f := by
  constructor
  · rintro ⟨s, rfl⟩ b hb
    rw [← _root_.Sym.mem_coe, Sym.coe_map] at hb
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hb
    exact Set.mem_range_self a
  · intro hw
    let g : {b // b ∈ w} → α := fun b => (hw b b.2).choose
    have hg : ∀ b : {b // b ∈ w}, f (g b) = b := fun b => (hw b b.2).choose_spec
    refine ⟨Sym.map g w.attach, ?_⟩
    rw [Sym.map_map]
    convert w.attach_map_coe using 1
    exact congrArg (fun h => Sym.map h w.attach) (funext hg)

/-- Concatenating two ordered tuples adjoins the two unordered ones. -/
@[simp]
theorem ofFn_fin_append (f : Fin m → α) (g : Fin n → α) :
    ofFn (Fin.append f g) = (ofFn f).append (ofFn g) :=
  Sym.coe_injective <| by simp [Sym.coe_append, List.ofFn_fin_append]

/-! ### The fibres of the quotient map -/

/-- Reindexing an ordered tuple by a permutation leaves the underlying unordered tuple unchanged. -/
theorem ofFn_comp_perm (σ : Equiv.Perm (Fin n)) (f : Fin n → α) : ofFn (f ∘ σ) = ofFn f :=
  Sym.coe_injective <| by simpa using Multiset.coe_eq_coe.2 (σ.ofFn_comp_perm f)

/-- Two ordered tuples have the same underlying unordered tuple exactly when one is a reindexing
of the other: the fibres of `ofFn` are the orbits of the permutation action. -/
theorem ofFn_eq_ofFn_iff {f g : Fin n → α} :
    ofFn f = ofFn g ↔ ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  refine ⟨fun h => ?_, ?_⟩
  · -- the two tuples take each value the same number of times, so their fibres are equinumerous
    have hcard : ∀ c : α, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← count_coe_ofFn g c, ← count_coe_ofFn f c, h]
    exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
      funext fun i => Equiv.ofFiberEquiv_map _ i⟩
  · rintro ⟨σ, rfl⟩
    exact (ofFn_comp_perm σ f).symm

/-! ### Adjoining a fixed point -/

/-- The divisor of unordered tuples containing the fixed point `a`. -/
def basepointDivisor (a : α) : Set (Sym α n) := {s | a ∈ s}

@[simp]
theorem mem_basepointDivisor {a : α} {s : Sym α n} :
    s ∈ basepointDivisor a ↔ a ∈ s := Iff.rfl

/-- No unordered tuple of length zero contains a point. -/
@[simp]
theorem basepointDivisor_zero (a : α) : (basepointDivisor a : Set (Sym α 0)) = ∅ :=
  Set.eq_empty_of_forall_notMem fun s => by simp [_root_.Sym.eq_nil_of_card_zero s]

/-- The unordered `(n + 1)`-tuples obtained by adjoining the point `a` are exactly those that
contain `a`. -/
@[simp]
theorem range_cons (a : α) :
    Set.range (Sym.cons a : Sym α n → Sym α (n + 1)) = basepointDivisor a := by
  ext s
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨t, rfl⟩
    exact Sym.mem_cons_self a t
  · obtain ⟨t, rfl⟩ := Sym.exists_cons_of_mem hs
    exact ⟨t, rfl⟩

end Sym

/-! ### Unordered tuples over a two-element type -/

/-- **A multiset of size `d` over `Fin 2` is determined by how many of its entries are `0`**, and
that count can be anything from `0` to `d`: the two counts sum to `d`, so the pair of them runs
over the antidiagonal of `d`.  This is the rank-two instance of the count
`#(Sym α d) = (#α + d - 1).choose d`. -/
noncomputable def symFinTwoEquiv (d : ℕ) : Sym (Fin 2) d ≃ Fin (d + 1) :=
  (Sym.equivNatSumOfFintype (Fin 2) d).trans <|
    ((finTwoArrowEquiv ℕ).subtypeEquiv fun _ => by
      simp [Fin.sum_univ_two, Finset.mem_antidiagonal]).trans
        (Finset.Nat.antidiagonalEquivFin d)

/-- `TauCeti.symFinTwoEquiv` is the number of entries equal to `0`. -/
@[simp]
theorem coe_symFinTwoEquiv_apply (d : ℕ) (s : Sym (Fin 2) d) :
    (symFinTwoEquiv d s : ℕ) = Multiset.count 0 (s : Multiset (Fin 2)) := (rfl)

/-- The inverse of `TauCeti.symFinTwoEquiv` spelled out: `i` many `0`s and `d - i` many `1`s. -/
@[simp]
theorem coe_symFinTwoEquiv_symm_apply (d : ℕ) (i : Fin (d + 1)) :
    (((symFinTwoEquiv d).symm i : Sym (Fin 2) d) : Multiset (Fin 2))
      = Multiset.replicate (i : ℕ) 0 + Multiset.replicate (d - (i : ℕ)) 1 := by
  simp [symFinTwoEquiv, Fin.sum_univ_two, Multiset.nsmul_singleton]

end TauCeti
end
end TAF_LiteralSource_0339

section TAF_LiteralSource_0340
/- Original module: PaperVerification.AlternatingFormsTopInterlacing -/


/-!
# Interlacing and the symmetric-power indexing set in Corollary 5.2

The selected `a` indices are zero based.  If `c` enumerates the omitted
`b` indices, the inequalities are `cᵢ ≤ aᵢ < cᵢ₊₁`.  Subtracting `i`
from both kinds of entries gives the literal weak list in the paper.
The construction is an equivalence with unordered tuples, not a cardinality
assumption.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.TopInterlacing

def abIndex (k : ℕ) : Fin k ⊕ Fin (k+1) ≃ Fin (2*k+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have h : ¬(2*i.val+1)%2=0 := by omega
        simp only [h, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr i =>
        have h : (2*i.val)%2=0 := by omega
        simp only [h, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

theorem strictMonoFin_lower {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i : Fin m) : i.val ≤ (f i).val := by
  have h : ∀ r : ℕ, ∀ hr : r<m, r ≤ (f ⟨r,hr⟩).val := by
    intro r
    induction r with
    | zero => intro hr; exact Nat.zero_le _
    | succ r ih =>
        intro hr
        have hr' : r<m := by omega
        have hp := ih hr'
        have hs := hf (show (⟨r,hr'⟩ : Fin m) < ⟨r+1,hr⟩ from Nat.lt_succ_self r)
        change (f ⟨r,hr'⟩).val < (f ⟨r+1,hr⟩).val at hs
        omega
  exact h i.val i.isLt

theorem strictMonoFin_upper {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i : Fin m) : (f i).val + m ≤ n+i.val := by
  have hr : StrictMono (fun j : Fin m => (f j.rev).rev) := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr hab))
  have h := strictMonoFin_lower _ hr i.rev
  simp only [Fin.val_rev, Fin.rev_rev] at h
  have hi := i.isLt
  have hf' := (f i).isLt
  omega

def Interlacing (p q : ℕ) :=
  {ac : (Fin p → Fin (p+q)) × (Fin (p+1) → Fin (p+q+1)) //
    StrictMono ac.1 ∧ StrictMono ac.2 ∧
      ∀ i : Fin p, (ac.2 i.castSucc).val ≤ (ac.1 i).val ∧
        (ac.1 i).val < (ac.2 i.succ).val}

def WeakWord (r q : ℕ) := {z : Fin r → Fin (q+1) // Monotone z}

instance (p q : ℕ) : Fintype (Interlacing p q) := by
  unfold Interlacing
  infer_instance
instance (r q : ℕ) : Fintype (WeakWord r q) := by
  unfold WeakWord
  infer_instance

def weakValue {p q : ℕ} (I : Interlacing p q) (j : Fin (2*p+1)) : ℕ :=
  if h : j.val%2=0 then
    (I.val.2 ⟨j.val/2, by have := j.isLt; omega⟩).val-j.val/2
  else (I.val.1 ⟨j.val/2, by have := j.isLt; omega⟩).val-j.val/2

theorem weakValue_le {p q : ℕ} (I : Interlacing p q) (j : Fin (2*p+1)) :
    weakValue I j ≤ q := by
  unfold weakValue
  split_ifs with hj
  · have h := strictMonoFin_upper I.val.2 I.property.2.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    have hl := strictMonoFin_lower I.val.2 I.property.2.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    dsimp only at h hl
    omega
  · have h := strictMonoFin_upper I.val.1 I.property.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    have hl := strictMonoFin_lower I.val.1 I.property.1
      ⟨j.val/2, by have := j.isLt; omega⟩
    dsimp only at h hl
    omega

theorem weakValue_a {p q : ℕ} (I : Interlacing p q) (i : Fin p) :
    weakValue I (abIndex p (.inl i)) = (I.val.1 i).val-i.val := by
  have h : ¬(2*i.val+1)%2=0 := by omega
  have hd : (2*i.val+1)/2=i.val := by omega
  change weakValue I (⟨2*i.val+1, by have := i.isLt; omega⟩ : Fin (2*p+1)) = _
  simp only [weakValue, h, dite_false, hd]

theorem weakValue_c {p q : ℕ} (I : Interlacing p q) (i : Fin (p+1)) :
    weakValue I (abIndex p (.inr i)) = (I.val.2 i).val-i.val := by
  have h : (2*i.val)%2=0 := by omega
  have hd : (2*i.val)/2=i.val := by omega
  change weakValue I (⟨2*i.val, by have := i.isLt; omega⟩ : Fin (2*p+1)) = _
  simp only [weakValue, h, dite_true, hd]

theorem weakValue_monotone {p q : ℕ} (I : Interlacing p q) :
    Monotone (weakValue I) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro j
  by_cases hj : j.val%2=0
  · let i : Fin p := ⟨j.val/2, by have := j.isLt; omega⟩
    have he : j.castSucc=abIndex p (.inr i.castSucc) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    have ho : j.succ=abIndex p (.inl i) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    rw [he, ho, weakValue_c, weakValue_a]
    exact Nat.sub_le_sub_right (I.property.2.2 i).1 _
  · let i : Fin p := ⟨j.val/2, by have := j.isLt; omega⟩
    have ho : j.castSucc=abIndex p (.inl i) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    have he : j.succ=abIndex p (.inr i.succ) := by
      apply Fin.ext
      dsimp [i, abIndex]
      omega
    rw [ho, he, weakValue_a, weakValue_c]
    have hi := (I.property.2.2 i).2
    have ha := strictMonoFin_lower I.val.1 I.property.1 i
    have hc := strictMonoFin_lower I.val.2 I.property.2.1 i.succ
    simp only [Fin.val_succ] at *
    omega

def toWeakWord {p q : ℕ} (I : Interlacing p q) : WeakWord (2*p+1) q :=
  ⟨fun j => ⟨weakValue I j, Nat.lt_succ_of_le (weakValue_le I j)⟩,
    fun i j hij => weakValue_monotone I hij⟩

def ofWeakWord {p q : ℕ} (z : WeakWord (2*p+1) q) : Interlacing p q :=
  ⟨(fun i => ⟨(z.val (abIndex p (.inl i))).val+i.val,
      by have := (z.val (abIndex p (.inl i))).isLt; have := i.isLt; omega⟩,
    fun i => ⟨(z.val (abIndex p (.inr i))).val+i.val,
      by have := (z.val (abIndex p (.inr i))).isLt; have := i.isLt; omega⟩), by
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have hz := z.property (show abIndex p (.inl i) ≤ abIndex p (.inl j) from by
        change 2*i.val+1≤2*j.val+1
        change i.val<j.val at hij
        omega)
      change (z.val (abIndex p (.inl i))).val ≤ (z.val (abIndex p (.inl j))).val at hz
      change i.val<j.val at hij
      change (z.val (abIndex p (.inl i))).val+i.val <
        (z.val (abIndex p (.inl j))).val+j.val
      omega
    · intro i j hij
      have hz := z.property (show abIndex p (.inr i) ≤ abIndex p (.inr j) from by
        change 2*i.val≤2*j.val
        change i.val<j.val at hij
        omega)
      change (z.val (abIndex p (.inr i))).val ≤ (z.val (abIndex p (.inr j))).val at hz
      change i.val<j.val at hij
      change (z.val (abIndex p (.inr i))).val+i.val <
        (z.val (abIndex p (.inr j))).val+j.val
      omega
    · intro i
      have hl := z.property (show abIndex p (.inr i.castSucc) ≤ abIndex p (.inl i) from by
        change 2*i.val≤2*i.val+1
        omega)
      have hr := z.property (show abIndex p (.inl i) ≤ abIndex p (.inr i.succ) from by
        change 2*i.val+1≤2*(i.val+1)
        omega)
      change (z.val (abIndex p (.inr i.castSucc))).val ≤
        (z.val (abIndex p (.inl i))).val at hl
      change (z.val (abIndex p (.inl i))).val ≤
        (z.val (abIndex p (.inr i.succ))).val at hr
      dsimp only
      simp only [Fin.val_castSucc, Fin.val_succ]
      constructor <;> omega⟩

def interlacingWeakEquiv (p q : ℕ) : Interlacing p q ≃ WeakWord (2*p+1) q where
  toFun := toWeakWord
  invFun := ofWeakWord
  left_inv I := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Fin.ext
      change weakValue I (abIndex p (.inl i))+i.val=(I.val.1 i).val
      rw [weakValue_a, Nat.sub_add_cancel (strictMonoFin_lower _ I.property.1 i)]
    · funext i
      apply Fin.ext
      change weakValue I (abIndex p (.inr i))+i.val=(I.val.2 i).val
      rw [weakValue_c, Nat.sub_add_cancel (strictMonoFin_lower _ I.property.2.1 i)]
  right_inv z := by
    apply Subtype.ext
    funext j
    obtain ⟨j,rfl⟩ := (abIndex p).surjective j
    apply Fin.ext
    cases j with
    | inl i =>
        change weakValue (ofWeakWord z) (abIndex p (.inl i)) = _
        rw [weakValue_a]
        exact Nat.add_sub_cancel _ _
    | inr i =>
        change weakValue (ofWeakWord z) (abIndex p (.inr i)) = _
        rw [weakValue_c]
        exact Nat.add_sub_cancel _ _

theorem weakToSym_injective (r q : ℕ) :
    Function.Injective (fun z : WeakWord r q => TauCeti.Sym.ofFn z.val) := by
  intro z w h
  apply Subtype.ext
  apply List.ofFn_injective
  have hp : (List.ofFn z.val).Perm (List.ofFn w.val) := by
    apply Multiset.coe_eq_coe.mp
    simpa only [TauCeti.Sym.coe_ofFn] using
      congrArg (fun x : Sym (Fin (q+1)) r => (x : Multiset (Fin (q+1)))) h
  exact hp.eq_of_pairwise' z.property.sortedLE_ofFn.pairwise w.property.sortedLE_ofFn.pairwise

theorem weakToSym_surjective (r q : ℕ) :
    Function.Surjective (fun z : WeakWord r q => TauCeti.Sym.ofFn z.val) := by
  intro s
  let L := (s : Multiset (Fin (q+1))).sort
  have hl : L.length=r := by simp [L, s.property]
  let f : Fin r → Fin (q+1) := fun i => L[i.val]'(by rw [hl]; exact i.isLt)
  have hf : List.ofFn f=L := by
    apply List.ext_getElem
    · simp [hl]
    · intro i hi hi'
      simp [f]
  have hmono : Monotone f := by
    apply List.sortedLE_ofFn_iff.mp
    rw [hf]
    exact (Multiset.pairwise_sort _ _).sortedLE
  refine ⟨⟨f,hmono⟩, ?_⟩
  change TauCeti.Sym.ofFn f=s
  apply Sym.coe_injective
  rw [TauCeti.Sym.coe_ofFn, hf]
  exact Multiset.sort_eq _ _

def weakSymEquiv (r q : ℕ) : WeakWord r q ≃ Sym (Fin (q+1)) r :=
  Equiv.ofBijective (fun z => TauCeti.Sym.ofFn z.val)
    ⟨weakToSym_injective r q, weakToSym_surjective r q⟩

/-- The actual indexing equivalence underlying the plethysm in Corollary 5.2. -/
def interlacingSymEquiv (p q : ℕ) : Interlacing p q ≃ Sym (Fin (q+1)) (2*p+1) :=
  (interlacingWeakEquiv p q).trans (weakSymEquiv (2*p+1) q)

theorem interlacing_card (p q : ℕ) :
    Fintype.card (Interlacing p q) = (2*p+q+1).choose q := by
  rw [Fintype.card_congr (interlacingSymEquiv p q), Sym.card_sym_eq_multichoose,
    Fintype.card_fin, Nat.multichoose_eq]
  rw [show q+1+(2*p+1)-1=2*p+q+1 by omega]
  simpa only [show 2*p+q+1-q=2*p+1 by omega] using
    (Nat.choose_symm (show q≤2*p+q+1 by omega))

end PaperVerification.AlternatingForms.TopInterlacing
end
end
end TAF_LiteralSource_0340

section TAF_LiteralSource_0341
/- Original module: TauCeti.LinearAlgebra.SymmetricPower.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Functoriality of symmetric tensor powers, and the symmetrization back into the tensor power

This file equips Mathlib's symmetric tensor power with the linear map induced by a linear map of
the underlying modules. It proves the expected action on pure tensors, identity law, and composition
law. It also records that a symmetric power indexed by a finite type is finitely generated when its
underlying module is.

It then builds the map back, `SymmetricPower.toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M`,
for a finite index type. The **symmetrization** `∑_σ σ` of the tensor power is constant on the
fibres of the quotient map `SymmetricPower.mk`, because reindexing a pure tensor only permutes the
terms of that sum, so it descends to the symmetric power; `toTensorPower` is that descent. It is
the exact counterpart of Mathlib's `exteriorPower.toTensorPower`, and it takes a pure symmetric
tensor to the sum of the pure tensors over all orderings of its factors.

Composing back the other way multiplies by the order of the permutation group: `mk ∘ toTensorPower`
is `(card ι)!`, because each of the `(card ι)!` reorderings becomes the same symmetric tensor
again. So as soon as `(card ι)!` is a unit -- for instance over a `ℚ`-algebra -- the symmetrization
is injective, and it identifies the symmetric power with the image of the symmetrization operator
inside the tensor power. That is the statement a Young symmetrizer of a one-row shape consumes.

## Main definitions

* `SymmetricPower.map` is the map induced on a symmetric tensor power.
* `SymmetricPower.toTensorPower` is the symmetrization, from the symmetric power back into the
  tensor power.

## Main results

* `SymmetricPower.ext`: linear maps out of a symmetric power are determined by pure tensors.
* `LinearMap.apply_mem_of_forall_symmetricPower_tprod`: a linear map out of a symmetric power
  lands in a submodule once every pure tensor does.
* `SymmetricPower.toTensorPower_tprod`: the symmetrization of a pure symmetric tensor is the sum
  of the pure tensors over all orderings of its factors.
* `SymmetricPower.mk_comp_toTensorPower`: composing the symmetrization with the quotient map is
  multiplication by `(card ι)!`.
* `SymmetricPower.toTensorPower_injective`: the symmetrization is injective once `(card ι)!` is a
  unit.
* `SymmetricPower.range_toTensorPower`: its image is the image of the symmetrization operator on
  the tensor power.
* `SymmetricPower.toTensorPower_comp_map`: the symmetrization is natural in the module.

## References

The quotient construction of `SymmetricPower`, including `SymmetricPower.mk` and
`SymmetricPower.tprod`, is from Kenny Lau's
`Mathlib.LinearAlgebra.TensorPower.Symmetric`.
-/

public section

open scoped TensorProduct

universe u v

variable {R ι : Type u} {M : Type v}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

/-- A linear map out of a symmetric power is determined by its values on pure symmetric
tensors. -/
@[ext]
theorem ext {N : Type*} [AddCommMonoid N] [Module R N] {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h := by
  refine LinearMap.ext_on (span_tprod_eq_top R ι M) ?_
  rintro _ ⟨m, rfl⟩
  exact hgh m

/-- A linear map sends every symmetric tensor into a submodule if it does so on pure tensors. -/
theorem _root_.LinearMap.apply_mem_of_forall_symmetricPower_tprod {N : Type*} [AddCommMonoid N]
    [Module R N] (f : Sym[R] ι M →ₗ[R] N) (p : Submodule R N)
    (h : ∀ m : ι → M, f (⨂ₛ[R] i, m i) ∈ p) (x : Sym[R] ι M) : f x ∈ p := by
  have hle : (⊤ : Submodule R (Sym[R] ι M)) ≤ p.comap f := by
    rw [← span_tprod_eq_top R ι M, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact h m
  exact hle Submodule.mem_top

private theorem map_rel {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    addConGen (Rel R ι M) ≤
      AddCon.ker ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom) := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      apply (AddCon.ker_rel _).2
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        PiTensorProduct.map_tprod, tprod, LinearMap.compMultilinearMap_apply,
        Function.comp_apply] using (tprod_equiv (R := R) e (f ∘ m)).symm

/-- A linear map induces a linear map on every symmetric tensor power. -/
noncomputable def map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (Rel R ι M)).lift
      ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => by
    exact congrArg (mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)

/-- The map on symmetric powers commutes with the quotient map from the tensor power. -/
@[simp]
theorem map_mk {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map f (mk R ι M x) = mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  AddCon.lift_mk' (map_rel f) x

/-- The map induced on symmetric powers sends a pure tensor to the tensor of the images. -/
@[simp]
theorem map_tprod {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (m : ι → M) :
    map f (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) := by
  simp only [tprod, LinearMap.compMultilinearMap_apply, map_mk,
    PiTensorProduct.map_tprod]

/-- The map induced by the identity is the identity on the symmetric power. -/
@[simp]
theorem map_id :
    map (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  ext m
  simp

/-- Symmetric powers preserve composition of linear maps. -/
@[simp]
theorem map_comp {N : Type*} {P : Type*}
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map (ι := ι) g).comp (map (ι := ι) f) := by
  ext m
  simp

/-- A symmetric power indexed by a finite type is finitely generated when the underlying module
is finitely generated. -/
noncomputable instance finite [Finite ι] [Module.Finite R M] : Module.Finite R (Sym[R] ι M) :=
  Module.Finite.of_surjective (mk R ι M)
    (LinearMap.range_eq_top.mp (range_mk R ι M))

end CommSemiring

/-! ### The symmetrization back into the tensor power -/

section Symmetrization

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

variable (R ι M) in
/-- The symmetrization operator `∑_σ σ` on the tensor power, permuting the tensor factors. -/
private noncomputable def symmetrizer : (⨂[R] (_ : ι), M) →ₗ[R] ⨂[R] (_ : ι), M :=
  ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap

private theorem symmetrizer_tprod (m : ι → M) :
    symmetrizer R ι M (⨂ₜ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [symmetrizer, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm ι)) _ _ fun σ => ?_
  simp

private theorem symmetrizer_rel :
    addConGen (Rel R ι M) ≤ AddCon.ker (symmetrizer R ι M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, symmetrizer_tprod]
      refine Fintype.sum_bijective (e⁻¹ * ·) (Group.mulLeft_bijective _) _ _ fun σ => ?_
      congr 1
      funext i
      simp

variable (R ι M) in
/-- **The symmetrization**, from the symmetric power back into the tensor power: the descent of
the symmetrization operator `∑_σ σ` through the quotient map `SymmetricPower.mk`.

This is the counterpart of Mathlib's `exteriorPower.toTensorPower`. -/
noncomputable def toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M where
  toFun := (addConGen (Rel R ι M)).lift (symmetrizer R ι M).toAddMonoidHom symmetrizer_rel
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (symmetrizer R ι M).map_smul r x

private theorem toTensorPower_mk' (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) = (symmetrizer R ι M).toAddMonoidHom x :=
  (rfl)

@[simp]
theorem toTensorPower_mk (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) =
      ∑ σ : Equiv.Perm ι, PiTensorProduct.reindex R (fun _ : ι => M) σ x := by
  rw [toTensorPower_mk', LinearMap.toAddMonoidHom_coe, symmetrizer, LinearMap.sum_apply]
  rfl

/-- The symmetrization of a pure symmetric tensor is the sum of the pure tensors over all
orderings of its factors. -/
@[simp]
theorem toTensorPower_tprod (m : ι → M) :
    toTensorPower R ι M (⨂ₛ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, toTensorPower_mk']
  exact symmetrizer_tprod m

private theorem toTensorPower_comp_mk :
    (toTensorPower R ι M) ∘ₗ mk R ι M =
      ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, toTensorPower_mk, LinearMap.sum_apply]
    simp only [LinearEquiv.coe_coe]

/-- The image of the symmetrization is the image of the symmetrization operator `∑_σ σ` on the
tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R ι M) =
      LinearMap.range (∑ σ : Equiv.Perm ι,
        ((PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap)) := by
  rw [← toTensorPower_comp_mk, LinearMap.range_comp, range_mk, Submodule.map_top]

/-- Symmetrizing and then projecting back to the symmetric power multiplies by `(card ι)!`: the
`(card ι)!` reorderings of a pure tensor all become the same symmetric tensor. -/
@[simp]
theorem mk_comp_toTensorPower :
    (mk R ι M) ∘ₗ (toTensorPower R ι M) =
      (Fintype.card ι).factorial • LinearMap.id (R := R) (M := Sym[R] ι M) := by
  ext m
  have h (σ : Equiv.Perm ι) : mk R ι M (⨂ₜ[R] i, m (σ i)) = ⨂ₛ[R] i, m i :=
    tprod_equiv σ m
  simp [h, Fintype.card_perm]

/-- The symmetrization is injective as soon as `(card ι)!` is a unit in the base ring, for
instance over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit ((Fintype.card ι).factorial : R)) :
    Function.Injective (toTensorPower R ι M) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the quotient map by `u⁻¹` makes it a left inverse of the symmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • mk R ι M) ?_
  rw [LinearMap.smul_comp, mk_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← hu,
    u.inv_mul, one_smul]

/-- The symmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R ι N) ∘ₗ (map (ι := ι) f) =
      (PiTensorProduct.map fun _ : ι => f) ∘ₗ (toTensorPower R ι M) := by
  ext m
  simp

end Symmetrization

end SymmetricPower
end
end TAF_LiteralSource_0341

section TAF_LiteralSource_0342
/- Original module: TauCeti.LinearAlgebra.SymmetricPower.Lift -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The universal property of the symmetric tensor power

A multilinear map `f : Mⁱ → N` that is unchanged by permuting its arguments factors uniquely
through the symmetric tensor power. This file builds that factorization,
`SymmetricPower.lift`, as the descent of `PiTensorProduct.lift f` through the quotient map
`SymmetricPower.mk`: the defining relation of the quotient identifies a pure tensor with each of
its reorderings, and `f` takes the same value on all of them.

Together with `SymmetricPower.ext`, which says that a linear map out of the symmetric power is
determined by its values on pure symmetric tensors, this says that composing with the pure
symmetric tensor `⨂ₛ` is a bijection from the linear maps `Sym[R] ι M →ₗ[R] N` onto the
permutation-invariant multilinear maps `Mⁱ → N`, for every `N`.

As a first use, prepending a fixed factor to a pure tensor is permutation-invariant in the remaining
factors, so it lifts to `SymmetricPower.consMul : M →ₗ[R] Sym[R]^k M →ₗ[R] Sym[R]^(k + 1) M`.
Since `Sym[R]^k M` is indexed by `Fin k`, this part takes the scalars in `Type`.

## Main definitions

* `SymmetricPower.lift`: the linear map on the symmetric power induced by a permutation-invariant
  multilinear map.
* `SymmetricPower.consMul`: multiplication of a symmetric tensor of degree `k` by one more
  factor, the lift of the pure tensor with that factor prepended.

## Main results

* `SymmetricPower.lift_tprod`: `lift f` agrees with `f` on pure symmetric tensors.
* `SymmetricPower.consMul_tprod` and `SymmetricPower.consMul_comm`: `consMul` prepends a factor
  to a pure tensor, and multiplications by two factors commute.
-/

public section

open scoped TensorProduct

universe u v w

variable {R ι : Type u} {M : Type v} {N : Type w}

namespace SymmetricPower

section Lift

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (f : MultilinearMap R (fun _ : ι ↦ M) N)

/-- A permutation-invariant multilinear map takes the same value on a pure tensor and on each of
its reorderings, so it is constant on the classes of the defining relation of the symmetric
power. -/
private theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) :
    addConGen (Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]
      exact (congrFun (congrArg DFunLike.coe (hf e)) m).symm

/-- **The universal property of the symmetric tensor power**: a multilinear map that is unchanged
by permuting its arguments descends to a linear map on the symmetric power. -/
noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x

/-- The descent of a multilinear map commutes with the quotient map from the tensor power. -/
@[simp]
theorem lift_mk (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (x : ⨂[R] (_ : ι), M) :
    lift f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  AddCon.lift_mk' (lift_rel f hf) x

/-- The descent of a multilinear map agrees with it on pure symmetric tensors. -/
@[simp]
theorem lift_tprod (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (m : ι → M) :
    lift f hf (⨂ₛ[R] i, m i) = f m := by
  rw [tprod, LinearMap.compMultilinearMap_apply, lift_mk, PiTensorProduct.lift.tprod]

end Lift

/-! ### Multiplication by one more factor -/

section ConsMul

variable {R : Type} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Prepending a fixed factor to a pure tensor is invariant under permutations of the remaining
factors. -/
theorem tprod_cons_perm_invariant (k : ℕ) (m : M) (e : Equiv.Perm (Fin k)) :
    ((tprod R (ι := Fin (k + 1)) (M := M)).curryLeft m).domDomCongr e =
      (tprod R).curryLeft m := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.curryLeft_apply]
  rw [← tprod_equiv (Equiv.Perm.decomposeFin.symm (0, e)) (Fin.cons m v)]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [Equiv.Perm.decomposeFin_symm_apply_zero]
  | succ i => simp [Equiv.Perm.decomposeFin_symm_apply_succ]

variable (R M) in
/-- Multiplying a symmetric tensor of degree `k` by one more factor, prepended to every pure
tensor. -/
noncomputable def consMul (k : ℕ) : M →ₗ[R] Sym[R]^k M →ₗ[R] Sym[R]^(k + 1) M where
  toFun m := lift ((tprod R).curryLeft m) (tprod_cons_perm_invariant k m)
  map_add' m m' := SymmetricPower.ext fun v ↦ by
    simp [lift_tprod]
  map_smul' c m := SymmetricPower.ext fun v ↦ by
    simp [lift_tprod]

/-- Multiplying a pure symmetric tensor by one more factor prepends that factor. -/
@[simp]
theorem consMul_tprod (k : ℕ) (m : M) (v : Fin k → M) :
    consMul R M k m (⨂ₛ[R] i, v i) = ⨂ₛ[R] i, (Fin.cons m v : Fin (k + 1) → M) i := by
  simp [consMul, lift_tprod]

/-- Multiplications of a symmetric tensor by two factors commute. -/
theorem consMul_comm (k : ℕ) (m m' : M) (x : Sym[R]^k M) :
    consMul R M (k + 1) m (consMul R M k m' x) = consMul R M (k + 1) m' (consMul R M k m x) := by
  suffices h : consMul R M (k + 1) m ∘ₗ consMul R M k m' =
      consMul R M (k + 1) m' ∘ₗ consMul R M k m from LinearMap.congr_fun h x
  refine SymmetricPower.ext fun v ↦ ?_
  simp only [LinearMap.comp_apply, consMul_tprod]
  rw [← tprod_equiv (Equiv.swap 0 1) (Fin.cons m (Fin.cons m' v))]
  exact congrArg (fun f : Fin (k + 2) → M ↦ ⨂ₛ[R] i, f i)
    (Matrix.cons_cons_comp_swap_zero_one m m' v)

end ConsMul

end SymmetricPower
end
end TAF_LiteralSource_0342

section TAF_LiteralSource_0343
/- Original module: TauCeti.LinearAlgebra.SymmetricPower.Basis -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# A basis of a symmetric tensor power

A basis `b : Basis κ R M` induces a basis of every symmetric tensor power `Sym[R]^n M`, indexed by
the **unordered** `n`-tuples `Sym κ n` of basis indices: the basis vector at `s` is the pure
symmetric tensor of the basis vectors listed by `s`. This is the symmetric counterpart of
`Basis.piTensorProduct`, whose index type is the ordered tuples `Fin n → κ`, and of
`Module.Basis.exteriorPower`, whose index type is the `n`-element subsets.

The coordinate map is built from the tensor-power basis: reading a pure tensor of basis vectors as
the unordered tuple of its indices is invariant under permuting the factors, so it descends to the
symmetric power by `SymmetricPower.lift`. Its inverse sends an unordered tuple to the pure
symmetric tensor of the corresponding basis vectors, which is well defined because any two
orderings of an unordered tuple differ by a permutation.

## Main definitions

* `SymmetricPower.tprodOfSym`: the pure symmetric tensor whose factors are listed, without order,
  by a point of `Sym κ n`.
* `Module.Basis.symmetricPower`: the induced basis of `Sym[R]^n M`.

## Main results

* `Module.Basis.map_symmetricPower_of_apply`: an endomorphism diagonal in a basis is
  diagonal in the induced basis of the symmetric power, with eigenvalue the product of the
  eigenvalues listed by the index.
* `SymmetricPower.finrank_eq`: the rank of `Sym[R]^n M` is `Nat.multichoose (finrank R M) n`.
* `Module.Basis.trace_map_symmetricPower_of_apply`: the trace on `Sym[R]^n M` of an endomorphism
  that is diagonal in a basis is the sum, over the unordered `n`-tuples of basis indices, of the
  product of the corresponding eigenvalues. This is the complete homogeneous symmetric polynomial
  in the eigenvalues, and is the symmetric counterpart of
  `Module.Basis.trace_map_exteriorPower_of_apply`.
-/

public section

open Module
open scoped TensorProduct

universe v w

variable {R : Type} {M : Type v} {κ : Type w} {n : ℕ}

namespace SymmetricPower

/-- A choice of ordering of an unordered tuple: an arbitrary section of `TauCeti.Sym.ofFn`, used
only to write down a pure symmetric tensor with prescribed factors. Any two orderings of the same
unordered tuple differ by a permutation, by `TauCeti.Sym.ofFn_eq_ofFn_iff`, so the choice never
escapes into the API below. -/
private noncomputable def orderOfSym (s : Sym κ n) : Fin n → κ :=
  Function.surjInv TauCeti.Sym.ofFn_surjective s

private theorem ofFn_orderOfSym (s : Sym κ n) : TauCeti.Sym.ofFn (orderOfSym s) = s :=
  Function.surjInv_eq TauCeti.Sym.ofFn_surjective s

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-! ### Pure symmetric tensors indexed by unordered tuples -/

variable (R) in
/-- The pure symmetric tensor whose factors are the members of a family `v : κ → M` listed, with
multiplicity but without order, by a point of `Sym κ n`. -/
noncomputable def tprodOfSym (v : κ → M) (s : Sym κ n) : Sym[R]^n M :=
  ⨂ₛ[R] i, v (orderOfSym s i)

/-- Reading off an ordered tuple of factors gives the pure symmetric tensor of those factors: the
choice of ordering hidden in the definition of `tprodOfSym` does not matter. -/
@[simp]
theorem tprodOfSym_ofFn (v : κ → M) (f : Fin n → κ) :
    tprodOfSym R v (TauCeti.Sym.ofFn f) = ⨂ₛ[R] i, v (f i) := by
  obtain ⟨σ, hσ⟩ := TauCeti.Sym.ofFn_eq_ofFn_iff.1 (ofFn_orderOfSym (TauCeti.Sym.ofFn f))
  conv_rhs => rw [← hσ]
  exact (tprod_equiv (R := R) σ fun i => v (orderOfSym (TauCeti.Sym.ofFn f) i)).symm

/-! ### The coordinate map in a basis -/

variable (b : Basis κ R M)

/-- Reading a pure tensor of basis vectors as the unordered tuple of its indices, on the tensor
power. -/
private noncomputable def toFinsuppAux : (⨂[R] (_ : Fin n), M) →ₗ[R] (Sym κ n →₀ R) :=
  (Basis.piTensorProduct fun _ : Fin n => b).constr R
    fun f => Finsupp.single (TauCeti.Sym.ofFn f) 1

private theorem toFinsuppAux_tprod_basis (f : Fin n → κ) :
    toFinsuppAux b (⨂ₜ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsuppAux, ← Basis.piTensorProduct_apply, Basis.constr_basis]

/-- Permuting the factors of a pure tensor does not change the unordered tuple of its indices. -/
private theorem toFinsuppAux_reindex (e : Equiv.Perm (Fin n)) :
    (toFinsuppAux b) ∘ₗ (PiTensorProduct.reindex R (fun _ : Fin n => M) e).toLinearMap =
      toFinsuppAux b := by
  refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.piTensorProduct_apply,
    PiTensorProduct.reindex_tprod, toFinsuppAux_tprod_basis b fun i => f (e.symm i),
    toFinsuppAux_tprod_basis b f]
  exact congrArg (Finsupp.single · (1 : R)) (TauCeti.Sym.ofFn_comp_perm e.symm f)

/-- The multilinear form of the coordinate map, before descending to the symmetric power. -/
private noncomputable def toFinsuppMultilinear :
    MultilinearMap R (fun _ : Fin n ↦ M) (Sym κ n →₀ R) :=
  (toFinsuppAux b).compMultilinearMap (PiTensorProduct.tprod R)

private theorem toFinsuppMultilinear_domDomCongr (e : Equiv.Perm (Fin n)) :
    (toFinsuppMultilinear b).domDomCongr e = toFinsuppMultilinear b := by
  refine MultilinearMap.ext fun m => ?_
  have h := congrFun (congrArg DFunLike.coe (toFinsuppAux_reindex b e.symm)) (⨂ₜ[R] i, m i)
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, PiTensorProduct.reindex_tprod] at h
  simpa [toFinsuppMultilinear] using h

variable (n) in
/-- The coordinates of a symmetric tensor in the basis induced by `b`: a pure tensor of basis
vectors is sent to the unordered tuple of its indices. -/
private noncomputable def toFinsupp : Sym[R]^n M →ₗ[R] (Sym κ n →₀ R) :=
  lift (toFinsuppMultilinear b) (toFinsuppMultilinear_domDomCongr b)

private theorem toFinsupp_tprod_basis (f : Fin n → κ) :
    toFinsupp n b (⨂ₛ[R] i, b (f i)) = Finsupp.single (TauCeti.Sym.ofFn f) 1 := by
  rw [toFinsupp, lift_tprod, toFinsuppMultilinear, LinearMap.compMultilinearMap_apply,
    toFinsuppAux_tprod_basis]

variable (n) in
/-- The symmetric power of a free module is free on the unordered `n`-tuples of basis indices. -/
private noncomputable def linearEquivFinsupp : Sym[R]^n M ≃ₗ[R] (Sym κ n →₀ R) :=
  LinearEquiv.ofLinearMap (toFinsupp n b) (Finsupp.linearCombination R (tprodOfSym R b))
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
      rw [Finsupp.linearCombination_single, one_smul, ← ofFn_orderOfSym s, tprodOfSym_ofFn,
        toFinsupp_tprod_basis, ofFn_orderOfSym])
    (by
      apply (LinearMap.cancel_right (LinearMap.range_eq_top.1 (range_mk R (Fin n) M))).1
      refine (Basis.piTensorProduct fun _ : Fin n => b).ext fun f => ?_
      -- `⨂ₛ` is the quotient map applied to `⨂ₜ`.
      have hmk : mk R (Fin n) M (⨂ₜ[R] i, b (f i)) = ⨂ₛ[R] i, b (f i) := by
        rw [tprod, LinearMap.compMultilinearMap_apply]
      simp [hmk, toFinsupp_tprod_basis, tprodOfSym_ofFn])

private theorem linearEquivFinsupp_symm_single (s : Sym κ n) :
    (linearEquivFinsupp n b).symm (Finsupp.single s 1) = tprodOfSym R b s := by
  rw [linearEquivFinsupp, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    Finsupp.linearCombination_single, one_smul]

variable (n) in
/-- **A basis of the symmetric tensor power**: a basis of `M` induces a basis of `Sym[R]^n M`
indexed by the unordered `n`-tuples of basis indices. -/
noncomputable def _root_.Module.Basis.symmetricPower : Basis (Sym κ n) R (Sym[R]^n M) :=
  Basis.ofRepr (linearEquivFinsupp n b)

/-- The basis vector of `Sym[R]^n M` indexed by an unordered tuple `s : Sym κ n` of basis indices
is the pure symmetric tensor `SymmetricPower.tprodOfSym R b s` of the corresponding basis
vectors. -/
@[simp]
theorem _root_.Module.Basis.symmetricPower_apply (s : Sym κ n) :
    b.symmetricPower n s = tprodOfSym R b s :=
  linearEquivFinsupp_symm_single b s

/-- **An endomorphism diagonal in a basis is diagonal in the induced basis of the symmetric
power**: the basis vector indexed by `s` is an eigenvector, with eigenvalue the product of the
eigenvalues listed by `s`.  Summing these eigenvalues gives the trace,
`Module.Basis.trace_map_symmetricPower_of_apply`. -/
theorem _root_.Module.Basis.map_symmetricPower_of_apply (f : M →ₗ[R] M) (a : κ → R)
    (hf : ∀ i, f (b i) = a i • b i) (s : Sym κ n) :
    map (ι := Fin n) f (b.symmetricPower n s) =
      ((s : Multiset κ).map a).prod • b.symmetricPower n s := by
  obtain ⟨p, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  simp [hf, (tprod R).map_smul_univ, List.prod_ofFn]

/-! ### Freeness and rank -/

/-- A symmetric power of a free module is free, on the unordered tuples of basis indices. -/
instance free [Module.Free R M] : Module.Free R (Sym[R]^n M) :=
  Module.Free.of_basis ((Module.Free.chooseBasis R M).symmetricPower n)

/-- The rank of a symmetric power of a finite free module: the number of unordered `n`-tuples of
basis indices, `Nat.multichoose (finrank R M) n`. -/
theorem finrank_eq [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (Sym[R]^n M) = Nat.multichoose (Module.finrank R M) n := by
  classical
  rw [Module.finrank_eq_card_basis ((Module.Free.chooseBasis R M).symmetricPower n),
    Sym.card_sym_eq_multichoose, Module.finrank_eq_card_chooseBasisIndex]

/-! ### Traces -/

/-- If an endomorphism of a semimodule over a commutative semiring is diagonal in a finite basis,
then its trace on the `n`th symmetric power is the sum, over the unordered `n`-tuples of basis
indices, of the product of the corresponding eigenvalues. -/
theorem _root_.Module.Basis.trace_map_symmetricPower_of_apply [Fintype κ] [DecidableEq κ]
    (b : Basis κ R M) (f : M →ₗ[R] M) (a : κ → R) (n : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (Sym[R]^n M) (map (ι := Fin n) f) =
      ∑ s : Sym κ n, ((s : Multiset κ).map a).prod := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (b.symmetricPower n), Matrix.trace]
  simp_rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.map_symmetricPower_of_apply b f a hf]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

end CommSemiring

end SymmetricPower
end
end TAF_LiteralSource_0343

section TAF_LiteralSource_0344
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Standard -/
/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The standard representation of the general linear group

This file defines the tautological representation of `GL n k` on column vectors, together with
its finite-dimensional and dual forms.  Its action and character are identified with matrix-vector
multiplication and the matrix trace.

## Main definitions

* `TauCeti.stdRep`: the standard representation of `GL n k`.
* `TauCeti.stdFDRep`: the standard representation as a finite-dimensional representation.
* `TauCeti.stdDualRep`: the contragredient of the standard representation.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The standard representation of `GL n k` on column vectors. -/
def stdRep : Representation k (GL (Fin n) k) (Fin n → k) :=
  (Units.coeHom ((Fin n → k) →ₗ[k] (Fin n → k))).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- The standard representation acts by matrix-vector multiplication. -/
@[simp]
theorem stdRep_apply (g : GL (Fin n) k) :
    stdRep k n g = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) :=
  Matrix.GeneralLinearGroup.coe_toLin g

/-- Evaluation of the standard action is matrix-vector multiplication. -/
theorem stdRep_apply_apply (g : GL (Fin n) k) (v : Fin n → k) :
    stdRep k n g v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

/-- The standard representation is faithful. -/
theorem stdRep_injective : Function.Injective (stdRep k n) := by
  simpa [stdRep] using
    Units.coeHom_injective.comp Matrix.GeneralLinearGroup.toLin.injective

/-- The standard representation of `GL n k`, bundled as an object of `FDRep`. -/
noncomputable abbrev stdFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (stdRep k n)

end CommRing

section Field

variable [Field k]

/-- The character of the standard representation is the matrix trace. -/
@[simp]
theorem char_stdRep (g : GL (Fin n) k) :
    (stdRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.character, stdRep_apply, ← Matrix.toLin'_apply']
  exact Matrix.trace_toLin'_eq (g : Matrix (Fin n) (Fin n) k)

/-- The character of the bundled standard representation is the matrix trace. -/
@[simp]
theorem char_stdFDRep (g : GL (Fin n) k) :
    (stdFDRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdRep k n g

end Field

section CommRing

variable [CommRing k]

/-- The dual, or contragredient, of the standard representation. -/
noncomputable def stdDualRep :
    Representation k (GL (Fin n) k) (Module.Dual k (Fin n → k)) :=
  (stdRep k n).dual

/-- The dual standard action is the transpose of the inverse standard action. -/
@[simp]
theorem stdDualRep_apply (g : GL (Fin n) k) :
    stdDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
  rw [stdDualRep, Representation.dual_apply, stdRep_apply]

/-- The dual standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev stdDualFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (stdDualRep k n)

end CommRing

section Field

variable [Field k]

/-- The character of the dual standard representation is the trace at the inverse matrix. -/
@[simp]
theorem char_stdDualRep (g : GL (Fin n) k) : (stdDualRep k n).character g =
      Matrix.trace ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [stdDualRep, Representation.char_dual, char_stdRep]

/-- The character of the bundled dual standard representation is the inverse matrix trace. -/
@[simp]
theorem char_stdDualFDRep (g : GL (Fin n) k) : (stdDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdDualRep k n g

end Field

end TauCeti
end
end TAF_LiteralSource_0344

section TAF_LiteralSource_0345
/- Original module: TauCeti.Algebra.Group.Torsion -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Commuting with nonzero powers in groups with unique roots

Commuting with a nonzero integer or natural power is equivalent to commuting with its base.
-/

public section

namespace Commute

variable {G : Type*} [Group G] [HasUniqueRoots G] {x y : G}

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_left_iff {n : ℤ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  constructor
  · intro h
    have hconj : y⁻¹ * x * y = x := by
      apply zpow_left_injective hn
      calc
        (y⁻¹ * x * y) ^ n = y⁻¹ * x ^ n * y := by
          simpa only [inv_inv] using (conj_zpow (a := y⁻¹) (b := x) (i := n))
        _ = x ^ n := h.symm.inv_mul_cancel
    exact calc
      x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [hconj]
  · intro h
    exact h.zpow_left n

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_right_iff {n : ℤ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((zpow_left_iff hn).trans Commute.symm_iff)

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_left_iff (x := x) (y := y) hn')

/-- In a group with unique roots, an element commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using (zpow_right_iff (x := x) (y := y) hn')

end Commute
end
end TAF_LiteralSource_0345

section TAF_LiteralSource_0346
/- Original module: TauCeti.Algebra.Group.Subgroup.Centralizer -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `Subgroup.centralizer` occurs in the statement below.
-- `Commute.units_val_iff` transports commutation between units and their values.
-- `Subgroup.zpowers` occurs in `Subgroup.zpowers_le_centralizer_singleton`.

/-!
# Centralizers and maximal commutative subgroups

Centralizers of a group of units are computed on the underlying monoid: a unit centralizes another
exactly when their values commute. Mathlib has both halves —
`Subgroup.mem_centralizer_singleton_iff` turns membership into an equation, and
`Commute.units_val_iff` transports that equation between `Mˣ` and `M` — but not their combination,
which is the form every concrete centralizer computation in a matrix group starts from.

## Main results

* `TauCeti.mem_centralizer_singleton_iff_commute_val`: a unit lies in the centralizer of a unit `g`
  exactly when the two commute as elements of the monoid.
* `Subgroup.zpowers_le_centralizer_singleton`: an element's cyclic subgroup lies in its
  centralizer.
* `Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative`: a self-centralizing subgroup is
  maximal among commutative subgroups.
* `Subgroup.exists_maximal_isMulCommutative`: every commutative subgroup lies in a maximal one.
* `Subgroup.centralizer_zpow_eq` and `Subgroup.centralizer_pow_eq`: nonzero powers have the same
  centralizer as their base in groups with unique roots.
-/

public section

namespace TauCeti

/-- Membership in the centralizer of a unit `g`, read on the underlying monoid. -/
theorem mem_centralizer_singleton_iff_commute_val {M : Type*} [Monoid M] {g h : Mˣ} :
    h ∈ Subgroup.centralizer {g} ↔ Commute (g : M) (h : M) :=
  ⟨fun hh => Commute.units_val_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hh).symm,
    fun hh => Subgroup.mem_centralizer_singleton_iff.mpr (Commute.units_val_iff.mp hh).symm⟩

end TauCeti

namespace Subgroup

/-- Every abelian subgroup is contained in a maximal abelian subgroup. -/
theorem exists_maximal_isMulCommutative {G : Type*} [Group G] (H : Subgroup G)
    (hH : IsMulCommutative H) :
    ∃ M : Subgroup G, H ≤ M ∧ Maximal (fun K : Subgroup G => IsMulCommutative K) M := by
  classical
  apply zorn_le_nonempty₀ {K : Subgroup G | IsMulCommutative K} ?_ H hH
  intro c hc hcc y hy
  have : ∀ K : c, IsMulCommutative (K : Subgroup G) := fun K => hc K.2
  have hcomm : IsMulCommutative (sSup c : Subgroup G) := by
    rw [sSup_eq_iSup']
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    exact Subgroup.isMulCommutative_iSup hcc.directedOn.directed_val
  exact ⟨sSup c, hcomm, fun K hK => le_sSup hK⟩

/-- The cyclic subgroup generated by an element lies in the centralizer of that element. -/
theorem zpowers_le_centralizer_singleton {G : Type*} [Group G] (x : G) :
    zpowers x ≤ centralizer {x} :=
  zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)

/-- A self-centralizing subgroup is maximal among commutative subgroups. -/
theorem eq_of_centralizer_eq_self_of_le_of_isMulCommutative {G : Type*} [Group G]
    {S H : Subgroup G} (hS : Subgroup.centralizer (S : Set G) = S) [IsMulCommutative H]
    (hle : S ≤ H) :
    H = S :=
  le_antisymm
    (by
      rw [← hS]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [HasUniqueRoots G] (x : G)

/-- Taking a nonzero integer power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_zpow_eq {n : ℤ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  ext y
  simp only [mem_centralizer_singleton_iff, ← commute_iff_eq, Commute.zpow_right_iff hn]

/-- Taking a nonzero natural power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_pow_eq {n : ℕ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using centralizer_zpow_eq x hn'

end Subgroup
end
end TAF_LiteralSource_0346

section TAF_LiteralSource_0347
/- Original module: TauCeti.LinearAlgebra.Matrix.Diagonal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Diagonal matrices: products with matrix units, and commutation

This file records generic identities about diagonal matrices. Multiplying a rectangular matrix
unit on both sides by diagonal matrices of the corresponding row and column sizes rescales its one
nonzero entry. And a matrix commuting with a diagonal matrix has no entry away from the diagonal
wherever that diagonal matrix separates two coordinates, so a matrix commuting with a diagonal
matrix of pairwise distinct entries is itself diagonal.

Neither statement needs a unit or an associative multiplication in the entries: the first holds
over a `NonUnitalNonAssocSemiring`, and the second adds commutativity and cancellation by nonzero
elements, which is what forces the off-diagonal entries to vanish.

For linear maps between based modules, the coordinate matrix is diagonal exactly when each source
basis vector maps to the corresponding scalar multiple of the target basis vector.

## Main results

* `TauCeti.diagonal_mul_single_mul_diagonal`: multiplying `Eᵢⱼ(c)` on the left and right by
  diagonal matrices rescales its entry by the corresponding diagonal coefficients.
* `TauCeti.isUnit_diagonal_iff`: a diagonal matrix over a possibly noncommutative semiring is a
  unit exactly when its diagonal is.
* `TauCeti.isUnit_diagonal_snoc_one_iff`: `diagonal (1, …, 1, x)` is a unit exactly when `x` is.
* `TauCeti.apply_eq_zero_of_commute_diagonal`: a matrix commuting with a diagonal matrix has
  vanishing `(i, j)` entry wherever that diagonal matrix separates `i` from `j`.
* `TauCeti.isDiag_of_commute_diagonal`: a matrix commuting with a diagonal matrix of pairwise
  distinct entries is itself diagonal.
* `Module.Basis.toMatrix_eq_diagonal_iff`: a linear map has a specified diagonal matrix in two
  bases exactly when it scales the corresponding basis vectors by the diagonal entries.
-/

public section

open Matrix

namespace TauCeti

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
variable {A : Type*} [NonUnitalNonAssocSemiring A] {i : m} {j : n}

/-- Multiplying a matrix unit on the left and right by diagonal matrices rescales its nonzero
entry by the corresponding diagonal entries. -/
@[simp]
theorem diagonal_mul_single_mul_diagonal {v : m → A} {w : n → A} (c : A) :
    diagonal v * single i j c * diagonal w = single i j (v i * c * w j) := by
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

/-- A diagonal matrix is a unit exactly when its family of diagonal entries is. Unlike Mathlib's
`Matrix.isUnit_diagonal`, the entries need not commute. -/
theorem isUnit_diagonal_iff {R : Type*} [Semiring R] {v : n → R} :
    IsUnit (diagonal v) ↔ IsUnit v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map (diagonalRingHom n R)⟩
  obtain ⟨M, h₁, h₂⟩ := isUnit_iff_exists.1 h
  refine isUnit_iff_exists.2 ⟨fun i ↦ M i i, funext fun i ↦ ?_, funext fun i ↦ ?_⟩
  · simpa [diagonal_mul] using congr_fun₂ h₁ i i
  · simpa [mul_diagonal] using congr_fun₂ h₂ i i

/-- `diagonal (1, …, 1, x)` is a unit exactly when `x` is. -/
theorem isUnit_diagonal_snoc_one_iff {R : Type*} [Semiring R] {d : ℕ} (x : R) :
    IsUnit (diagonal (Fin.snoc (α := fun _ ↦ R) (1 : Fin d → R) x)) ↔ IsUnit x := by
  simp [isUnit_diagonal_iff, Pi.isUnit_iff, Fin.forall_fin_succ']

section Commute

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : Type*} [NonUnitalNonAssocCommSemiring k] [IsLeftCancelMulZero k]

/-- A matrix commuting with a diagonal matrix has vanishing `(i, j)` entry whenever the diagonal
matrix separates the coordinates `i` and `j`. -/
theorem apply_eq_zero_of_commute_diagonal {t : ι → k} {g : Matrix ι ι k}
    (hg : Commute (Matrix.diagonal t) g) {i j : ι} (hij : t i ≠ t j) : g i j = 0 := by
  have hentry : (Matrix.diagonal t * g) i j = (g * Matrix.diagonal t) i j := by rw [hg.eq]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  -- `hentry : t i * g i j = g i j * t j`; cancelling `g i j` on the left would give `t i = t j`.
  by_contra h
  exact hij (mul_left_cancel₀ h (by rw [mul_comm (g i j) (t i)]; exact hentry))

/-- **A matrix commuting with a diagonal matrix of pairwise distinct entries is diagonal.** -/
theorem isDiag_of_commute_diagonal {t : ι → k} (ht : Function.Injective t)
    {g : Matrix ι ι k} (hg : Commute (Matrix.diagonal t) g) : g.IsDiag :=
  fun _ _ hij => apply_eq_zero_of_commute_diagonal hg (ht.ne hij)

end Commute

end TauCeti

namespace Module.Basis

/-- A linear map has a specified diagonal matrix in two bases exactly when it scales the
corresponding basis vectors by the diagonal entries. -/
@[simp]
theorem toMatrix_eq_diagonal_iff
    {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (f : M →ₗ[R] N) (c : ι → R) :
    LinearMap.toMatrix b b' f = Matrix.diagonal c ↔ ∀ i, f (b i) = c i • b' i := by
  rw [← (Matrix.toLin b b').injective.eq_iff, Matrix.toLin_toMatrix]
  constructor
  · intro h i
    simpa only [Matrix.toLin_self, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using congrArg (fun g : M →ₗ[R] N => g (b i)) h
  · intro hf
    apply b.ext
    intro i
    simpa only [Matrix.toLin_self, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hf i

end Module.Basis
end
end TAF_LiteralSource_0347

section TAF_LiteralSource_0348
/- Original module: TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

-- `GL` and `Matrix.GeneralLinearGroup.det` occur in the statements below.
-- Permutation matrices provide the canonical normalizer action on diagonal matrices.
-- `MulEquiv.piUnits` identifies the units of a product with the product of the units, and is what
-- makes the diagonal embedding a homomorphism.
-- `Subgroup.centralizer` and its maximal-commutative-subgroup API occur below.
-- `Matrix.IsDiag` occurs in the statements below.
-- `Nat.card` occurs in the statement of `TauCeti.natCard_diagonalTorus`.
-- `Nat.card_units`, the number of units of a `GroupWithZero`.

/-!
# Diagonal elements of the general linear group, and the diagonal torus

A family of units indexed by a finite type `ι` is the diagonal of an invertible diagonal matrix,
and this assignment is an injective group homomorphism `TauCeti.diagGL : (ι → kˣ) →* GL ι k`.
Its entries, trace and determinant are recorded here, together with the fact that the diagonal
entries of an invertible diagonal matrix are units.

The image of `diagGL` is the **diagonal torus**

`TauCeti.diagonalTorus k n = (TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k).range`

of `GL n k`, for which three descriptions are given. As the range of an injective homomorphism
it is isomorphic to the coordinatewise units `Fin n → kˣ` (`TauCeti.diagonalTorusEquiv`), whence
its order `(q - 1)ⁿ` over a division semiring with `q` elements
(`TauCeti.natCard_diagonalTorus`). An invertible matrix lies in it exactly when it is diagonal
(`TauCeti.mem_diagonalTorus_iff`). And over a commutative semiring with cancellation by nonzero
elements and at least two units it is its own centralizer (`TauCeti.centralizer_diagonalTorus`),
hence a maximal abelian subgroup of `GL n k`.

The hypothesis that `kˣ` is nontrivial cannot be dropped: over a semiring with a single unit,
such as `𝔽₂`, the torus is trivial (`TauCeti.diagonalTorus_eq_bot`) while its centralizer is the
whole of `GL n k` (`TauCeti.centralizer_diagonalTorus_eq_top`).

A scalar matrix is central in `GL ι k` over any commutative semiring
(`TauCeti.scalar_mem_center`), and `diagGL` sends a constant family to the corresponding scalar
element (`TauCeti.diagGL_const`).

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.
* `TauCeti.diagonalTorus`: the subgroup of invertible diagonal matrices in `GL n k`.
* `TauCeti.diagonalTorusEquiv`: the identification `(Fin n → kˣ) ≃* diagonalTorus k n`.
* `TauCeti.detOneRescale`: the explicit rescaling of the first column of an invertible matrix
  that makes its determinant one.

## Main statements

* `TauCeti.isUnit_apply_of_isDiag`: the diagonal entries of an invertible diagonal matrix are
  units.
* `TauCeti.coe_inv_of_coe_eq_diagonal`: over a division ring, the inverse of an invertible
  diagonal matrix is the diagonal matrix of the inverse entries.
* `TauCeti.exists_det_eq_one_mul_map_eq_map_mul_diagGL`: a matrix intertwining another matrix with
  a diagonal matrix can be normalized to have determinant one while preserving the equation.
* `TauCeti.mem_diagonalTorus_iff`: membership in the torus is diagonality of the matrix.
* `TauCeti.mul_diagGL_of_coe_eq_permMatrix`: a permutation matrix moves past a diagonal by
  relabelling its entries.
* `TauCeti.natCard_diagonalTorus`: the torus has `(q - 1)ⁿ` elements over a division semiring
  with `q` elements.
* `TauCeti.centralizer_diagonalTorus`: the diagonal torus is its own centralizer.
* `TauCeti.mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL` and
  `TauCeti.mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL`: inside any subgroup, an element
  centralizes a family of diagonal elements exactly when its entries vanish between the
  coordinates the family separates; for a family separating all coordinates, exactly when it is
  diagonal.
* `TauCeti.centralizer_diagonalTorus_eq_top`: over a semiring with a single unit the centralizer
  is instead the whole group.
* `TauCeti.scalar_mem_center` and `TauCeti.centralizer_scalar`: a scalar matrix is central, so its
  centralizer is the whole group.
* `TauCeti.diagGL_const` and `TauCeti.notMem_range_scalar_diagGL`: the diagonal embedding sends a
  constant family to the corresponding scalar element, and it is scalar *only* there.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring k]

/-- Coordinatewise units embed in a general linear group as diagonal matrices. -/
def diagGL : (ι → kˣ) →* GL ι k :=
  (Units.map (Matrix.diagonalRingHom ι k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The matrix underlying `diagGL t` is the diagonal matrix with entries `t i`. -/
@[simp]
theorem diagGL_coe (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k) = Matrix.diagonal fun i => (t i : k) := by
  rfl

/-- The entries of `diagGL t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagGL_apply (t : ι → kˣ) (i j : ι) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  rw [diagGL_coe, Matrix.diagonal_apply]

/-- The trace of a diagonal element of the general linear group is the sum of its diagonal
entries. -/
theorem trace_diagGL (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k).trace = ∑ i, (t i : k) := by
  rw [diagGL_coe, Matrix.trace_diagonal]

/-- The diagonal embedding is injective. -/
theorem diagGL_injective : Function.Injective (diagGL (k := k) (ι := ι)) := fun t s h =>
  funext fun i => Units.ext <| by
    simpa using congrArg (fun g : GL ι k ↦ (g : Matrix ι ι k) i i) h

/-- **A constant family of units embeds as the corresponding scalar element** of the general linear
group. Together with `TauCeti.notMem_range_scalar_diagGL` this says that the diagonal embedding is
scalar exactly on the constant families. -/
@[simp]
theorem diagGL_const (a : kˣ) :
    diagGL (fun _ : ι => a) = Matrix.GeneralLinearGroup.scalar ι a :=
  Units.ext <| by rw [diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- An invertible diagonal matrix with two distinct diagonal entries is not scalar. -/
theorem notMem_range_scalar_diagGL {t : ι → kˣ} {i j : ι} (ht : t i ≠ t j) :
    (diagGL t : Matrix ι ι k) ∉ Set.range (Matrix.scalar ι) := by
  rintro ⟨c, hc⟩
  refine ht (Units.ext ?_)
  have hi : c = (t i : k) := by simpa using congrFun (congrFun hc i) i
  have hj : c = (t j : k) := by simpa using congrFun (congrFun hc j) j
  rw [← hi, ← hj]

/-- A general-linear element whose underlying matrix is the permutation matrix of `π` moves
past a diagonal matrix by relabelling its diagonal entries along `π`. -/
theorem mul_diagGL_of_coe_eq_permMatrix
    (g : GL ι k) (π : Equiv.Perm ι) (hg : (g : Matrix ι ι k) = π.permMatrix k)
    (d : ι → kˣ) :
    g * diagGL d = diagGL (d ∘ π) * g := by
  ext i j
  simp only [Units.val_mul, diagGL_coe, hg, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, Matrix.diagonal_apply]
  grind

/-- The diagonal entries of an invertible diagonal matrix are units. Unlike Mathlib's
`Matrix.isUnit_diagonal`, this assumes no commutativity of `k`. -/
theorem isUnit_apply_of_isDiag {g : GL ι k} (hg : (g : Matrix ι ι k).IsDiag) (i : ι) :
    IsUnit ((g : Matrix ι ι k) i i) := by
  have h₁ := congrFun (congrFun g.mul_inv i) i
  have h₂ := congrFun (congrFun g.inv_mul i) i
  rw [← hg.diagonal_diag, Matrix.diagonal_mul, Matrix.one_apply_eq] at h₁
  rw [← hg.diagonal_diag, Matrix.mul_diagonal, Matrix.one_apply_eq] at h₂
  exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩

/-- The **diagonal torus** of `GL n k`: the image of the coordinatewise units under `diagGL`. -/
def diagonalTorus (k : Type u) [Semiring k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  MonoidHom.range (diagGL (k := k) (ι := Fin n))

/-- Membership in the diagonal torus, read off its definition as a range: an element lies in it
exactly when it is `diagGL t` for a family of units `t`. -/
theorem mem_diagonalTorus_iff_exists_diagGL {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ ∃ t : Fin n → kˣ, diagGL t = g :=
  MonoidHom.mem_range

/-- An invertible matrix lies in the diagonal torus exactly when it is a diagonal matrix. -/
@[simp]
theorem mem_diagonalTorus_iff {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ (g : Matrix (Fin n) (Fin n) k).IsDiag := by
  refine ⟨?_, fun hg => ⟨fun i => (isUnit_apply_of_isDiag hg i).unit, Units.ext ?_⟩⟩
  · rintro ⟨t, rfl⟩
    rw [diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · rw [diagGL_coe]
    simp only [IsUnit.unit_spec]
    exact hg.diagonal_diag

/-- The diagonal torus is the group of coordinatewise units. -/
noncomputable def diagonalTorusEquiv (k : Type u) [Semiring k] (n : ℕ) :
    (Fin n → kˣ) ≃* diagonalTorus k n :=
  MonoidHom.ofInjective diagGL_injective

/-- The torus element attached to a family of units is `diagGL t`. -/
@[simp]
theorem coe_diagonalTorusEquiv_apply (t : Fin n → kˣ) :
    ((diagonalTorusEquiv k n t : diagonalTorus k n) : GL (Fin n) k) = diagGL t :=
  MonoidHom.ofInjective_apply diagGL_injective

/-- The `i`-th coordinate character of a torus element is its `(i, i)` matrix entry. -/
@[simp]
theorem coe_diagonalTorusEquiv_symm_apply (g : diagonalTorus k n) (i : Fin n) :
    (((diagonalTorusEquiv k n).symm g i : kˣ) : k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i := by
  have h : diagGL ((diagonalTorusEquiv k n).symm g) = (g : GL (Fin n) k) :=
    MonoidHom.apply_ofInjective_symm diagGL_injective g
  conv_rhs => rw [← h, diagGL_coe]
  rw [Matrix.diagonal_apply_eq]

/-- **The order of the diagonal torus**: over a division semiring with `q` elements it has
`(q - 1)ⁿ` elements, one invertible scalar per diagonal entry. Over an infinite division semiring
both sides vanish when `n > 0`. -/
theorem natCard_diagonalTorus (k : Type u) [DivisionSemiring k] (n : ℕ) :
    Nat.card (diagonalTorus k n) = (Nat.card k - 1) ^ n := by
  rw [← Nat.card_congr (diagonalTorusEquiv k n).toEquiv, Nat.card_fun, Nat.card_units,
    Nat.card_fin]

/-- An element centralizing the diagonal torus commutes, as a matrix, with every diagonal matrix
of units. -/
theorem commute_diagonal_of_mem_centralizer {g : GL (Fin n) k}
    (hg : g ∈ Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k))) (t : Fin n → kˣ) :
    Commute (Matrix.diagonal fun i => (t i : k)) (g : Matrix (Fin n) (Fin n) k) := by
  have h := congrArg Units.val <|
    Subgroup.mem_centralizer_iff.mp hg _ (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩)
  rwa [Units.val_mul, Units.val_mul, diagGL_coe] at h

section Subsingleton

variable [Subsingleton kˣ]

/-- Over a semiring with only one unit, such as `𝔽₂`, the diagonal torus is trivial. -/
theorem diagonalTorus_eq_bot : diagonalTorus k n = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro - ⟨t, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim t 1, map_one]

/-- Over a semiring with only one unit the centralizer of the diagonal torus is the whole group,
while the torus itself is trivial by `TauCeti.diagonalTorus_eq_bot`. So the hypothesis
`Nontrivial kˣ` of `TauCeti.centralizer_diagonalTorus` cannot simply be dropped: the two
subgroups differ as soon as `GL n k` is nontrivial, as it is over `𝔽₂` for `n ≥ 2`. -/
theorem centralizer_diagonalTorus_eq_top :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = ⊤ := by
  simp [diagonalTorus_eq_bot, Subgroup.centralizer_eq_top_iff_subset]

end Subsingleton

end Semiring

section CommSemiring

variable [CommSemiring k]

/-- The diagonal torus is commutative. -/
instance instIsMulCommutativeDiagonalTorus : IsMulCommutative (diagonalTorus k n) :=
  Subgroup.range_isMulCommutative _

section Scalar

/-- **A scalar matrix is central in `GL ι k`**. Mathlib's
`Matrix.GeneralLinearGroup.scalar_commute` asks for a commutative ring. -/
theorem scalar_mem_center (u : kˣ) :
    Matrix.GeneralLinearGroup.scalar ι u ∈ Subgroup.center (GL ι k) :=
  Subgroup.mem_center_iff.mpr fun g => Units.ext
    ((Matrix.scalar_commute (u : k) (fun _ => Commute.all _ _) (g : Matrix ι ι k)).symm.eq)

/-- **The centralizer of a scalar matrix is everything**, scalar matrices being central. The size of
its conjugacy class is `TauCeti.ncard_carrier_mk_scalar`, in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer`. -/
@[simp]
theorem centralizer_scalar (u : kˣ) :
    Subgroup.centralizer {Matrix.GeneralLinearGroup.scalar ι u} = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (scalar_mem_center u))

end Scalar

section IsLeftCancelMulZero

variable [IsLeftCancelMulZero k] [Nontrivial kˣ]

/-- **The diagonal torus is its own centralizer**, hence a maximal abelian subgroup of `GL n k`. -/
theorem centralizer_diagonalTorus :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = diagonalTorus k n := by
  refine le_antisymm (fun g hg => mem_diagonalTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  obtain ⟨u, v, huv⟩ := exists_pair_ne kˣ
  refine apply_eq_zero_of_commute_diagonal
    (commute_diagonal_of_mem_centralizer hg fun m => if m = i then u else v) ?_
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij)]
  exact fun h => huv (Units.ext h)

/-- A commutative subgroup of `GL n k` containing the diagonal torus equals it: this is the
maximality of the torus among abelian subgroups. -/
theorem eq_diagonalTorus_of_le_of_isMulCommutative (H : Subgroup (GL (Fin n) k))
    [IsMulCommutative H] (hle : diagonalTorus k n ≤ H) :
    H = diagonalTorus k n :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative centralizer_diagonalTorus hle

end IsLeftCancelMulZero

section FamilyCentralizer

variable [IsLeftCancelMulZero k] {X : Type*} {P : Subgroup (GL ι k)} {T : X → P}
  {f : X → ι → kˣ}

/-- **The centralizer of a family of diagonal elements.** Suppose `T` sends each `x` to an element
of a subgroup `P` of `GL ι k` whose matrix is diagonal with entries `f x`. An element of `P`
commutes with every `T x` exactly when its `(i, j)` entry vanishes whenever some `f x` takes
different values at `i` and `j`. -/
theorem mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL
    (hT : ∀ x, (T x : GL ι k) = diagGL (f x)) (g : P) :
    g ∈ Subgroup.centralizer (Set.range T) ↔
      ∀ i j, (∃ x, f x i ≠ f x j) → ((g : GL ι k) : Matrix ι ι k) i j = 0 := by
  constructor
  · rintro hg i j ⟨x, hx⟩
    have hcomm := congrArg (fun y : P ↦ ((y : GL ι k) : Matrix ι ι k))
      (Subgroup.mem_centralizer_iff.mp hg (T x) ⟨x, rfl⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, hT, diagGL_coe] at hcomm
    exact apply_eq_zero_of_commute_diagonal hcomm fun h ↦ hx (Units.ext h)
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hT, diagGL_coe]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : f x i = f x j
    · rw [hij, mul_comm]
    · rw [hg i j ⟨x, hij⟩, mul_zero, zero_mul]

/-- **An element centralizing a separating family of diagonal elements is diagonal.** If every
pair of distinct coordinates is separated by some `f x`, an element of `P` commutes with every
`T x` exactly when its matrix is diagonal. -/
theorem mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL
    (hT : ∀ x, (T x : GL ι k) = diagGL (f x))
    (hf : Pairwise fun i j ↦ ∃ x, f x i ≠ f x j) (g : P) :
    g ∈ Subgroup.centralizer (Set.range T) ↔ ((g : GL ι k) : Matrix ι ι k).IsDiag := by
  rw [mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL hT]
  refine ⟨fun h i j hij ↦ h i j (hf hij), fun h i j ⟨x, hx⟩ ↦ h ?_⟩
  rintro rfl
  exact hx rfl

end FamilyCentralizer

end CommSemiring

section DivisionRing

variable [DivisionRing k]

/-- The inverse of an invertible matrix that is the diagonal matrix of a family of scalars is the
diagonal matrix of their inverses. The scalars are automatically nonzero, by invertibility. -/
theorem coe_inv_of_coe_eq_diagonal {g : GL ι k} {d : ι → k}
    (hg : (g : Matrix ι ι k) = diagonal d) : ((g⁻¹ : GL ι k) : Matrix ι ι k) = diagonal d⁻¹ := by
  have hd (i : ι) : d i ≠ 0 := by
    have h := congrFun (congrFun g.mul_inv i) i
    rw [hg, diagonal_mul, one_apply_eq] at h
    exact left_ne_zero_of_mul_eq_one h
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [hg, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal (funext fun i => inv_mul_cancel₀ (hd i))

end DivisionRing

variable [CommRing k]

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
@[simp]
theorem det_diagGL (t : ι → kˣ) :
    Matrix.GeneralLinearGroup.det (diagGL t) = ∏ i, t i := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]

/-- Mapping the entries of `diagGL t` along a ring homomorphism gives the diagonal matrix of the
mapped units. -/
@[simp]
theorem map_diagGL {S : Type*} [CommRing S] (f : k →+* S) (t : ι → kˣ) :
    Matrix.GeneralLinearGroup.map f (diagGL t) = diagGL fun i ↦ Units.map (f : k →* S) (t i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, Units.coe_map,
    MonoidHom.coe_ofClass]
  split_ifs <;> simp

/-- Rescaling one column makes an invertible matrix have determinant one. For an empty index
type, every invertible matrix already has determinant one. -/
theorem exists_det_mul_diagGL_eq_one (P : GL ι k) :
    ∃ u : ι → kˣ, Matrix.GeneralLinearGroup.det (P * diagGL u) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact ⟨1, Units.ext <| by simp [Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨Pi.mulSingle i (Matrix.GeneralLinearGroup.det P)⁻¹, ?_⟩
  rw [map_mul, det_diagGL, Fintype.prod_pi_mulSingle' i, mul_inv_cancel]

/-- Rescale the first column of an invertible matrix by the inverse of its determinant. The
result has determinant one (`TauCeti.det_detOneRescale`), and the operation is the identity on
determinant-one matrices (`TauCeti.detOneRescale_of_det_eq_one`).

Unlike `TauCeti.exists_det_mul_diagGL_eq_one`, the rescaling is an explicit formula, so it
commutes with entrywise ring homomorphisms (`TauCeti.map_detOneRescale`): it is a morphism of
schemes `GLₙ → SLₙ`. In rank zero it is the identity. -/
def detOneRescale (g : GL (Fin n) k) : GL (Fin n) k :=
  g * diagGL fun i : Fin n ↦ if (i : ℕ) = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1

/-- The determinant-one rescaling multiplies on the right by the diagonal matrix
`diag((det g)⁻¹, 1, …, 1)`. -/
theorem detOneRescale_def (g : GL (Fin n) k) :
    detOneRescale g =
      g * diagGL fun i : Fin n ↦ if (i : ℕ) = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1 :=
  (rfl)

/-- The determinant-one rescaling has determinant one. -/
@[simp]
theorem det_detOneRescale (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (detOneRescale g) = 1 := by
  rw [detOneRescale, map_mul, det_diagGL]
  cases n with
  | zero =>
    rw [Fin.prod_univ_zero, mul_one]
    exact Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])
  | succ m =>
    rw [Fin.prod_univ_succ]
    simp

/-- The determinant-one rescaling fixes matrices of determinant one. -/
theorem detOneRescale_of_det_eq_one {g : GL (Fin n) k}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : detOneRescale g = g := by
  rw [detOneRescale, hg, inv_one]
  simp

/-- The determinant-one rescaling commutes with mapping the entries along a ring
homomorphism. -/
theorem map_detOneRescale {S : Type*} [CommRing S] (f : k →+* S) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.map f (detOneRescale g) =
      detOneRescale (Matrix.GeneralLinearGroup.map f g) := by
  rw [detOneRescale, detOneRescale, map_mul, map_diagGL, Matrix.GeneralLinearGroup.map_det]
  congr 2
  funext i
  split_ifs <;> simp

/-- If `P` intertwines `M` with a diagonal matrix, there is an intertwining matrix of determinant
one, obtained in the nonempty case by rescaling one of the columns of `P`. -/
theorem exists_det_eq_one_mul_map_eq_map_mul_diagGL {Q : Type*} [CommRing Q]
    (f : k →+* Q) (M : GL ι Q) (P : GL ι k) (t : ι → Qˣ)
    (h : M * Matrix.GeneralLinearGroup.map f P =
      Matrix.GeneralLinearGroup.map f P * diagGL t) :
    ∃ P' : GL ι k, Matrix.GeneralLinearGroup.det P' = 1 ∧
      M * Matrix.GeneralLinearGroup.map f P' =
        Matrix.GeneralLinearGroup.map f P' * diagGL t := by
  obtain ⟨u, hu⟩ := exists_det_mul_diagGL_eq_one P
  have hcomm : Commute (diagGL t) (Matrix.GeneralLinearGroup.map f (diagGL u)) := by
    rw [map_diagGL]
    exact (Commute.all _ _).map diagGL
  refine ⟨P * diagGL u, hu, ?_⟩
  rw [map_mul, ← mul_assoc, h, mul_assoc, hcomm.eq, ← mul_assoc]

/-- The determinant of an element of the diagonal torus is the product of its diagonal entries. -/
theorem det_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    (Matrix.GeneralLinearGroup.det g : k) = ∏ i, (g : Matrix (Fin n) (Fin n) k) i i := by
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← (mem_diagonalTorus_iff.mp hg).diagonal_diag, Matrix.det_diagonal]
  simp [Matrix.diag]

end TauCeti
end
end TAF_LiteralSource_0348

section TAF_LiteralSource_0349
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.Diagonal -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Diagonal elements in the standard representation

This file describes the action of the invertible diagonal matrices `TauCeti.diagGL t` in the
standard representation. These elements are the concrete points of the diagonal torus used to
compute characters and weight spaces; the matrices themselves, and the torus they form, are in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic`.

## Main statements

* `TauCeti.stdRep_diagGL_apply_basisFun`: every standard basis vector is an eigenvector of a
  diagonal matrix.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {n : ℕ}

/-- The standard representation acts at `diagGL t` by coordinatewise multiplication. -/
@[simp↓]
theorem stdRep_diagGL_apply (t : Fin n → kˣ) (v : Fin n → k) (i : Fin n) :
    stdRep k n (diagGL t) v i = (t i : k) * v i := by
  rw [stdRep_apply_apply, diagGL_coe]
  exact Matrix.mulVec_diagonal _ _ _

/-- Every standard basis vector is an eigenvector for a diagonal matrix. -/
@[simp↓]
theorem stdRep_diagGL_apply_basisFun (t : Fin n → kˣ) (i : Fin n) :
    stdRep k n (diagGL t) (Pi.basisFun k (Fin n) i) =
      (t i : k) • Pi.basisFun k (Fin n) i := by
  ext j
  rw [stdRep_diagGL_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.basisFun_apply, hji]

end TauCeti
end
end TAF_LiteralSource_0349

section TAF_LiteralSource_0350
/- Original module: TauCeti.RepresentationTheory.SymmetricPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Symmetric powers of representations

This file equips each symmetric power of a representation with the induced diagonal action.
Intertwining maps and equivalences pass functorially to symmetric powers.

## Main definitions

* `Representation.symmetricPower` is the induced action on `Sym[R]^d M`.
* `IntertwiningMap.symmetricPower` is the induced map between symmetric-power representations.
* `Representation.Equiv.symmetricPower` is the induced equivalence.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1, “Symmetric and exterior power representations”.
* The representation and equivariance constructions are adapted from the formal template in
  `TauCeti.RepresentationTheory.ExteriorPower`.
-/

public section

open scoped TensorProduct

universe v w w'

variable {R : Type} {G : Type v} {M : Type w} {N : Type w'}

namespace Representation

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M]

/-- The action induced by a representation on its `d`th symmetric power. -/
noncomputable def symmetricPower (ρ : Representation R G M) (d : ℕ) :
    Representation R G (Sym[R]^d M) where
  toFun g := SymmetricPower.map (ι := Fin d) (ρ g)
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, SymmetricPower.map_id,
      Module.End.one_eq_id]
  map_mul' g h := by
    simpa only [map_mul, Module.End.mul_eq_comp] using
      (SymmetricPower.map_comp (ι := Fin d) (ρ h) (ρ g))

/-- The action on a symmetric power is induced by the action on the original representation. -/
@[simp]
theorem symmetricPower_apply (ρ : Representation R G M) (d : ℕ) (g : G) :
    ρ.symmetricPower d g = SymmetricPower.map (ι := Fin d) (ρ g) :=
  (rfl)

/-- The symmetric-power action applies the original action to every factor of a pure tensor.

This is intentionally not a simp lemma: `symmetricPower_apply` followed by
`SymmetricPower.map_tprod` already performs this simplification. -/
theorem symmetricPower_apply_tprod (ρ : Representation R G M) (d : ℕ) (g : G) (m : Fin d → M) :
    ρ.symmetricPower d g (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, ρ g (m i) := by
  rw [symmetricPower_apply, SymmetricPower.map_tprod]

end CommSemiring

end Representation

namespace Representation.IntertwiningMap

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- An intertwining map induces an intertwining map on every symmetric power. -/
noncomputable def symmetricPower (f : IntertwiningMap ρ σ) (d : ℕ) :
    IntertwiningMap (ρ.symmetricPower d) (σ.symmetricPower d) where
  toLinearMap := SymmetricPower.map (ι := Fin d) f.toLinearMap
  isIntertwining' g := by
    rw [Representation.symmetricPower_apply, Representation.symmetricPower_apply,
      ← SymmetricPower.map_comp, ← SymmetricPower.map_comp, f.isIntertwining']

/-- The underlying linear map is the usual map induced on symmetric powers. -/
@[simp]
theorem symmetricPower_toLinearMap (f : IntertwiningMap ρ σ) (d : ℕ) :
    (f.symmetricPower d).toLinearMap =
      SymmetricPower.map (ι := Fin d) f.toLinearMap :=
  (rfl)

/-- The induced map sends a pure symmetric tensor to the tensor of the images. -/
@[simp]
theorem symmetricPower_apply_tprod (f : IntertwiningMap ρ σ) (d : ℕ) (m : Fin d → M) :
    f.symmetricPower d (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) :=
  SymmetricPower.map_tprod f.toLinearMap m

/-- Symmetric powers preserve identity intertwining maps. -/
@[simp]
theorem symmetricPower_id (d : ℕ) : (IntertwiningMap.id ρ).symmetricPower d =
      IntertwiningMap.id (ρ.symmetricPower d) := by
  apply IntertwiningMap.ext
  simp

/-- Symmetric powers preserve composition of intertwining maps. -/
@[simp]
theorem symmetricPower_comp {P : Type*} [AddCommMonoid P] [Module R P]
    {τ : Representation R G P} (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ) (d : ℕ) :
    (g.comp f).symmetricPower d = (g.symmetricPower d).comp (f.symmetricPower d) := by
  apply IntertwiningMap.ext
  exact SymmetricPower.map_comp f.toLinearMap g.toLinearMap

end CommSemiring

end Representation.IntertwiningMap

namespace Representation.Equiv

section CommSemiring

variable [CommSemiring R] [Monoid G]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ρ : Representation R G M} {σ : Representation R G N}

/-- The linear equivalence induced on `d`th symmetric powers by an equivalence of
representations. -/
private noncomputable def symmetricPowerLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (Sym[R]^d M) ≃ₗ[R] (Sym[R]^d N) :=
  LinearEquiv.ofLinearMap
    (SymmetricPower.map (ι := Fin d) e.toLinearMap)
    (SymmetricPower.map (ι := Fin d) e.symm.toLinearMap)
    (by
      rw [← SymmetricPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.comp_symm, SymmetricPower.map_id])
    (by
      rw [← SymmetricPower.map_comp, Representation.Equiv.toLinearMap_symm,
        e.toLinearEquiv.symm_comp, SymmetricPower.map_id])

private theorem symmetricPowerLinearEquiv_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (symmetricPowerLinearEquiv e d).toLinearMap =
      SymmetricPower.map (ι := Fin d) e.toLinearMap :=
  rfl

private theorem symmetricPowerLinearEquiv_symm_toLinearMap (e : ρ.Equiv σ) (d : ℕ) :
    (symmetricPowerLinearEquiv e d).symm.toLinearMap =
      SymmetricPower.map (ι := Fin d) e.symm.toLinearMap :=
  rfl

/-- An equivalence of representations induces an equivalence of every symmetric power. -/
noncomputable def symmetricPower (e : ρ.Equiv σ) (d : ℕ) :
    (ρ.symmetricPower d).Equiv (σ.symmetricPower d) :=
  .mk (symmetricPowerLinearEquiv e d) fun g => by
    rw [symmetricPowerLinearEquiv_toLinearMap]
    exact (e.toIntertwiningMap.symmetricPower d).isIntertwining' g

private theorem symmetricPower_toLinearEquiv (e : ρ.Equiv σ) (d : ℕ) :
    (e.symmetricPower d).toLinearEquiv = symmetricPowerLinearEquiv e d :=
  toLinearEquiv_mk' _

/-- The underlying linear map is the usual map induced on symmetric powers. -/
@[simp]
theorem symmetricPower_toLinearMap (e : ρ.Equiv σ) (d : ℕ) : (e.symmetricPower d).toLinearMap =
      SymmetricPower.map (ι := Fin d) e.toLinearMap :=
  (rfl)

/-- The induced equivalence sends a pure symmetric tensor to the tensor of the images. -/
@[simp]
theorem symmetricPower_apply_tprod (e : ρ.Equiv σ) (d : ℕ) (m : Fin d → M) :
    e.symmetricPower d (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, e (m i) :=
  SymmetricPower.map_tprod e.toLinearMap m

/-- Symmetric powers preserve identity equivalences. -/
@[simp]
theorem symmetricPower_refl (d : ℕ) :
    (Equiv.refl ρ).symmetricPower d = .refl (ρ.symmetricPower d) := by
  have h : ((Equiv.refl ρ).symmetricPower d).toLinearMap =
      (Equiv.refl (ρ.symmetricPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Symmetric powers preserve inverses of equivalences. -/
@[simp]
theorem symmetricPower_symm (e : ρ.Equiv σ) (d : ℕ) :
    e.symm.symmetricPower d = (e.symmetricPower d).symm := by
  have h : (e.symm.symmetricPower d).toLinearMap =
      ((e.symmetricPower d).symm).toLinearMap := by
    rw [symmetricPower_toLinearMap, toLinearMap_symm (e.symmetricPower d),
      symmetricPower_toLinearEquiv, symmetricPowerLinearEquiv_symm_toLinearMap]
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

/-- Symmetric powers preserve composition of equivalences. -/
@[simp]
theorem symmetricPower_trans {P : Type*} [AddCommMonoid P] [Module R P]
    {τ : Representation R G P} (e : ρ.Equiv σ) (f : σ.Equiv τ) (d : ℕ) :
    (e.trans f).symmetricPower d = (e.symmetricPower d).trans (f.symmetricPower d) := by
  have h : ((e.trans f).symmetricPower d).toLinearMap =
      ((e.symmetricPower d).trans (f.symmetricPower d)).toLinearMap := by
    simp
  exact Equiv.ext (funext fun x => LinearMap.congr_fun h x)

end CommSemiring

end Representation.Equiv
end
end TAF_LiteralSource_0350

section TAF_LiteralSource_0351
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Homogeneous -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The symmetric homogeneous polynomials of a fixed degree

The symmetric polynomials of `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` are graded by total
degree, each graded piece being the intersection of `MvPolynomial.symmetricSubalgebra` with the
homogeneous polynomials `MvPolynomial.homogeneousSubmodule` of that degree.  This file names that
intersection, `TauCeti.symmetricHomogeneousSubmodule`; it is the module the classical families of
symmetric polynomials are bases of, one degree at a time: the monomial symmetric polynomials over
any commutative semiring, and the Schur polynomials over a commutative ring.

## Main definitions

* `TauCeti.symmetricHomogeneousSubmodule σ R n`: the polynomials in `σ` over `R` that are both
  symmetric and homogeneous of degree `n`.

## Main results

* `TauCeti.prod_map_mem_symmetricHomogeneousSubmodule`: a multiset product of symmetric
  homogeneous factors has degree the sum of their degrees.

* `MvPolynomial.isHomogeneous_esymm`: the elementary symmetric polynomial `eₖ` is homogeneous of
  degree `k`.
* `MvPolynomial.isHomogeneous_hsymm`: the complete homogeneous symmetric polynomial `hₖ` is
  homogeneous of degree `k`.
-/

public section

namespace TauCeti

open MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] (n : ℕ)

/-- **The symmetric polynomials of degree `n`**: those polynomials in the alphabet `σ` over `R`
that are both symmetric and homogeneous of degree `n`.  The monomial symmetric polynomials of the
partitions of `n` are a basis of this module over any commutative semiring; the Schur polynomials
of those partitions are a basis of it over a commutative ring. -/
noncomputable def symmetricHomogeneousSubmodule : Submodule R (MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).toSubmodule ⊓ homogeneousSubmodule σ R n

variable {σ R n}

/-- Membership in `TauCeti.symmetricHomogeneousSubmodule` is the conjunction of the two
conditions defining it. -/
@[simp]
theorem mem_symmetricHomogeneousSubmodule {p : MvPolynomial σ R} :
    p ∈ symmetricHomogeneousSubmodule σ R n ↔ p.IsSymmetric ∧ p.IsHomogeneous n :=
  Iff.rfl

/-- A multiset product of symmetric polynomials, with the factor indexed by `k` homogeneous
of degree `k`, is symmetric and homogeneous of degree the sum of the indices. -/
theorem prod_map_mem_symmetricHomogeneousSubmodule (f : ℕ → MvPolynomial σ R)
    (hf : ∀ k, f k ∈ symmetricHomogeneousSubmodule σ R k) (s : Multiset ℕ) :
    (s.map f).prod ∈ symmetricHomogeneousSubmodule σ R s.sum := by
  apply mem_symmetricHomogeneousSubmodule.mpr
  induction s using Multiset.induction_on with
  | empty => exact ⟨IsSymmetric.one, isHomogeneous_one σ R⟩
  | cons k s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have hk := mem_symmetricHomogeneousSubmodule.mp (hf k)
    exact ⟨hk.1.mul ih.1, hk.2.mul ih.2⟩

end TauCeti

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The elementary symmetric polynomial `eₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_esymm [Fintype σ] (k : ℕ) : (esymm σ R k).IsHomogeneous k := by
  rw [esymm_eq_sum_subtype]
  refine IsHomogeneous.sum _ _ _ fun t _ => ?_
  have h := IsHomogeneous.prod (t : Finset σ) (fun i => (X i : MvPolynomial σ R)) (fun _ => 1)
    fun i _ => isHomogeneous_X R i
  rwa [Finset.sum_const, smul_eq_mul, mul_one, t.2] at h

/-- The complete homogeneous symmetric polynomial `hₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_hsymm [Fintype σ] [DecidableEq σ] (k : ℕ) :
    (hsymm σ R k).IsHomogeneous k := by
  have h (t : Multiset σ) : ((t.map X).prod : MvPolynomial σ R).IsHomogeneous t.card := by
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one σ R
    | cons a t ih => simpa [add_comm] using (isHomogeneous_X R a).mul ih
  exact IsHomogeneous.sum _ _ _ fun s _ => by simpa [s.2] using h s.1

end MvPolynomial
end
end TAF_LiteralSource_0351

section TAF_LiteralSource_0352
/- Original module: TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Evaluating the complete homogeneous symmetric polynomial

The complete homogeneous symmetric polynomial `h_d` in variables indexed by a finite type `σ` is
the sum of all monomials of degree `d`, one for each unordered `d`-tuple of indices.  Evaluating it
at a family `f : σ → R` therefore sums, over those unordered tuples, the product of the values `f`
takes on the tuple: `TauCeti.eval_hsymm`.

In two variables the unordered `d`-tuples are the `d + 1` splittings counted by
`TauCeti.symFinTwoEquiv`, and the evaluation reads `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`:
`TauCeti.eval_hsymm_fin_two`.

Reading the unordered tuples as their multiplicity functions instead writes `h_d` as the sum of the
monomials of degree `d`, indexed by `Finset.piAntidiag`: `TauCeti.hsymm_eq_sum_piAntidiag`.  Summed
over all degrees, this is the generating function `∑ₙ hₙ tⁿ = ∏ᵢ ∑ₙ xᵢⁿ tⁿ`, the product over the
variables of the geometric series `(1 - xᵢ t)⁻¹`: `TauCeti.mk_hsymm_eq_prod_mk_pow`, and
`TauCeti.mk_aeval_hsymm_eq_prod_mk_pow` at an arbitrary family of values.  On the alphabet
`σ × τ`, evaluated at products `fᵢ gⱼ`, the factors with a fixed first index multiply to
`∑ₘ fᵢᵐ hₘ(g) tᵐ`, so `hₙ(fᵢ gⱼ)` is the sum of `∏ᵢ fᵢ^{lᵢ} h_{lᵢ}(g)` over the exponent vectors
`l` on `σ` of total degree `n`: `TauCeti.aeval_hsymm_prod_eq_sum_finsuppAntidiag`.  This is the
first step of the Cauchy identity for Schur polynomials.

Determinantal formulas such as Jacobi--Trudi index `h` by integers, `h_m` being `0` for `m < 0`;
reading a negative index as `0` through a truncated subtraction of natural numbers would silently
give the wrong formula.  `TauCeti.hsymmInt` is this integer-indexed complete homogeneous symmetric
polynomial.

## Main results

* `TauCeti.eval_hsymm` evaluates the complete homogeneous symmetric polynomial as a sum over the
  unordered `d`-tuples of indices.
* `TauCeti.eval_hsymm_fin_two` reads that off in two variables: `h_d(x, y) = ∑_{i ≤ d} xⁱ y^{d-i}`.
* `TauCeti.hsymm_eq_sum_piAntidiag` writes `h_d` as the sum of the monomials of degree `d`.
* `TauCeti.mk_hsymm_eq_prod_mk_pow`: the generating function of the `h_d`, and
  `TauCeti.mk_aeval_hsymm_eq_prod_mk_pow`, the same evaluated at an arbitrary family.
* `TauCeti.aeval_hsymm_prod_eq_sum_finsuppAntidiag`: `hₙ(fᵢ gⱼ) = ∑_l ∏ᵢ fᵢ^{lᵢ} h_{lᵢ}(g)`.
* `TauCeti.hsymmPart_mem_symmetricHomogeneousSubmodule`: a product `h_ν` of complete homogeneous
  symmetric polynomials is symmetric and homogeneous of degree `n` for a partition `ν` of `n`.
* `TauCeti.hsymmInt`: the complete homogeneous symmetric polynomial `h_m` of an integer degree `m`,
  which is `0` for `m < 0`.
-/

public section

namespace TauCeti

/-- **The complete homogeneous symmetric polynomial evaluated**: `h_d(f)` is the sum, over the
unordered `d`-tuples of indices, of the product of the values `f` takes on the tuple. -/
theorem eval_hsymm {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R] (f : σ → R)
    (d : ℕ) : MvPolynomial.eval f (MvPolynomial.hsymm σ R d)
      = ∑ s : Sym σ d, ((s : Multiset σ).map f).prod := by
  rw [MvPolynomial.hsymm, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_multiset_prod, Multiset.map_map]
  simp [Function.comp_def]

/-- **The complete homogeneous symmetric polynomial in two variables**: `h_d(x, y)` is the sum of
all `d + 1` monomials `xⁱ y^{d-i}` of degree `d`. -/
theorem eval_hsymm_fin_two {R : Type*} [CommSemiring R] (f : Fin 2 → R) (d : ℕ) :
    MvPolynomial.eval f (MvPolynomial.hsymm (Fin 2) R d)
      = ∑ i ∈ Finset.range (d + 1), f 0 ^ i * f 1 ^ (d - i) := by
  rw [eval_hsymm, ← Fin.sum_univ_eq_sum_range _ (d + 1),
    ← Equiv.sum_comp (symFinTwoEquiv d).symm]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [coe_symFinTwoEquiv_symm_apply]
  simp

/-- **The monomial expansion of the complete homogeneous symmetric polynomial**: `h_d` is the sum of
the monomials `∏ᵢ X_i ^ γ_i` over the exponent vectors `γ` of total degree `d`.  This is the
multiplicity-function form of `MvPolynomial.hsymm`, whose summands are indexed by the unordered
`d`-tuples of variables. -/
theorem hsymm_eq_sum_piAntidiag {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] (d : ℕ) :
    MvPolynomial.hsymm σ R d =
      ∑ γ ∈ Finset.piAntidiag (Finset.univ : Finset σ) d,
        ∏ i, (MvPolynomial.X i : MvPolynomial σ R) ^ γ i := by
  rw [← Finset.map_sym_eq_piAntidiag, Finset.sum_map, Finset.sym_univ, MvPolynomial.hsymm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_multiset_map_count]
  refine Finset.prod_subset (Finset.subset_univ _) fun i _ hi => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), pow_zero]

/-- **The generating function of the complete homogeneous symmetric polynomials**:
`∑ₙ hₙ tⁿ = ∏ᵢ ∑ₙ xᵢⁿ tⁿ`, as power series over `MvPolynomial σ R`.  Each factor is the geometric
series `(1 - xᵢ t)⁻¹`, so the coefficient of `tⁿ` collects one monomial of degree `n` for every
exponent vector. -/
theorem mk_hsymm_eq_prod_mk_pow {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*)
    [CommSemiring R] :
    PowerSeries.mk (fun n => MvPolynomial.hsymm σ R n) =
      ∏ i, PowerSeries.mk fun n => (MvPolynomial.X i : MvPolynomial σ R) ^ n := by
  ext d
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_prod, hsymm_eq_sum_piAntidiag, Finset.finsuppAntidiag,
    Finset.sum_map, ← Finset.sum_attach (Finset.piAntidiag Finset.univ d)]
  simp

/-- **The generating function of the complete homogeneous symmetric polynomials, evaluated**:
`∑ₙ hₙ(ψ) tⁿ = ∏ᵢ ∑ₙ ψᵢⁿ tⁿ` for a family `ψ` in a commutative `R`-algebra `S`, as power series
over `S`.  This is `TauCeti.mk_hsymm_eq_prod_mk_pow` with the variables evaluated at `ψ`. -/
theorem mk_aeval_hsymm_eq_prod_mk_pow {σ R S : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring R] [CommSemiring S] [Algebra R S] (ψ : σ → S) :
    PowerSeries.mk (fun n => MvPolynomial.aeval ψ (MvPolynomial.hsymm σ R n)) =
      ∏ i, PowerSeries.mk fun n => ψ i ^ n := by
  ext d
  have h := congrArg (fun F => MvPolynomial.aeval ψ (PowerSeries.coeff d F))
    (mk_hsymm_eq_prod_mk_pow (σ := σ) R)
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_prod, map_sum, map_prod, map_pow,
    MvPolynomial.aeval_X] using h

/-- **`hₙ` of the products `fᵢ gⱼ`, grouped by the first index**: substituting `fᵢ gⱼ` for the
variable indexed by `(i, j)` in `hₙ` on the alphabet `σ × τ` gives `∑_l ∏ᵢ fᵢ^{lᵢ} h_{lᵢ}(g)`,
the sum running over the exponent vectors `l` on `σ` of total degree `n`.  In generating-function
form, the product of the geometric series `(1 - fᵢ gⱼ t)⁻¹` over all pairs is computed one `i` at a
time, the factors with a fixed `i` multiplying to `∑ₘ fᵢᵐ hₘ(g) tᵐ`. -/
theorem aeval_hsymm_prod_eq_sum_finsuppAntidiag {σ τ R S : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [DecidableEq τ] [CommSemiring R] [CommSemiring S] [Algebra R S] (f : σ → S)
    (g : τ → S) (n : ℕ) :
    MvPolynomial.aeval (fun p : σ × τ => f p.1 * g p.2) (MvPolynomial.hsymm (σ × τ) R n) =
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ n,
        ∏ i, f i ^ l i * MvPolynomial.aeval g (MvPolynomial.hsymm τ R (l i)) := by
  have hscale (i : σ) (m : ℕ) : f i ^ m * MvPolynomial.aeval g (MvPolynomial.hsymm τ R m) =
      MvPolynomial.aeval (fun j => f i * g j) (MvPolynomial.hsymm τ R m) := by
    simpa only [MvPolynomial.aeval_def] using
      ((MvPolynomial.isHomogeneous_hsymm m).eval₂_const_mul (algebraMap R S) g (f i)).symm
  have h : PowerSeries.mk (fun m => MvPolynomial.aeval (fun p : σ × τ => f p.1 * g p.2)
      (MvPolynomial.hsymm (σ × τ) R m)) =
      ∏ i, PowerSeries.mk fun m => f i ^ m * MvPolynomial.aeval g (MvPolynomial.hsymm τ R m) := by
    simp only [hscale, mk_aeval_hsymm_eq_prod_mk_pow, Fintype.prod_prod_type]
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_prod] using
    congrArg (PowerSeries.coeff n) h

/-- **A product of complete homogeneous symmetric polynomials is symmetric and homogeneous**: for
a partition `ν` of `n`, `h_ν = ∏ᵢ h_{νᵢ}` lies in `TauCeti.symmetricHomogeneousSubmodule σ R n`,
each factor `h_{νᵢ}` being symmetric and homogeneous of degree `νᵢ`. -/
theorem hsymmPart_mem_symmetricHomogeneousSubmodule {σ R : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring R] {n : ℕ} (ν : n.Partition) :
    MvPolynomial.hsymmPart σ R ν ∈ symmetricHomogeneousSubmodule σ R n := by
  rw [MvPolynomial.hsymmPart]
  simpa only [ν.parts_sum] using
    prod_map_mem_symmetricHomogeneousSubmodule (MvPolynomial.hsymm σ R)
      (fun k => mem_symmetricHomogeneousSubmodule.mpr
        ⟨MvPolynomial.hsymm_isSymmetric σ R k, MvPolynomial.isHomogeneous_hsymm k⟩) ν.parts

section hsymmInt

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

/-- The **complete homogeneous symmetric polynomial of integer degree** `m`: `h_m` for `m ≥ 0`
and `0` for `m < 0`.  This is the indexing determinantal formulas such as Jacobi--Trudi use. -/
noncomputable def hsymmInt (m : ℤ) : MvPolynomial σ R :=
  if 0 ≤ m then MvPolynomial.hsymm σ R m.toNat else 0

variable {σ R}

/-- In a nonnegative degree, `TauCeti.hsymmInt` is `MvPolynomial.hsymm`. -/
@[simp]
theorem hsymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    hsymmInt σ R m = MvPolynomial.hsymm σ R m.toNat := by
  simp [hsymmInt, hm]

/-- In a negative degree, `TauCeti.hsymmInt` vanishes. -/
@[simp]
theorem hsymmInt_of_neg {m : ℤ} (hm : m < 0) : hsymmInt σ R m = 0 := by
  simp [hsymmInt, not_le.mpr hm]

/-- In a natural-number degree, `TauCeti.hsymmInt` is `MvPolynomial.hsymm`. -/
theorem hsymmInt_natCast (n : ℕ) : hsymmInt σ R n = MvPolynomial.hsymm σ R n := by
  simp [hsymmInt]

/-- `h_0 = 1`. -/
theorem hsymmInt_zero : hsymmInt σ R 0 = 1 := by
  simp

/-- Changing the coefficients along a ring homomorphism preserves `TauCeti.hsymmInt`. -/
@[simp]
theorem map_hsymmInt {S : Type*} [CommSemiring S] (m : ℤ) (f : R →+* S) :
    MvPolynomial.map f (hsymmInt σ R m) = hsymmInt σ S m := by
  unfold hsymmInt
  split_ifs <;> simp [MvPolynomial.map_hsymm]

/-- Renaming the variables along a bijection preserves `TauCeti.hsymmInt`. -/
@[simp]
theorem rename_hsymmInt {τ : Type*} [Fintype τ] [DecidableEq τ] (m : ℤ) (e : σ ≃ τ) :
    MvPolynomial.rename e (hsymmInt σ R m) = hsymmInt τ R m := by
  unfold hsymmInt
  split_ifs <;> simp [MvPolynomial.rename_hsymm]

end hsymmInt

end TauCeti
end
end TAF_LiteralSource_0352

section TAF_LiteralSource_0353
/- Original module: TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Symmetric powers of the standard representation

This file specializes symmetric powers of representations to the standard representation of the
general linear group. The resulting action applies a matrix to every factor of a pure symmetric
tensor.

A diagonal matrix acts diagonally on the basis of `Sym[k]^d (Fin n → k)` given by the unordered
`d`-tuples of standard basis vectors, with eigenvalue the product of the corresponding diagonal
entries. Summing those eigenvalues, the character of the `d`th symmetric power at a diagonal
matrix is the `d`th complete homogeneous symmetric polynomial in its diagonal entries, dual to the
elementary symmetric polynomial the exterior power gives.

## Main definitions

* `TauCeti.symPowerRep` is the symmetric-power representation of `GL n k`.
* `TauCeti.symPowerFDRep` is its bundled finite-dimensional form.

## Main results

* `TauCeti.char_symPowerRep_diagonal` identifies the character on diagonal matrices with a
  complete homogeneous symmetric polynomial.

## References

* The standard-representation specialization is adapted from the formal template in
  `TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower`.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

variable (k : Type) (n d : ℕ)

section CommRing

variable [CommRing k]

/-- The `d`th symmetric power of the standard representation of `GL n k`. -/
noncomputable abbrev symPowerRep :
    Representation k (GL (Fin n) k) (Sym[k]^d (Fin n → k)) :=
  (stdRep k n).symmetricPower d

/-- The symmetric power of the standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev symPowerFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (symPowerRep k n d)

end CommRing

section Field

variable [Field k]

/-- The character of the `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerRep_diagonal (t : Fin n → kˣ) : (symPowerRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  rw [Representation.character, Representation.symmetricPower_apply,
    Module.Basis.trace_map_symmetricPower_of_apply (Pi.basisFun k (Fin n))
      (stdRep k n (diagGL t)) (fun i => (t i : k)) d (stdRep_diagGL_apply_basisFun t)]
  -- both sides sum, over the unordered `d`-tuples of indices, the product of the entries listed
  rw [eval_hsymm]

/-- The character of the bundled `d`th symmetric power on a diagonal matrix is the `d`th complete
homogeneous symmetric polynomial in its diagonal entries. -/
@[simp]
theorem char_symPowerFDRep_diagonal (t : Fin n → kˣ) : (symPowerFDRep k n d).character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : k)) (MvPolynomial.hsymm (Fin n) k d) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_symPowerRep_diagonal k n d t

end Field

end TauCeti
end
end TAF_LiteralSource_0353

