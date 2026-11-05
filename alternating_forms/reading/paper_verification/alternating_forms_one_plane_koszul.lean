module

public import PaperVerification.AlternatingFormsOnePlane
public import PaperVerification.AlternatingFormsPolynomialKoszul
public import Mathlib.RingTheory.Regular.RegularSequence

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
