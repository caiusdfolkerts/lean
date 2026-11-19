module

public import TauCeti.RingTheory.KoszulComplex.Regular
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Fin.Tuple.Take
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

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
