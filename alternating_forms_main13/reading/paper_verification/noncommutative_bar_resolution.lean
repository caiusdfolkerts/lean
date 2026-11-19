module

public import PaperVerification.NoncommutativeBarLength
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import PaperVerification.AugmentationCoinvariants
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# An actual projective normalized bar resolution

The terms are the free length pieces and the differential is the literal
normalized bar differential. Exactness is proved using the explicit contraction.
The augmentation module is the actual quotient by the augmentation ideal,
proved algebra-isomorphic to the coefficient ring.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.NoncommutativeBar

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def residueIdeal : Ideal A := RingHom.ker ε.toRingHom

instance residueIdeal_twoSided : (residueIdeal ε).IsTwoSided := by
  dsimp only [residueIdeal]
  infer_instance

abbrev Residue := A ⧸ residueIdeal ε

theorem augmentation_surjective : Function.Surjective ε := by
  intro c
  exact ⟨algebraMap K A c, ε.commutes c⟩

def residueEquivCoefficients : Residue ε ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (augmentation_surjective ε)

def degreeDifferential (r : ℕ) :
    lengthPiece I A (r+1) →ₗ[A] lengthPiece I A r :=
  LinearMap.codRestrict _
    ((differential B).comp (lengthPiece I A (r+1)).subtype)
    (fun z ↦ differential_mem_lengthPiece B z.val z.property)

@[simp] theorem degreeDifferential_coe (r : ℕ) (z : lengthPiece I A (r+1)) :
    (degreeDifferential B r z : Words I A)=differential B z.val := rfl

include hunit hε in
theorem degreeDifferential_comp (r : ℕ) :
    (degreeDifferential B r).comp (degreeDifferential B (r+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact differential_squared ε B hunit hε z.val

def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of A (lengthPiece I A r))
    (fun r ↦ ModuleCat.ofHom (degreeDifferential B r))
    (fun r ↦ ModuleCat.hom_ext (degreeDifferential_comp ε B hunit hε r))

include hunit hε in
@[simp] theorem complex_X (r : ℕ) :
    (complex ε B hunit hε).X r=ModuleCat.of A (lengthPiece I A r) := rfl

include hunit hε in
@[simp] theorem complex_d (r : ℕ) :
    (complex ε B hunit hε).d (r+1) r=ModuleCat.ofHom (degreeDifferential B r) := by
  simp [complex]

/-- The degree-zero map is evaluation of the free coefficient modulo the
actual augmentation ideal. -/
def augmentationMap : lengthPiece I A 0 →ₗ[A] Residue ε :=
  (residueIdeal ε).mkQ.comp
    ((Finsupp.lapply []).comp (lengthPiece I A 0).subtype)

theorem length_zero_eq_single (z : Words I A) (hz : z∈lengthPiece I A 0) :
    z=Finsupp.single [] (z []) := by
  classical
  ext L
  by_cases hL : L=[]
  · subst L
    simp
  · have hlen : L.length≠0 := fun h => hL (List.length_eq_zero_iff.mp h)
    rw [(mem_lengthPiece_iff z 0).mp hz L hlen,Finsupp.single_eq_of_ne hL]

theorem differential_length_zero (z : Words I A) (hz : z∈lengthPiece I A 0) :
    differential B z=0 := by
  rw [length_zero_eq_single z hz]
  simp only [differential,LinearMap.sub_apply,front_single,frontBasis,internal_single,
    PaperVerification.ReducedBarBasis.differentialBasis,map_zero,smul_zero,sub_zero]

theorem augmentationMap_surjective : Function.Surjective (augmentationMap (I := I) ε) := by
  intro q
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨Finsupp.single [] a,single_mem_lengthPiece _ _ rfl⟩,by
    simp [augmentationMap]⟩

include hunit hε in
/-- The augmentation kills the literal differential on every length-one word. -/
theorem augmentation_differential_zero (z : Words I A)
    (hz : z∈lengthPiece I A 1) :
    (residueIdeal ε).mkQ ((differential B z) [])=0 := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    obtain ⟨i,rfl⟩ := List.length_eq_one_iff.mp hL
    simp only [differential,LinearMap.sub_apply,front_single,frontBasis,internal_single,
      PaperVerification.ReducedBarBasis.differentialBasis,
      PaperVerification.ReducedBarBasis.merge_single,
      PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,sub_zero,one_smul,
      Finsupp.single_eq_same]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hε i
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw ihz ihw => simp only [map_add,Finsupp.add_apply,ihz,ihw,add_zero]
  | smul a z hz ih =>
    simp only [map_smul,Finsupp.smul_apply,ih,smul_zero]

include hunit hε in
theorem augmentationMap_differential :
    (augmentationMap (I := I) ε).comp (degreeDifferential B 0)=0 := by
  apply LinearMap.ext
  intro z
  exact augmentation_differential_zero ε B hunit hε z.val z.property

include hunit hε in
theorem degreeDifferential_exact (r : ℕ) :
    Function.Exact (degreeDifferential B (r+1)) (degreeDifferential B r) := by
  intro z
  constructor
  · intro hz
    have hd : differential B z.val=0 := congrArg Subtype.val hz
    obtain ⟨y,hy,hd⟩ := positive_cycle_is_boundary ε B hunit hε z.val z.property hd
    exact ⟨⟨y,hy⟩,Subtype.ext hd⟩
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact differential_squared ε B hunit hε y.val

include hunit hε in
theorem augmentationMap_exact :
    Function.Exact (degreeDifferential B 0) (augmentationMap (I := I) ε) := by
  intro z
  constructor
  · intro hz
    have he : ε (z.val [])=0 := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hp : augmentationProjection ε z.val=0 := by
      simp only [augmentationProjection,LinearMap.comp_apply,LinearMap.smulRight_apply,
        Finsupp.lapply_apply,AlgHom.toLinearMap_apply,he,zero_smul]
    refine ⟨⟨homotopy B z.val,homotopy_mem_lengthPiece B z.val z.property⟩,?_⟩
    apply Subtype.ext
    change differential B (homotopy B z.val)=z.val
    have h := contracting_identity ε B hunit hε z.val
    simpa only [differential_length_zero B z.val z.property,map_zero,hp,add_zero] using h
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (augmentationMap_differential ε B hunit hε) y

include hunit hε in
theorem complex_exactAt_succ (r : ℕ) :
    (complex ε B hunit hε).ExactAt (r+1) := by
  rw [HomologicalComplex.exactAt_iff' _ ((r+1)+1) (r+1) r (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',
    complex,ChainComplex.of_d,ModuleCat.hom_ofHom]
  exact (LinearMap.exact_iff.mp (degreeDifferential_exact ε B hunit hε r)).symm

def augmentation :
    (complex ε B hunit hε).X 0 ⟶ ModuleCat.of A (Residue ε) :=
  ModuleCat.ofHom (augmentationMap ε)

include hunit hε in
theorem complex_d_augmentation :
    (complex ε B hunit hε).d 1 0 ≫ augmentation ε B hunit hε=0 := by
  apply ModuleCat.hom_ext
  exact augmentationMap_differential ε B hunit hε

include hunit hε in
theorem augmentation_exact :
    (ShortComplex.mk _ _ (complex_d_augmentation ε B hunit hε)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (degreeDifferential B 0)=LinearMap.ker (augmentationMap ε)
  exact (LinearMap.exact_iff.mp (augmentationMap_exact ε B hunit hε)).symm

instance augmentation_epi : Epi (augmentation ε B hunit hε) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentationMap_surjective ε)

/-- The actual normalized free bar resolution, with no exactness premise. -/
def resolution : ProjectiveResolution (ModuleCat.of A (Residue ε)) where
  complex := complex ε B hunit hε
  projective r := by
    change Projective (ModuleCat.of A (lengthPiece I A r))
    infer_instance
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨augmentation ε B hunit hε,complex_d_augmentation ε B hunit hε⟩
  quasiIso := ⟨fun r ↦ by
    cases r with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (complex_d_augmentation ε B hunit hε)).Exact ∧
          Epi (augmentation ε B hunit hε)
        exact ⟨augmentation_exact ε B hunit hε,inferInstance⟩
      all_goals rfl
    | succ r =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ ε B hunit hε r
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- The actual left-derived augmentation-coinvariants functor is computed
by the genuine projective bar resolution.  The algebra need not commute. -/
def derivedCoinvariantsIso (r : ℕ) :
    (AugmentationCoinvariants.derived ε r).obj (ModuleCat.of A (Residue ε)) ≅
      (((AugmentationCoinvariants.functor ε).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (resolution ε B hunit hε).complex).homology r :=
  AugmentationCoinvariants.computedByResolution ε (resolution ε B hunit hε) r

end PaperVerification.NoncommutativeBar
