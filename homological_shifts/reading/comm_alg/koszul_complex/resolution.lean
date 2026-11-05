import CommAlg.KoszulComplex.Complex
import CommAlg.KoszulComplex.Variables
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor

/-! # Genuine projective resolutions and derived Tor from Koszul complexes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CommAlg.Koszul

universe u
variable {R : Type u} [CommRing R]

/-- An exact positive-degree complex of projectives resolves its zeroth cokernel. -/
def resolutionOpcycles (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hproj : ∀ n, Projective (K.X n)) (hexact : ∀ n, K.ExactAt (n + 1)) :
    ProjectiveResolution (K.opcycles 0) where
  complex := K
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv K _).symm ⟨K.pOpcycles 0, K.d_pOpcycles 1 0⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, inferInstance⟩
        exact ShortComplex.exact_of_g_is_cokernel _ (K.opcyclesIsCokernel 1 0 (by simp))
      · exact K.shape 0 0 (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact hexact n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- Change the resolved object along an actual isomorphism. -/
def transportResolution {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (e : X ≅ Y) : ProjectiveResolution Y where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ _).map e.hom

/-- The Koszul complex of a regular sequence is a projective resolution of its quotient ring. -/
def regularSequenceResolution (l : List R) (hl : RingTheory.Sequence.IsRegular R l) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList l)) :=
  transportResolution
    (resolutionOpcycles (koszulComplex.ofList l)
      (fun n => by
        change Projective (ModuleCat.of R (⋀[R]^n (Fin l.length → R)))
        infer_instance)
      (fun n => koszulComplex.exactAt_of_isRegular l hl (n + 1) (by omega)))
    ((koszulComplex.ofList l).isoHomologyι₀.symm ≪≫
      (koszulComplex.zeroHomologyOfListLinearEquiv l).toModuleIso)

@[simp] theorem regularSequenceResolution_complex (l : List R)
    (hl : RingTheory.Sequence.IsRegular R l) :
    (regularSequenceResolution l hl).complex = koszulComplex.ofList l := rfl

/-- Tensor a Koszul complex with a genuine module. -/
def coefficientComplex (l : List R) (M : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj (koszulComplex.ofList l)

/-- The first-factor derived tensor functor (Mathlib's `Tor'`) is computed by this Koszul complex.
No balance or symmetry theorem is assumed: the quotient is resolved in the first factor. -/
def torIsoKoszulHomology (l : List R) (hl : RingTheory.Sequence.IsRegular R l)
    (M : ModuleCat.{u} R) (i : ℕ) :
    ((CategoryTheory.Tor' (ModuleCat R) i).obj
      (ModuleCat.of R (R ⧸ Ideal.ofList l))).obj M ≅
      (coefficientComplex l M).homology i :=
  (regularSequenceResolution l hl).isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat R)).obj M) i

end CommAlg.Koszul
