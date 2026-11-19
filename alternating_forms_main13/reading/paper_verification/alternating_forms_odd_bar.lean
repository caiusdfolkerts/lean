module

public import PaperVerification.AlternatingFormsOddStandardPieces
public import PaperVerification.AlternatingFormsBarTensor
public import Mathlib.Logic.Equiv.Option

/-!
# The actual augmentation and normalized bar complex of the odd Plücker ring

The augmentation sends every positive-degree Plücker coordinate to zero.
Its kernel is the actual augmentation ideal. The unit-plus-positive basis
is a reindexing of the previously constructed standard-product basis;
neither the multiplication nor its coefficients are replaced by a model.
The final comparison computes ordinary Mathlib Tor for this actual ring.
Off-diagonal vanishing still requires the PBW filtration argument.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open MvPolynomial CategoryTheory
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K]

def isotropicAugmentation (t n : ℕ) (forms : Fin 2 → StrictPairs n → K) :
    (MvPolynomial (PluckerIndex (t+2) n) K⧸isotropicPluckerIdeal forms) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (matrixMinorEvaluation (0 : Matrix (Fin (t+2)) (Fin n) K))
    (by
      change isotropicPluckerIdeal (t := t) forms ≤
        RingHom.ker (matrixMinorEvaluation (0 : Matrix (Fin (t+2)) (Fin n) K)).toRingHom
      apply sup_le
      · exact matrixPluckerIdeal_le_matrixMinorKernel _
      · apply Ideal.span_le.mpr
        rintro _ ⟨⟨l,J⟩,rfl⟩
        exact matrixMinorEvaluation_isotropy_eq_zero (forms l) _
          (by intro i j; simp [alternatingRowPair]) J)

@[simp] theorem isotropicAugmentation_mk (t n : ℕ)
    (forms : Fin 2 → StrictPairs n → K)
    (p : MvPolynomial (PluckerIndex (t+2) n) K) :
    isotropicAugmentation t n forms (Ideal.Quotient.mk _ p)=
      matrixMinorEvaluation (0 : Matrix (Fin (t+2)) (Fin n) K) p := rfl

@[simp] theorem isotropicAugmentation_X (t n : ℕ)
    (forms : Fin 2 → StrictPairs n → K) (I : PluckerIndex (t+2) n) :
    isotropicAugmentation t n forms (Ideal.Quotient.mk _ (X I))=0 := by
  rw [isotropicAugmentation_mk]
  simp only [matrixMinorEvaluation,aeval_X]
  change (0 : Matrix (Fin (t+2)) (Fin (t+2)) K).det = 0
  exact Matrix.det_zero

variable (k t : ℕ) (hs : t+2≤k+1)

def oddEmptyStandardIndex : OddStandardIndex k t hs :=
  ⟨0,⟨Fin.elim0,by
    refine ⟨?_,?_,?_⟩
    · intro j; exact Fin.elim0 j
    · intro j; exact Fin.elim0 j
    · intro i; exact Fin.elim0 i⟩⟩

theorem oddStandardIndex_eq_empty_of_degree_zero (C : OddStandardIndex k t hs)
    (hC : C.1=0) : C=oddEmptyStandardIndex k t hs := by
  rcases C with ⟨r,C⟩
  dsimp only at hC
  subst r
  congr 1
  apply Subtype.ext
  exact funext (fun i => Fin.elim0 i)

theorem oddStandardIndex_degree_positive (C : OddStandardIndex k t hs)
    (hC : C≠oddEmptyStandardIndex k t hs) : 0<C.1 := by
  by_contra h
  exact hC (oddStandardIndex_eq_empty_of_degree_zero k t hs C (by omega))

def OddPositiveStandardIndex (K : Type u) :=
  ULift.{u} {C : OddStandardIndex k t hs // C≠oddEmptyStandardIndex k t hs}

def oddOptionStandardEquiv :
    Option (OddPositiveStandardIndex (K := K) k t hs) ≃ OddStandardIndex k t hs := by
  classical
  exact (Equiv.optionCongr Equiv.ulift).trans
    (Equiv.optionSubtypeNe (oddEmptyStandardIndex k t hs))

def oddAugmentedBasis :
    Module.Basis (Option (OddPositiveStandardIndex (K := K) k t hs)) K
      (MvPolynomial (PluckerIndex (t+2) (2*k+1)) K⧸
        isotropicPluckerIdeal (t := t) (oddPluckerForms (K := K) k)) :=
  (oddPluckerStandardBasis k t hs).reindex (oddOptionStandardEquiv (K := K) k t hs).symm

@[simp] theorem oddAugmentedBasis_none :
    oddAugmentedBasis (K := K) k t hs none=1 := by
  rw [oddAugmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  change oddPluckerStandardBasis (K := K) k t hs (oddEmptyStandardIndex k t hs)=1
  rw [oddPluckerStandardBasis_apply]
  simp [oddStandardRepresentative,chainPluckerProduct,oddEmptyStandardIndex]
  exact Finset.prod_eq_one (fun i _ => Fin.elim0 i)

@[simp] theorem oddAugmentedBasis_some (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentedBasis (K := K) k t hs (some C)=
      oddPluckerStandardBasis k t hs C.down.val := by
  rw [oddAugmentedBasis,Module.Basis.reindex_apply,Equiv.symm_symm]
  rfl

def oddAugmentation :=
  isotropicAugmentation (K := K) t (2*k+1) (oddPluckerForms k)

theorem oddAugmentation_positive (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentation (K := K) k t (oddAugmentedBasis k t hs (some C))=0 := by
  classical
  rw [oddAugmentedBasis_some,oddPluckerStandardBasis_apply]
  change isotropicAugmentation t (2*k+1) (oddPluckerForms k)
    (Ideal.Quotient.mk _ (chainPluckerProduct _ _ C.down.val.2))=0
  simp only [chainPluckerProduct,map_prod]
  have hpos := oddStandardIndex_degree_positive k t hs C.down.val C.down.property
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0,hpos⟩ : Fin C.down.val.1))
    (isotropicAugmentation_X t (2*k+1) (oddPluckerForms k) _)

/-- This is the internal degree of the actual positive standard product. -/
def oddPositiveDegree (C : OddPositiveStandardIndex (K := K) k t hs) : ℕ :=
  C.down.val.1

theorem oddPositiveDegree_pos (C : OddPositiveStandardIndex (K := K) k t hs) :
    0<oddPositiveDegree (K := K) k t hs C :=
  oddStandardIndex_degree_positive k t hs C.down.val C.down.property

theorem oddAugmentedBasis_homogeneous (C : OddPositiveStandardIndex (K := K) k t hs) :
    oddAugmentedBasis (K := K) k t hs (some C)∈
      oddPluckerDegree k t (oddPositiveDegree (K := K) k t hs C) := by
  rw [oddAugmentedBasis_some]
  exact oddPluckerStandardBasis_mem_degree k t hs C.down.val

/-- The residue, tensor functor, and homology here are the genuine ones
for the original isotropic Plücker quotient. This comparison alone does
not assert Koszulness. -/
def oddNormalizedBarTorIso (r : ℕ) :
    BarFree.TorOverCoefficients (oddAugmentation (K := K) k t) r ≅
      (BarFree.reducedComplex (oddAugmentation (K := K) k t)
        (oddAugmentedBasis k t hs) (oddAugmentedBasis_none k t hs)
        (oddAugmentation_positive k t hs)).homology r :=
  BarFree.reducedBarTorIso (oddAugmentation k t) (oddAugmentedBasis k t hs)
    (oddAugmentedBasis_none k t hs) (oddAugmentation_positive k t hs) r

end PaperVerification.AlternatingForms

