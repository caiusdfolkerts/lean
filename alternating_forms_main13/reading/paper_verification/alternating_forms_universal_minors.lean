module

public import PaperVerification.AlternatingFormsIntervalPlucker
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Universal maximal minors and the Cramer identities

Every ordered maximal minor, including those with repeated columns, is a
literal polynomial in the strictly increasing Plücker variables. The Cramer
identities below are identities in the kernel of the generic minor map; no
Grassmannian presentation or rank assumption is supplied as a hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}

def sortedPluckerIndex (I : Fin s → Fin n) (hI : Function.Injective I) :
    PluckerIndex s n :=
  ⟨I ∘ Tuple.sort I,(Tuple.monotone_sort I).strictMono_of_injective
    (hI.comp (Tuple.sort I).injective)⟩

/-- An arbitrary ordered maximal minor in the literal Plücker polynomial ring. -/
def orderedPluckerCoordinate (I : Fin s → Fin n) : MvPolynomial (PluckerIndex s n) K :=
  if hI : Function.Injective I then
    (((Equiv.Perm.sign (Tuple.sort I).symm : ℤ) : K) • X (sortedPluckerIndex I hI))
  else 0

theorem genericPluckerMap_orderedCoordinate (I : Fin s → Fin n) :
    genericPluckerMap (K := K) (orderedPluckerCoordinate I) =
      Matrix.det (Matrix.of fun i j : Fin s => (X (i,I j) : MvPolynomial (Fin s × Fin n) K)) := by
  classical
  unfold orderedPluckerCoordinate
  split_ifs with hI
  · rw [map_smul]
    simp only [genericPluckerMap,aeval_X,genericPluckerMinor,Algebra.smul_def,map_intCast]
    have he := Matrix.det_permute' (Tuple.sort I).symm
      (Matrix.of fun i j : Fin s => (X (i,I (Tuple.sort I j)) : MvPolynomial (Fin s × Fin n) K))
    have hm : (Matrix.of fun i j : Fin s =>
        (X (i,I (Tuple.sort I j)) : MvPolynomial (Fin s × Fin n) K)).submatrix
          id (Tuple.sort I).symm =
        (Matrix.of fun i j : Fin s => (X (i,I j) : MvPolynomial (Fin s × Fin n) K)) := by
      apply Matrix.ext
      intro i j
      simp only [Matrix.submatrix_apply,Matrix.of_apply,id_eq,Equiv.apply_symm_apply]
    rw [hm] at he
    simpa only [sortedPluckerIndex,Function.comp_apply] using he.symm
  · rw [map_zero]
    obtain ⟨i,j,hij,hne⟩ : ∃ i j, I i=I j ∧ i≠j := by
      simpa only [Function.Injective,not_forall,not_imp,exists_prop] using hI
    exact (Matrix.det_zero_of_column_eq hne (fun a => by
      simp only [Matrix.of_apply]
      rw [hij])).symm

/-- Evaluation of generic matrix entries at an arbitrary matrix. -/
def matrixEntryEvaluation {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) : MvPolynomial (Fin s × Fin n) K →ₐ[K] R :=
  aeval fun a => A a.1 a.2

def matrixMinorEvaluation {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) : MvPolynomial (PluckerIndex s n) K →ₐ[K] R :=
  aeval fun I => Matrix.det (Matrix.of fun i j : Fin s => A i (I.val j))

theorem matrixEntryEvaluation_minor {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (I : Fin s → Fin n) :
    matrixEntryEvaluation (K := K) A
      (Matrix.det (Matrix.of fun i j : Fin s => (X (i,I j) : MvPolynomial (Fin s × Fin n) K))) =
      Matrix.det (Matrix.of fun i j : Fin s => A i (I j)) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [matrixEntryEvaluation,AlgHom.mapMatrix_apply,Matrix.map_apply,Matrix.of_apply]

theorem matrixMinorEvaluation_eq_comp {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) :
    matrixMinorEvaluation (K := K) A =
      (matrixEntryEvaluation A).comp genericPluckerMap := by
  apply MvPolynomial.algHom_ext
  intro I
  simpa only [matrixMinorEvaluation,genericPluckerMap,aeval_X,AlgHom.comp_apply,
    genericPluckerMinor] using (matrixEntryEvaluation_minor A I.val).symm

theorem matrixMinorEvaluation_orderedCoordinate {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (I : Fin s → Fin n) :
    matrixMinorEvaluation (K := K) A (orderedPluckerCoordinate I) =
      Matrix.det (Matrix.of fun i j : Fin s => A i (I j)) := by
  rw [matrixMinorEvaluation_eq_comp,AlgHom.comp_apply,genericPluckerMap_orderedCoordinate,
    matrixEntryEvaluation_minor]

theorem matrixPluckerIdeal_le_matrixMinorKernel {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) :
    matrixPluckerIdeal (K := K) ≤ RingHom.ker (matrixMinorEvaluation A).toRingHom := by
  intro p hp
  change matrixMinorEvaluation A p=0
  change genericPluckerMap p=0 at hp
  rw [matrixMinorEvaluation_eq_comp,AlgHom.comp_apply,hp,map_zero]

def cramerPluckerCoordinate (p : PluckerIndex s n) (i : Fin s) (j : Fin n) :
    MvPolynomial (PluckerIndex s n) K :=
  orderedPluckerCoordinate (Function.update p.val i j)

theorem matrixMinorEvaluation_cramer {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (p : PluckerIndex s n) (i : Fin s) (j : Fin n) :
    matrixMinorEvaluation (K := K) A (cramerPluckerCoordinate p i j) =
      Matrix.cramer (Matrix.of fun a b => A a (p.val b)) (fun a => A a j) i := by
  rw [cramerPluckerCoordinate,matrixMinorEvaluation_orderedCoordinate,Matrix.cramer_apply]
  congr 1
  ext a b
  by_cases h : b=i
  · subst b
    simp [Matrix.of_apply]
  · simp [Function.update_of_ne h,Matrix.updateCol_ne h,Matrix.of_apply]

theorem cramerPlucker_pivot_relation (p : PluckerIndex s n) (i j : Fin s) :
    cramerPluckerCoordinate (K := K) p i (p.val j) -
      (if i=j then X p else 0) ∈ matrixPluckerIdeal := by
  classical
  change genericPluckerMap _=0
  have he := matrixMinorEvaluation_cramer
    (K := K) (Matrix.of fun a b => (X (a,b) : MvPolynomial (Fin s × Fin n) K)) p i (p.val j)
  have hmap : matrixMinorEvaluation
      (K := K) (Matrix.of fun a b => (X (a,b) : MvPolynomial (Fin s × Fin n) K)) =
      genericPluckerMap := by
    apply MvPolynomial.algHom_ext
    intro I
    simp [matrixMinorEvaluation,genericPluckerMap,genericPluckerMinor,Matrix.of_apply]
  rw [hmap] at he
  simp only [Matrix.of_apply] at he
  rw [map_sub,he]
  have hc := Matrix.cramer_row_self
    (Matrix.of fun a b : Fin s => (X (a,p.val b) : MvPolynomial (Fin s × Fin n) K))
    (fun a : Fin s => (X (a,p.val j) : MvPolynomial (Fin s × Fin n) K)) j
    (fun a => rfl)
  rw [hc]
  by_cases h : i=j
  · subst i
    simp [genericPluckerMap,genericPluckerMinor]
  · simp [h,Ne.symm h,Pi.single_apply]

/-- The universal Cramer identity among actual generic maximal minors. -/
theorem cramerPlucker_minor_relation (p I : PluckerIndex s n) :
    Matrix.det (Matrix.of fun i j : Fin s => cramerPluckerCoordinate (K := K) p i (I.val j)) -
      (X p) ^ (s-1) * X I ∈ matrixPluckerIdeal := by
  classical
  change genericPluckerMap _=0
  rw [map_sub,map_mul,map_pow,AlgHom.map_det]
  let A : Matrix (Fin s) (Fin n) (MvPolynomial (Fin s × Fin n) K) := Matrix.of fun a b => X (a,b)
  let B : Matrix (Fin s) (Fin s) (MvPolynomial (Fin s × Fin n) K) :=
    Matrix.of fun a b => A a (p.val b)
  have hmap : matrixMinorEvaluation (K := K) A = genericPluckerMap := by
    apply MvPolynomial.algHom_ext
    intro J
    simp [matrixMinorEvaluation,genericPluckerMap,genericPluckerMinor,A,Matrix.of_apply]
  have hm : genericPluckerMap.mapMatrix
      (Matrix.of fun i j : Fin s => cramerPluckerCoordinate (K := K) p i (I.val j)) =
      B.adjugate * (Matrix.of fun i j : Fin s => A i (I.val j)) := by
    apply Matrix.ext
    intro i j
    change genericPluckerMap (K := K) (cramerPluckerCoordinate (K := K) p i (I.val j)) = _
    rw [←hmap,matrixMinorEvaluation_cramer (K := K),Matrix.cramer_eq_adjugate_mulVec]
    rfl
  rw [hm,Matrix.det_mul,Matrix.det_adjugate,Fintype.card_fin]
  simp [genericPluckerMap,genericPluckerMinor,A,B,Matrix.of_apply]

end PaperVerification.AlternatingForms
