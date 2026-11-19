module

public import PaperVerification.AlternatingFormsChernRelationsBasic
public import PaperVerification.HomogeneousNullstellensatz
public import PaperVerification.AlternatingFormsFieldDescent
import Lean.Elab.Tactic.Omega

/-!
# The Chern relations form a regular sequence

This file applies the general homogeneous-system-of-parameters theorem to the
actual relations of Section 4.3.  It also establishes compatibility of the
relations with change of coefficient field.  The cohomology and Chow comparison
is a further geometric theorem, not part of the definition of this sequence.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open Finset RingTheory.Sequence

variable {K L σ : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
  [Fintype σ] [DecidableEq σ]

/-- Section 4.3's regularity statement over an algebraically closed field of
characteristic zero, for every number of variables and every positive window. -/
theorem chernRelationSequence_isWeaklyRegular [IsAlgClosed K] (s w : ℕ) (hw : 0 < w) :
    IsWeaklyRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) := by
  apply HomogeneousLocalization.homogeneous_family_regular_of_common_zero
    chernCoefficientWeight chernCoefficientWeight_ne_zero
    (fun i : Fin s => chernCoefficientRelation s (w + i.val))
  · intro i
    exact ⟨w + i.val, chernCoefficientRelation_isWeightedHomogeneous s (w + i.val)⟩
  · intro i
    exact chernCoefficientRelation_constantCoeff s (w + i.val) (by omega)
  · intro x hx
    apply chernCoefficientRelation_common_zero hw x
    intro m hwm hms
    let i : Fin s := ⟨m - w, by omega⟩
    have hi : w + i.val = m := by dsimp [i]; omega
    simpa only [hi, MvPolynomial.aeval_eq_eval] using hx i

/-- The sequence generates a proper ideal, since every entry vanishes at the
origin.  This is the nonzero-quotient condition in Mathlib's `IsRegular`. -/
theorem chernRelationSequence_top_ne_smul (s w : ℕ) (hw : 0 < w) :
    (⊤ : Submodule (MvPolynomial (Fin s) K) (MvPolynomial (Fin s) K)) ≠
      Ideal.ofList (chernRelationSequence K s w) • ⊤ := by
  intro htop
  have hmem : (1 : MvPolynomial (Fin s) K) ∈
      Ideal.ofList (chernRelationSequence K s w) := by
    have h : (1 : MvPolynomial (Fin s) K) ∈
        Ideal.ofList (chernRelationSequence K s w) •
          (⊤ : Submodule (MvPolynomial (Fin s) K) (MvPolynomial (Fin s) K)) := by
      rw [← htop]
      trivial
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h
  have hle : Ideal.ofList (chernRelationSequence K s w) ≤
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin s) K →+* K) := by
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact chernCoefficientRelation_constantCoeff s (w + i.val) (by omega)
  have hzero := hle hmem
  simpa using hzero

theorem chernRelationSequence_isRegular [IsAlgClosed K] (s w : ℕ) (hw : 0 < w) :
    IsRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) :=
  ⟨chernRelationSequence_isWeaklyRegular s w hw,
    chernRelationSequence_top_ne_smul s w hw⟩

/-- The regular-sequence assertion over the original characteristic-zero field.
The common-zero argument is performed over its actual algebraic closure and
proved by the extension-valued Nullstellensatz; algebraic closedness is not an added hypothesis. -/
theorem chernRelationSequence_isWeaklyRegular_over_field (s w : ℕ) (hw : 0 < w) :
    IsWeaklyRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) := by
  apply homogeneous_parameters_regular_of_common_zero_extension
    (L := AlgebraicClosure K) chernCoefficientWeight chernCoefficientWeight_ne_zero
    (chernRelationSequence K s w)
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact ⟨w + i.val, chernCoefficientRelation_isWeightedHomogeneous s (w + i.val)⟩
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact chernCoefficientRelation_constantCoeff s (w + i.val) (by omega)
  · intro x hx
    apply chernCoefficientRelation_common_zero hw x
    intro m hwm hms
    let i : Fin s := ⟨m - w, by omega⟩
    have hi : w + i.val = m := by dsimp [i]; omega
    have h := hx (chernCoefficientRelation s (w + i.val))
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [← MvPolynomial.eval_map, map_chernCoefficientRelation, hi] at h
    exact h
  · simp [chernRelationSequence]

/-- The homogeneous regular sequence of Section 4.3, including its rational
coefficient field and its entire parameter range. -/
theorem chernRelationSequence_isRegular_over_field (s w : ℕ) (hw : 0 < w) :
    IsRegular (MvPolynomial (Fin s) K) (chernRelationSequence K s w) :=
  ⟨chernRelationSequence_isWeaklyRegular_over_field s w hw,
    chernRelationSequence_top_ne_smul s w hw⟩

end PaperVerification.AlternatingForms
