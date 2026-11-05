module

public import PaperVerification.AlternatingFormsChernHomogeneity
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The finite window of Chern relations

The literal ordered list of the Section 4 relations commutes with extension
of the coefficient field. Neither its definition nor these identities assumes
regularity, a quotient dimension formula, or a geometric comparison.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms

variable {K L σ : Type*} [Field K] [CharZero K] [Field L] [CharZero L]
  [Fintype σ] [DecidableEq σ]

theorem map_squareSubstitution (φ : K →+* L) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (squareSubstitution p) =
      squareSubstitution (MvPolynomial.map φ p) := by
  change MvPolynomial.map φ
    (MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i ^ 2) p) = _
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext i
  simp

theorem map_chernRootRelationPolynomial (φ : K →+* L) (n : ℕ) :
    MvPolynomial.map φ (chernRootRelationPolynomial (K := K) (σ := σ) n) =
      chernRootRelationPolynomial (K := L) (σ := σ) n := by
  unfold chernRootRelationPolynomial
  split_ifs
  · rw [map_squareSubstitution, MvPolynomial.map_hsymm]
  · simp only [map_sum, map_mul, MvPolynomial.map_X, map_squareSubstitution,
      ← MvPolynomial.pderiv_map, MvPolynomial.map_hsymm]

theorem map_elementarySubstitution (φ : K →+* L) {s : ℕ}
    (p : MvPolynomial (Fin s) K) :
    MvPolynomial.map φ (elementarySubstitution s p) =
      elementarySubstitution s (MvPolynomial.map φ p) := by
  change MvPolynomial.map φ
    (MvPolynomial.eval₂ MvPolynomial.C
      (fun i : Fin s => MvPolynomial.esymm (Fin s) K (i.val + 1)) p) = _
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext i
  exact MvPolynomial.map_esymm (σ := Fin s) (R := K) (i.val+1) φ

/-- The unique elementary-coordinate relations commute with coefficient maps. -/
theorem map_chernCoefficientRelation (φ : K →+* L) (s n : ℕ) :
    MvPolynomial.map φ (chernCoefficientRelation (K := K) s n) =
      chernCoefficientRelation (K := L) s n := by
  apply elementarySubstitution_injective s
  rw [← map_elementarySubstitution, elementarySubstitution,
    chernCoefficientRelation_substitution, map_chernRootRelationPolynomial,
    elementarySubstitution, chernCoefficientRelation_substitution]

/-- The ordered length-`s` window of the paper's actual coefficient relations. -/
noncomputable def chernRelationSequence (K : Type*) [Field K] [CharZero K]
    (s w : ℕ) : List (MvPolynomial (Fin s) K) :=
  List.ofFn fun i : Fin s => chernCoefficientRelation s (w + i.val)

theorem map_chernRelationSequence (φ : K →+* L) (s w : ℕ) :
    (chernRelationSequence K s w).map (MvPolynomial.map φ) =
      chernRelationSequence L s w := by
  simp only [chernRelationSequence, List.map_ofFn, Function.comp_def,
    map_chernCoefficientRelation]

end PaperVerification.AlternatingForms
