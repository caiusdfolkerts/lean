module

public import PaperVerification.AlternatingFormsTableauMinors
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Algebra.Rat

/-!
# Standard products span the algebra of maximal minors in characteristic zero

Each occurrence of a matrix-column value first receives its own label. Sorting
the labels makes their value map monotone; ordinary standard tableaux then
specialize to semistandard tableaux. A repeated value in one column gives a
zero determinant, while every other standard tableau gives a genuine
multichain of strictly increasing maximal-minor indices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial TauCeti

namespace PaperVerification.AlternatingForms

variable {s n r : ℕ}

def StandardMinorChain (s n r : ℕ) :=
  {I : Fin r → Fin s → Fin n // (∀ j, StrictMono (I j)) ∧ Monotone I}

instance standardMinorChain_fintype (s n r : ℕ) : Fintype (StandardMinorChain s n r) := by
  classical
  unfold StandardMinorChain
  infer_instance

def genericMinorProduct {K : Type*} [CommRing K] (I : Fin r → Fin s → Fin n) :
    MvPolynomial (Fin s × Fin n) K :=
  ∏ j, Matrix.det (Matrix.of (fun i k : Fin s => X (i,I j k)))

def genericStandardMinorProduct {K : Type*} [CommRing K]
    (C : StandardMinorChain s n r) : MvPolynomial (Fin s × Fin n) K :=
  genericMinorProduct C.val

theorem rectangleLabels_trans (t : YoungTableau (minorRectangle s r))
    (σ : Equiv.Perm (Fin (minorRectangle s r).card)) (p : Fin s × Fin r) :
    rectangleLabels (t.trans σ) p = σ (rectangleLabels t p) := rfl

theorem exists_sorted_rectangle_labels (I : Fin r → Fin s → Fin n) :
    ∃ (v : Fin (minorRectangle s r).card → Fin n)
      (t : YoungTableau (minorRectangle s r)),
      Monotone v ∧ ∀ i j, v (rectangleLabels t (i,j)) = I j i := by
  obtain ⟨t₀⟩ := YoungTableau.nonempty (minorRectangle s r)
  let u : Fin (minorRectangle s r).card → Fin n := fun k =>
    I (rectangleColumn t₀ k) (rectangleRow t₀ k)
  refine ⟨u ∘ Tuple.sort u,t₀.trans (Tuple.sort u).symm,Tuple.monotone_sort u,?_⟩
  intro i j
  simp only [Function.comp_apply,rectangleLabels_trans,Equiv.apply_symm_apply,u,
    rectangleColumn_labels,rectangleRow_labels]

theorem rectangularMinorProduct_eq_generic
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularMinorProduct v t =
      genericMinorProduct (K := ℚ) (fun j i => v (rectangleLabels t (i,j))) := rfl

theorem standard_rectangle_values_row_monotone
    (v : Fin (minorRectangle s r).card → Fin n) (hv : Monotone v)
    (T : StandardYoungTableau (minorRectangle s r)) :
    Monotone (fun j : Fin r => fun i : Fin s => v (rectangleLabels T.toTableau (i,j))) := by
  intro j k hjk i
  rcases eq_or_lt_of_le hjk with rfl | hjk
  · exact le_rfl
  · apply hv
    exact (T.row_strict hjk (mem_minorRectangle.mpr ⟨i.isLt,k.isLt⟩)).le

theorem standard_rectangle_values_column_monotone
    (v : Fin (minorRectangle s r).card → Fin n) (hv : Monotone v)
    (T : StandardYoungTableau (minorRectangle s r)) (j : Fin r) :
    Monotone (fun i : Fin s => v (rectangleLabels T.toTableau (i,j))) := by
  intro i k hik
  rcases eq_or_lt_of_le hik with rfl | hik
  · exact le_rfl
  · apply hv
    exact (T.col_strict hik (mem_minorRectangle.mpr ⟨k.isLt,j.isLt⟩)).le

theorem genericMinorProduct_zero_of_repeated_column {K : Type*} [CommRing K]
    (I : Fin r → Fin s → Fin n) (j : Fin r) (h : ¬Function.Injective (I j)) :
    genericMinorProduct (K := K) I = 0 := by
  classical
  obtain ⟨i,k,hval,hne⟩ : ∃ i k, I j i = I j k ∧ i ≠ k := by
    by_contra hn
    apply h
    intro i k hik
    by_contra hne
    exact hn ⟨i,k,hik,hne⟩
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact Matrix.det_zero_of_column_eq hne (fun a => by simp only [Matrix.of_apply,hval])

theorem standard_rectangle_product_mem_span
    (v : Fin (minorRectangle s r).card → Fin n) (hv : Monotone v)
    (T : StandardYoungTableau (minorRectangle s r)) :
    rectangularMinorProduct v T.toTableau ∈ Submodule.span ℚ
      (Set.range (genericStandardMinorProduct (K := ℚ) (s := s) (n := n) (r := r))) := by
  classical
  let I : Fin r → Fin s → Fin n := fun j i => v (rectangleLabels T.toTableau (i,j))
  change genericMinorProduct I ∈ _
  by_cases hI : ∀ j, Function.Injective (I j)
  · exact Submodule.subset_span ⟨⟨I,fun j =>
      (standard_rectangle_values_column_monotone v hv T j).strictMono_of_injective (hI j),
      standard_rectangle_values_row_monotone v hv T⟩,rfl⟩
  · obtain ⟨j,hj⟩ := not_forall.mp hI
    rw [genericMinorProduct_zero_of_repeated_column I j hj]
    exact (Submodule.span ℚ _).zero_mem

/-- Full maximal-minor straightening over the rational numbers, with every
number of rows, ambient columns, and minor factors retained. -/
theorem genericMinorProduct_mem_span_standard_rat (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := ℚ) I ∈ Submodule.span ℚ
      (Set.range (genericStandardMinorProduct (K := ℚ) (s := s) (n := n) (r := r))) := by
  obtain ⟨v,t,hv,hvt⟩ := exists_sorted_rectangle_labels I
  have he : genericMinorProduct (K := ℚ) I = rectangularMinorProduct v t := by
    rw [rectangularMinorProduct_eq_generic]
    congr 1
    funext j i
    exact (hvt i j).symm
  rw [he]
  apply Submodule.span_le.mpr (fun p hp => ?_)
    (rectangularMinorProduct_mem_span_standard v t)
  obtain ⟨T,rfl⟩ := hp
  exact standard_rectangle_product_mem_span v hv T

section CoefficientExtension

variable {K : Type*} [Field K] [CharZero K]

def rationalMatrixCoefficientMap :
    MvPolynomial (Fin s × Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin s × Fin n) K :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℚ K)

theorem rationalMatrixCoefficientMap_product (I : Fin r → Fin s → Fin n) :
    rationalMatrixCoefficientMap (K := K) (genericMinorProduct (K := ℚ) I) =
      genericMinorProduct (K := K) I := by
  simp only [genericMinorProduct,map_prod,AlgHom.map_det]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  apply Matrix.ext
  intro i k
  simp [rationalMatrixCoefficientMap]

/-- The rational straightening identities hold over every characteristic-zero
field by actual coefficient extension. -/
theorem genericMinorProduct_mem_span_standard (I : Fin r → Fin s → Fin n) :
    genericMinorProduct (K := K) I ∈ Submodule.span K
      (Set.range (genericStandardMinorProduct (K := K) (s := s) (n := n) (r := r))) := by
  rw [← rationalMatrixCoefficientMap_product]
  have h := genericMinorProduct_mem_span_standard_rat I
  refine Submodule.span_induction
    (p := fun x _ => rationalMatrixCoefficientMap (K := K) x ∈ Submodule.span K
      (Set.range (genericStandardMinorProduct (K := K) (s := s) (n := n) (r := r))))
    ?_ ?_ ?_ ?_ h
  · intro p hp
    obtain ⟨C,rfl⟩ := hp
    change rationalMatrixCoefficientMap (genericMinorProduct C.val) ∈ _
    rw [rationalMatrixCoefficientMap_product]
    exact Submodule.subset_span ⟨C,rfl⟩
  · simpa only [map_zero] using (Submodule.span K _).zero_mem
  · intro x y hx hy hmx hmy
    simpa only [map_add] using (Submodule.span K _).add_mem hmx hmy
  · intro a x hx hmx
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ a hmx

end CoefficientExtension

end PaperVerification.AlternatingForms
