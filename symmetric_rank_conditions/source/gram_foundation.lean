module
public import gram_assignment
public import symmetric_local
public import ideal_real_weight

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


@[expose] public section

/- Generated from the separately readable proof sources listed in
   audit/GramFoundation_sources.json. All mathematical commands are copied verbatim.
   Generation alone is not evidence of successful kernel verification. -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "GramFoundation IMPORTS_LOADED\n"
  logInfo "GramFoundation IMPORTS_LOADED"

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "GramFoundation BEGIN GramMinors\n"
  logInfo "GramFoundation BEGIN GramMinors"

/- Begin GramMinors.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Leading terms of symmetric minors in generic Gram coordinates

The map sends the symmetric matrix to `Z * Zᵀ`, with all entries of `Z`
independent.  Multilinearity expands a minor over functions selecting columns.
Noninjective selections vanish because they repeat rows of a determinant.
The unique lexicographic maximum is the increasing selection of the first
columns.  Its coefficient is one over every commutative coefficient ring.
-/

noncomputable section
namespace FourPapers.Symmetric.Gram
open Finset Finsupp MvPolynomial
open scoped MonomialOrder
universe u

def generic (n : ℕ) (R : Type u) [CommRing R] :
    Matrix (Fin n) (Fin n) (Polynomial n R) := fun i j => X (toLex (j, i))

def matrix (n : ℕ) (R : Type u) [CommRing R] :
    Matrix (Fin n) (Fin n) (Polynomial n R) := generic n R * (generic n R).transpose

theorem matrix_transpose (n : ℕ) (R : Type u) [CommRing R] :
    (matrix n R).transpose = matrix n R := by
  simp [matrix, Matrix.transpose_mul]

def hom (n : ℕ) (R : Type u) [CommRing R] :
    CoordinateRing n R →ₐ[R] Polynomial n R :=
  aeval (fun e : Entry n => matrix n R e.val.1 e.val.2)

theorem hom_X_fold (n : ℕ) (R : Type u) [CommRing R] (i j : Fin n) :
    hom n R (X (fold i j)) = matrix n R i j := by
  simp only [hom, aeval_X]
  by_cases hij : i ≤ j
  · simp only [fold, max_eq_right hij, min_eq_left hij]
    exact congrFun (congrFun (matrix_transpose n R) i) j
  · simp only [fold, max_eq_left (le_of_not_ge hij), min_eq_right (le_of_not_ge hij)]
    rfl

def rowMinor {n t : ℕ} (R : Type u) [CommRing R]
    (b : Fin t → Fin n) (f : Fin t → Fin n) : Polynomial n R :=
  Matrix.det (fun i j : Fin t => (X (toLex (f i, b j)) : Polynomial n R))

theorem rowMinor_eq_zero_of_not_injective {n t : ℕ} (R : Type u) [CommRing R]
    (b : Fin t → Fin n) (f : Fin t → Fin n) (hf : ¬Function.Injective f) :
    rowMinor R b f = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hne
  funext k
  simp only [hij]

theorem row_product {n t : ℕ} (R : Type u) [CommRing R]
    (a : Fin t → Fin n) (f : Fin t → Fin n) :
    (∏ i, generic n R (a i) (f i)) = monomial (assignmentExponent a f) 1 := by
  classical
  symm
  exact monomial_sum_one univ (fun i => single (toLex (f i, a i)) 1)

theorem rowMinor_eq_sum {n t : ℕ} (R : Type u) [CommRing R]
    (b : Fin t → Fin n) (f : Fin t → Fin n) :
    rowMinor R b f = ∑ σ : Equiv.Perm (Fin t),
      monomial (assignmentExponent b (f ∘ σ)) (signCoefficient R σ) := by
  classical
  unfold rowMinor
  erw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  have hp : (∏ p : Fin t, (X (toLex (f (σ p), b p)) : Polynomial n R)) =
      monomial (assignmentExponent b (f ∘ σ)) 1 := by
    exact row_product R b (f ∘ σ)
  rw [hp, smul_monomial]
  rfl

theorem rowMinor_degree_le {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (b : Fin t ↪o Fin n) (f : Fin t → Fin n)
    (hf : Function.Injective f) :
    (order n).degree (rowMinor R b f) ≼[order n] diagonalExponent h b := by
  classical
  rw [rowMinor_eq_sum]
  apply (order n).degree_sum_le.trans
  apply Finset.sup_le
  intro σ _
  exact ((order n).degree_monomial_le _).trans
    (assignmentExponent_le_diagonal h b (f ∘ σ) (hf.comp σ.injective))

private theorem first_comp_ne {n t : ℕ} (h : t ≤ n)
    (σ : Equiv.Perm (Fin t)) (hσ : σ ≠ 1) :
    firstColumns h ∘ σ ≠ firstColumns h := by
  intro he
  apply hσ
  apply Equiv.ext
  intro i
  exact firstColumns_injective h (congrFun he i)

theorem rowMinor_coeff_diagonal {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (b : Fin t ↪o Fin n) :
    (rowMinor R b (firstColumns h)).coeff (diagonalExponent h b) = 1 := by
  classical
  rw [rowMinor_eq_sum, coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin t))]
  · simp [assignmentExponent, diagonalExponent, signCoefficient]
  · intro σ _ hσ
    have hlt := assignmentExponent_lt_diagonal h b (firstColumns h ∘ σ)
      ((firstColumns_injective h).comp σ.injective) (first_comp_ne h σ hσ)
    have hn : assignmentExponent b (firstColumns h ∘ σ) ≠ diagonalExponent h b :=
      fun he => hlt.ne (congrArg (order n).toSyn he)
    simp [hn]
  · simp

theorem rowMinor_degree {n t : ℕ} (R : Type u) [CommRing R] [Nontrivial R]
    (h : t ≤ n) (b : Fin t ↪o Fin n) :
    (order n).degree (rowMinor R b (firstColumns h)) = diagonalExponent h b := by
  apply (order n).toSyn.injective
  apply le_antisymm (rowMinor_degree_le R h b _ (firstColumns_injective h))
  apply (order n).le_degree
  rw [MvPolynomial.mem_support_iff, rowMinor_coeff_diagonal R h b]
  exact one_ne_zero

theorem rowMinor_monic {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (b : Fin t ↪o Fin n) :
    (order n).Monic (rowMinor R b (firstColumns h)) := by
  nontriviality R
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff, rowMinor_degree R h b,
    rowMinor_coeff_diagonal R h b]

/-- The genuine determinant after applying the Gram polynomial map. -/
theorem hom_tupleMinor_eq_sum {n t : ℕ} (R : Type u) [CommRing R]
    (a b : Fin t → Fin n) :
    hom n R ((FourPapers.Symmetric.genericMatrix n R).submatrix a b).det = ∑ f : Fin t → Fin n,
      monomial (assignmentExponent a f) 1 * rowMinor R b f := by
  classical
  have hmat : (hom n R).mapMatrix
      ((FourPapers.Symmetric.genericMatrix n R).submatrix a b) =
      (matrix n R).submatrix a b := by
    funext i j
    exact hom_X_fold n R (a i) (b j)
  rw [AlgHom.map_det, hmat, matrix,
    Matrix.submatrix_mul _ _ a id b Function.bijective_id,
    determinant_product_expansion]
  apply Finset.sum_congr rfl
  intro f _
  change (∏ i, generic n R (a i) (f i)) * _ = _
  rw [row_product]
  rfl

theorem hom_minor_eq_sum {n t : ℕ} (R : Type u) [CommRing R]
    (a b : Fin t ↪o Fin n) :
    hom n R (minor R a b) = ∑ f : Fin t → Fin n,
      monomial (assignmentExponent a f) 1 * rowMinor R b f :=
  hom_tupleMinor_eq_sum R a b

def minorExponent {n t : ℕ} (h : t ≤ n) (a b : Fin t ↪o Fin n) :
    Variable n →₀ ℕ := diagonalExponent h a + diagonalExponent h b

private theorem gram_term_degree_le {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (a b : Fin t ↪o Fin n) (f : Fin t → Fin n)
    (hf : Function.Injective f) :
    (order n).degree (monomial (assignmentExponent a f) (1 : R) * rowMinor R b f)
      ≼[order n] minorExponent h a b := by
  apply (order n).degree_mul_le.trans
  change _ ≤ (order n).toSyn (diagonalExponent h a + diagonalExponent h b)
  rw [map_add]
  apply add_le_add
  · exact ((order n).degree_monomial_le _).trans (assignmentExponent_le_diagonal h a f hf)
  · exact rowMinor_degree_le R h b f hf

theorem hom_minor_degree_le {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (a b : Fin t ↪o Fin n) :
    (order n).degree (hom n R (minor R a b)) ≼[order n] minorExponent h a b := by
  classical
  rw [hom_minor_eq_sum]
  apply (order n).degree_sum_le.trans
  apply Finset.sup_le
  intro f _
  by_cases hf : Function.Injective f
  · exact gram_term_degree_le R h a b f hf
  · rw [rowMinor_eq_zero_of_not_injective R b f hf, mul_zero, MonomialOrder.degree_zero]
    exact bot_le

private theorem gram_term_degree_lt {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (a b : Fin t ↪o Fin n) (f : Fin t → Fin n)
    (hf : Function.Injective f) (hne : f ≠ firstColumns h) :
    (order n).degree (monomial (assignmentExponent a f) (1 : R) * rowMinor R b f)
      ≺[order n] minorExponent h a b := by
  apply (order n).degree_mul_le.trans_lt
  change _ < (order n).toSyn (diagonalExponent h a + diagonalExponent h b)
  rw [map_add]
  apply add_lt_add_of_lt_of_le
  · exact ((order n).degree_monomial_le _).trans_lt
      (assignmentExponent_lt_diagonal h a f hf hne)
  · exact rowMinor_degree_le R h b f hf

theorem hom_minor_coeff {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (a b : Fin t ↪o Fin n) :
    (hom n R (minor R a b)).coeff (minorExponent h a b) = 1 := by
  classical
  nontriviality R
  rw [hom_minor_eq_sum, coeff_sum, Finset.sum_eq_single (firstColumns h)]
  · have hm : (order n).Monic (monomial (diagonalExponent h a) (1 : R)) := by
      simp [MonomialOrder.Monic, MonomialOrder.leadingCoeff_monomial]
    have hn := rowMinor_monic R h b
    have hp := hm.mul hn
    have hd : (order n).degree (monomial (diagonalExponent h a) (1 : R) *
        rowMinor R b (firstColumns h)) = minorExponent h a b := by
      rw [(order n).degree_mul_of_mul_leadingCoeff_ne_zero
        (f := monomial (diagonalExponent h a) (1 : R))
        (g := rowMinor R b (firstColumns h))
        (by rw [hm.leadingCoeff_eq_one, hn.leadingCoeff_eq_one, one_mul]; exact one_ne_zero),
        (order n).degree_monomial (1 : R), rowMinor_degree R h b]
      simp only [one_ne_zero, ite_false, minorExponent]
    change (monomial (diagonalExponent h a) (1 : R) *
      rowMinor R b (firstColumns h)).coeff (minorExponent h a b) = 1
    rw [← hd]
    exact hp
  · intro f _ hne
    by_cases hf : Function.Injective f
    · exact (order n).coeff_eq_zero_of_lt (gram_term_degree_lt R h a b f hf hne)
    · simp only [rowMinor_eq_zero_of_not_injective R b f hf, mul_zero,
        MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · simp

theorem hom_minor_degree {n t : ℕ} (R : Type u) [CommRing R] [Nontrivial R]
    (h : t ≤ n) (a b : Fin t ↪o Fin n) :
    (order n).degree (hom n R (minor R a b)) = minorExponent h a b := by
  apply (order n).toSyn.injective
  apply le_antisymm (hom_minor_degree_le R h a b)
  apply (order n).le_degree
  rw [MvPolynomial.mem_support_iff, hom_minor_coeff R h a b]
  exact one_ne_zero

theorem hom_minor_monic {n t : ℕ} (R : Type u) [CommRing R]
    (h : t ≤ n) (a b : Fin t ↪o Fin n) :
    (order n).Monic (hom n R (minor R a b)) := by
  nontriviality R
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff, hom_minor_degree R h a b,
    hom_minor_coeff R h a b]

end FourPapers.Symmetric.Gram
end
end
/- End GramMinors.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "GramFoundation BEGIN GramWeights\n"
  logInfo "GramFoundation BEGIN GramWeights"

/- Begin GramWeights.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Real weighted orders in Gram coordinates

A nonnegative score vector gives column weights by cumulative sums.  Every
injective choice of t columns has at least the weight of the first t columns.
Consequently every actual t-minor has Gram weight at least twice its
weighted symbolic score.  Its distinguished monic leading term attains the
bound.  The coefficient field is independent of the real weight field.
-/

noncomputable section
namespace FourPapers.Symmetric.Gram
open Finset Finsupp MvPolynomial
open CommAlg.RealWeight
open scoped BigOperators
universe u

/-- Cumulative column weights, starting at column zero. -/
def columnWeight {n : ℕ} (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => j ≤ i), w j

/-- The row coordinate does not change a variable's weight. -/
def weight {n : ℕ} (w : Fin n → ℝ) (v : Variable n) : ℝ := columnWeight w v.1

theorem columnWeight_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (i : Fin n) : 0 ≤ columnWeight w i :=
  Finset.sum_nonneg (fun j _ => hw j)

theorem columnWeight_mono {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Monotone (columnWeight w) := by
  intro i k hik
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2.trans hik⟩
  · intro j _ _
    exact hw j

theorem weight_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (v : Variable n) : 0 ≤ weight w v := columnWeight_nonneg w hw v.1

theorem bound_zero_of_nonnegative_weight {n : ℕ} (R : Type u) [CommRing R]
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (p : Polynomial n R) :
    Bound (weight w) 0 p := by
  intro a _
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun v _ => smul_nonneg (Nat.zero_le _) (weight_nonneg w hw v))

private theorem increasing_index_le {t n : ℕ} (c : Fin t ↪o Fin n) (i : Fin t) :
    i.val ≤ (c i).val := by
  have aux : ∀ k (hk : k < t), k ≤ (c ⟨k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < t := Nat.lt_of_succ_lt hk
      have hstep : (c ⟨k,hk'⟩).val < (c ⟨k+1,hk⟩).val :=
        c.strictMono (show (⟨k,hk'⟩ : Fin t) < ⟨k+1,hk⟩ from Nat.lt_succ_self k)
      exact Nat.succ_le_of_lt ((ih hk').trans_lt hstep)
  exact aux i.val i.isLt

/-- The first columns minimize the sum of every monotone column cost. -/
theorem sum_firstColumns_le {t n : ℕ} (h : t ≤ n) (f : Fin t → Fin n)
    (hf : Function.Injective f) (c : Fin n → ℝ) (hc : Monotone c) :
    (∑ i, c (firstColumns h i)) ≤ ∑ i, c (f i) := by
  classical
  let S : Finset (Fin n) := univ.image f
  have hcard : S.card = t := by
    simp only [S, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let e : Fin t ↪o Fin n := S.orderEmbOfFin hcard
  have hsum : (∑ i : Fin t, c (e i)) = ∑ i : Fin t, c (f i) := by
    calc
      (∑ i : Fin t, c (e i)) = ∑ x ∈ S, c x := by
        rw [← Finset.sum_image (fun i _ j _ hij => e.injective hij)]
        simp only [e, Finset.image_orderEmbOfFin_univ]
      _ = ∑ i : Fin t, c (f i) := by
        exact Finset.sum_image (fun i _ j _ hij => hf hij)
  rw [← hsum]
  exact Finset.sum_le_sum (fun i _ => hc (increasing_index_le e i))

private theorem card_fin_ge (t k : ℕ) :
    (univ.filter (fun i : Fin t => k ≤ i.val)).card = t - k := by
  by_cases hk : k < t
  · have he : univ.filter (fun i : Fin t => k ≤ i.val) = Ici (⟨k,hk⟩ : Fin t) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_Ici, Fin.le_def]
    rw [he, Fin.card_Ici]
  · have he : univ.filter (fun i : Fin t => k ≤ i.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := (mem_filter.mp hi).2
      omega
    rw [he, card_empty, Nat.sub_eq_zero_of_le (le_of_not_gt hk)]

/-- Summing cumulative weights over the first columns gives the usual
minor score, with truncated subtraction for columns beyond the minor size. -/
theorem sum_firstColumns_weight {t n : ℕ} (h : t ≤ n) (w : Fin n → ℝ) :
    (∑ i : Fin t, columnWeight w (firstColumns h i)) =
      ∑ j : Fin n, w j * (t - j.val : ℕ) := by
  classical
  simp only [columnWeight, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun i : Fin t => if j ≤ firstColumns h i then w j else 0) =
      (fun i : Fin t => if j.val ≤ i.val then w j else 0) := by
    funext i
    rfl
  rw [he, ← Finset.sum_filter, Finset.sum_const, card_fin_ge]
  simp only [nsmul_eq_mul, mul_comm]

@[simp] theorem assignmentExponent_weight {t n : ℕ} (a f : Fin t → Fin n)
    (w : Fin n → ℝ) :
    Finsupp.weight (weight w) (assignmentExponent a f) = ∑ i, columnWeight w (f i) := by
  simp only [assignmentExponent, map_sum, Finsupp.weight_single, one_smul, weight]
  rfl

theorem minorExponent_weight {t n : ℕ} (h : t ≤ n)
    (a b : Fin t ↪o Fin n) (w : Fin n → ℝ) :
    Finsupp.weight (weight w) (minorExponent h a b) =
      2 * ∑ j : Fin n, w j * (t - j.val : ℕ) := by
  simp only [minorExponent, map_add, diagonalExponent, assignmentExponent_weight,
    sum_firstColumns_weight]
  ring

private theorem bound_monomial (R : Type u) [CommRing R] {n : ℕ}
    (w : Fin n → ℝ) (a : Variable n →₀ ℕ) (c : R) :
    Bound (weight w) (Finsupp.weight (weight w) a) (monomial a c) := by
  intro b hb
  have he : a = b := by
    by_contra hn
    simp only [coeff_monomial, hn, ite_false] at hb
    exact hb rfl
  subst b
  exact le_rfl

theorem rowMinor_bound {n t : ℕ} (R : Type u) [CommRing R]
    (b f : Fin t → Fin n) (w : Fin n → ℝ) :
    Bound (weight w) (∑ i, columnWeight w (f i)) (rowMinor R b f) := by
  classical
  rw [rowMinor_eq_sum]
  apply bound_sum
  intro σ _
  have hb := bound_monomial R w (assignmentExponent b (f ∘ σ)) (signCoefficient R σ)
  rw [assignmentExponent_weight] at hb
  have he : (∑ i, columnWeight w ((f ∘ σ) i)) = ∑ i, columnWeight w (f i) :=
    Equiv.sum_comp σ (fun i => columnWeight w (f i))
  rwa [he] at hb

/-- The lower weight bound holds for every literal tuple minor, including
repeated row/column lists and sizes exceeding the matrix size. -/
theorem hom_tupleMinor_bound {n t : ℕ} (R : Type u) [CommRing R]
    (a b : Fin t → Fin n) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Bound (weight w) (2 * ∑ j : Fin n, w j * (t - j.val : ℕ))
      (hom n R ((FourPapers.Symmetric.genericMatrix n R).submatrix a b).det) := by
  classical
  rw [hom_tupleMinor_eq_sum]
  apply bound_sum
  intro f _
  by_cases hf : Function.Injective f
  · have htn : t ≤ n := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    have hb := (bound_monomial R w (assignmentExponent a f) 1).mul (rowMinor_bound R b f w)
    rw [assignmentExponent_weight] at hb
    apply hb.mono
    have hc := sum_firstColumns_le htn f hf (columnWeight w) (columnWeight_mono w hw)
    rw [sum_firstColumns_weight] at hc
    linarith
  · rw [rowMinor_eq_zero_of_not_injective R b f hf, mul_zero]
    exact bound_zero _ _

theorem hom_minor_bound {n t : ℕ} (R : Type u) [CommRing R]
    (a b : Fin t ↪o Fin n) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    Bound (weight w) (2 * ∑ j : Fin n, w j * (t - j.val : ℕ))
      (hom n R (minor R a b)) :=
  hom_tupleMinor_bound R a b w hw

end FourPapers.Symmetric.Gram
end
end
/- End GramWeights.lean -/

open Lean Elab Command in
run_cmd do
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/canonical_progress.txt" "GramFoundation BEGIN MonicWeightFamilies\n"
  logInfo "GramFoundation BEGIN MonicWeightFamilies"

/- Begin MonicWeightFamilies.lean -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Independent monic families and exact weighted support

Distinct leading exponents prevent cancellation in finite linear combinations.
The same argument, applied only to terms below a proposed weight threshold,
proves that a monic family whose leading terms attain their minimum weights
is adapted to every one of those weighted filtrations.
-/

noncomputable section
namespace CommAlg.RealWeight
open Finset MvPolynomial
open scoped MonomialOrder

variable {σ ι K : Type*} [Field K] [DecidableEq σ]

/-- A family with pairwise distinct monic leading terms is linearly independent. -/
theorem linearIndependent_of_distinct_monic
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ K)
    (hmonic : ∀ i, m.Monic (p i))
    (hdegree : Function.Injective (fun i => m.degree (p i))) :
    LinearIndependent K p := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  by_contra hci
  let S := s.filter (fun j => c j ≠ 0)
  have hS : S.Nonempty := ⟨i, mem_filter.mpr ⟨hi,hci⟩⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image S (fun j => m.toSyn (m.degree (p j))) hS
  have hjs := (mem_filter.mp hj).1
  have hcj := (mem_filter.mp hj).2
  have hc : (∑ k ∈ s, c k • p k).coeff (m.degree (p j)) = c j := by
    rw [coeff_sum, Finset.sum_eq_single j]
    · rw [coeff_smul, (hmonic j).coeff_degree, smul_eq_mul, mul_one]
    · intro k hk hkj
      by_cases hck : c k = 0
      · simp [hck]
      · have hkS : k ∈ S := mem_filter.mpr ⟨hk,hck⟩
        have hlt : m.degree (p k) ≺[m] m.degree (p j) := by
          apply lt_of_le_of_ne (hmax k hkS)
          intro he
          exact hkj (hdegree (m.toSyn.injective he))
        rw [coeff_smul, m.coeff_eq_zero_of_lt hlt, smul_zero]
    · exact fun h => (h hjs).elim
  rw [hsum, MvPolynomial.coeff_zero] at hc
  exact hcj hc.symm

/-- Exact weight membership of a finite linear combination, with no
assumption on characteristic and no cancellation hypothesis left implicit. -/
theorem bound_sum_iff_of_distinct_monic
    (m : MonomialOrder σ) (p : ι → MvPolynomial σ K)
    (hmonic : ∀ i, m.Monic (p i))
    (hdegree : Function.Injective (fun i => m.degree (p i)))
    (w : σ → ℝ) (v : ι → ℝ)
    (hp : ∀ i, Bound w (v i) (p i))
    (hv : ∀ i, Finsupp.weight w (m.degree (p i)) = v i)
    (s : Finset ι) (c : ι → K) (b : ℝ) :
    Bound w b (∑ i ∈ s, c i • p i) ↔
      ∀ i ∈ s, c i ≠ 0 → b ≤ v i := by
  classical
  constructor
  · intro h i hi hci
    by_contra hbad
    let S := s.filter (fun j => c j ≠ 0 ∧ v j < b)
    have hS : S.Nonempty := ⟨i, mem_filter.mpr ⟨hi,hci,lt_of_not_ge hbad⟩⟩
    obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image S
      (fun j => m.toSyn (m.degree (p j))) hS
    obtain ⟨hjs,hcj,hvj⟩ := mem_filter.mp hj
    have hc : (∑ k ∈ s, c k • p k).coeff (m.degree (p j)) = c j := by
      rw [coeff_sum, Finset.sum_eq_single j]
      · rw [coeff_smul, (hmonic j).coeff_degree, smul_eq_mul, mul_one]
      · intro k hk hkj
        by_cases hck : c k = 0
        · simp [hck]
        have hzero : (p k).coeff (m.degree (p j)) = 0 := by
          by_cases hvk : v k < b
          · have hkS : k ∈ S := mem_filter.mpr ⟨hk,hck,hvk⟩
            have hlt : m.degree (p k) ≺[m] m.degree (p j) := by
              apply lt_of_le_of_ne (hmax k hkS)
              intro he
              exact hkj (hdegree (m.toSyn.injective he))
            exact m.coeff_eq_zero_of_lt hlt
          · by_contra hn
            have hb := hp k _ hn
            rw [hv] at hb
            exact (not_lt_of_ge ((le_of_not_gt hvk).trans hb)) hvj
        rw [coeff_smul,hzero,smul_zero]
      · exact fun hn => (hn hjs).elim
    have hb := h (m.degree (p j)) (by rw [hc]; exact hcj)
    rw [hv] at hb
    exact (not_lt_of_ge hb) hvj
  · intro h
    apply bound_sum
    intro i hi a ha
    have hci : c i ≠ 0 := by intro he; simp [he] at ha
    have hpa : (p i).coeff a ≠ 0 := by
      intro he
      simp [coeff_smul,he] at ha
    exact (h i hi hci).trans (hp i a hpa)

end CommAlg.RealWeight
end
end
/- End MonicWeightFamilies.lean -/

#print axioms FourPapers.Symmetric.Gram.hom_minor_degree
#print axioms FourPapers.Symmetric.Gram.hom_minor_monic
#print axioms FourPapers.Symmetric.Gram.hom_tupleMinor_bound
#print axioms CommAlg.RealWeight.linearIndependent_of_distinct_monic
#print axioms CommAlg.RealWeight.bound_sum_iff_of_distinct_monic

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let roots : Array Name := #[
    "FourPapers.Symmetric.Gram.hom_minor_degree".toName,
    "FourPapers.Symmetric.Gram.hom_minor_monic".toName,
    "FourPapers.Symmetric.Gram.hom_tupleMinor_bound".toName,
    "CommAlg.RealWeight.linearIndependent_of_distinct_monic".toName,
    "CommAlg.RealWeight.bound_sum_iff_of_distinct_monic".toName]
  let mut runtimeOnly : Array Name := #[]
  let mut auditedImports : NameSet := {}
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      runtimeOnly := runtimeOnly.push name
    else
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
          if info.isAxiom && !auditedImports.contains dep then
            -- Exported theorems may have axiom-shaped public declarations. Stock Lean's
            -- exportedAxiomsExt stores their checked, transitive axiom dependencies.
            -- collectAxioms uses that metadata rather than misclassifying proof stubs.
            let deps ← collectAxioms dep
            for ax in deps do
              if !allowed.contains ax then
                throwError "Unapproved imported axiom {ax}, reached through {dep} in {name}"
            auditedImports := auditedImports.insert dep
  let mut rootAxioms : Array Json := #[]
  for root in roots do
    unless env.contains root do
      throwError "Required final theorem is unavailable: {root}"
    let axioms ← collectAxioms root
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Unapproved transitive axiom in {root}: {ax}"
    rootAxioms := rootAxioms.push <| Json.mkObj [
      ("theorem", toJson root.toString), ("axioms", toJson (axioms.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  for root in roots do
    names := names.insert root
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtimeOnly.map Name.toString))]
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/gram_foundation_dependency_graph.json" (Json.compress graph)
  logInfo m!"GRAM_FOUNDATION_AUDIT_OK {constants.size} local declarations; {roots.size} verification roots; only propext, Classical.choice, Quot.sound; no authored axioms or unsafe proof dependencies."

