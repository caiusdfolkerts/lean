module

public import PaperVerification.AlternatingFormsIntervalPlucker
public import TauCeti.RepresentationTheory.Symmetric.Specht.Straightening
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Rectangular polytabloids and products of maximal minors

The map in this file sends a row tabloid to the literal matrix-entry monomial
recording the row occupied by each label. Column antisymmetrization therefore
maps to a product of actual determinants. This identifies the hypotheses of the
existing rational Specht straightening theorem with the maximal-minor
straightening problem; no standard-monomial relation is introduced as an axiom.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial TauCeti

namespace PaperVerification.AlternatingForms

def minorRectangle (s r : ℕ) : YoungDiagram where
  cells := Finset.range s ×ˢ Finset.range r
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe,Finset.mem_product,Finset.mem_range] at hb ⊢
    exact ⟨hab.1.trans_lt hb.1,hab.2.trans_lt hb.2⟩

@[simp] theorem mem_minorRectangle {s r i j : ℕ} :
    (i,j) ∈ minorRectangle s r ↔ i < s ∧ j < r := by
  simp [minorRectangle]

def rectangleCellEquiv (s r : ℕ) : ↥(minorRectangle s r).cells ≃ Fin s × Fin r where
  toFun c := ⟨⟨c.val.1,(mem_minorRectangle.mp c.property).1⟩,
    ⟨c.val.2,(mem_minorRectangle.mp c.property).2⟩⟩
  invFun p := ⟨(p.1.val,p.2.val),mem_minorRectangle.mpr ⟨p.1.isLt,p.2.isLt⟩⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

variable {s r n : ℕ}

def rectangleLabels (t : YoungTableau (minorRectangle s r)) :
    Fin s × Fin r ≃ Fin (minorRectangle s r).card :=
  (rectangleCellEquiv s r).symm.trans t

def rectangleRow (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) : Fin s :=
  ((rectangleLabels t).symm k).1

def rectangleColumn (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) : Fin r :=
  ((rectangleLabels t).symm k).2

@[simp] theorem rectangleRow_val (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) :
    (rectangleRow t k).val = YoungTableau.rowIndex t k := by
  rw [YoungTableau.rowIndex_def]
  rfl

@[simp] theorem rectangleColumn_val (t : YoungTableau (minorRectangle s r))
    (k : Fin (minorRectangle s r).card) :
    (rectangleColumn t k).val = YoungTableau.colIndex t k := by
  rw [YoungTableau.colIndex_def]
  rfl

@[simp] theorem rectangleRow_labels (t : YoungTableau (minorRectangle s r))
    (i : Fin s) (j : Fin r) : rectangleRow t (rectangleLabels t (i,j)) = i := by
  simp [rectangleRow]

@[simp] theorem rectangleColumn_labels (t : YoungTableau (minorRectangle s r))
    (i : Fin s) (j : Fin r) : rectangleColumn t (rectangleLabels t (i,j)) = j := by
  simp [rectangleColumn]

def rectangularRowMonomial
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) : MvPolynomial (Fin s × Fin n) ℚ :=
  ∏ k, X (rectangleRow t k,v k)

theorem rectangularRowMonomial_eq_of_tabloid_eq
    (v : Fin (minorRectangle s r).card → Fin n)
    {t u : YoungTableau (minorRectangle s r)}
    (h : YoungTableau.tabloid t = YoungTableau.tabloid u) :
    rectangularRowMonomial v t = rectangularRowMonomial v u := by
  apply Finset.prod_congr rfl
  intro k hk
  congr 2
  apply Fin.ext
  rw [rectangleRow_val, rectangleRow_val]
  exact congrFun (YoungTableau.tabloid_eq_iff_rowIndex_eq.mp h) k

def rectangularTabloidMonomial
    (v : Fin (minorRectangle s r).card → Fin n)
    (q : Equiv.Perm (Fin (minorRectangle s r).card) ⧸
      youngSubgroup (shapePartition (minorRectangle s r))) :
    MvPolynomial (Fin s × Fin n) ℚ :=
  rectangularRowMonomial v (Classical.choose (YoungTableau.tabloid_surjective q))

@[simp] theorem rectangularTabloidMonomial_tabloid
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularTabloidMonomial v (YoungTableau.tabloid t) = rectangularRowMonomial v t := by
  apply rectangularRowMonomial_eq_of_tabloid_eq
  exact Classical.choose_spec (YoungTableau.tabloid_surjective (YoungTableau.tabloid t))

def rectangularTabloidMap (v : Fin (minorRectangle s r).card → Fin n) :
    (permutationModule (shapePartition (minorRectangle s r))).V →ₗ[ℚ]
      MvPolynomial (Fin s × Fin n) ℚ :=
  (permutationModuleBasis (shapePartition (minorRectangle s r))).constr ℚ
    (rectangularTabloidMonomial v)

@[simp] theorem rectangularTabloidMap_single
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularTabloidMap v (MonoidAlgebra.single (YoungTableau.tabloid t) 1) =
      rectangularRowMonomial v t := by
  simpa only [rectangularTabloidMap,permutationModuleBasis,MonoidAlgebra.basis_apply,
    rectangularTabloidMonomial_tabloid] using
    (permutationModuleBasis (shapePartition (minorRectangle s r))).constr_basis ℚ
      (rectangularTabloidMonomial v) (YoungTableau.tabloid t)

def rectangleColumnPermutation (t : YoungTableau (minorRectangle s r))
    (σ : Fin r → Equiv.Perm (Fin s)) : YoungTableau.colSubgroup t :=
  ⟨(rectangleLabels t).permCongr (Equiv.prodCongrLeft fun j => (σ j).symm),by
    rw [YoungTableau.mem_colSubgroup]
    intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := (rectangleLabels t).surjective k
    rw [← rectangleColumn_val, ← rectangleColumn_val]
    simp [Equiv.permCongr_apply,Equiv.prodCongrLeft_apply]⟩

@[simp] theorem rectangleColumnPermutation_apply
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s))
    (i : Fin s) (j : Fin r) :
    (rectangleColumnPermutation t σ : Equiv.Perm _) (rectangleLabels t (i,j)) =
      rectangleLabels t ((σ j).symm i,j) := by
  simp [rectangleColumnPermutation,Equiv.permCongr_apply,Equiv.prodCongrLeft_apply]

@[simp] theorem rectangleColumnPermutation_inv_apply
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s))
    (i : Fin s) (j : Fin r) :
    (rectangleColumnPermutation t σ : Equiv.Perm _).symm (rectangleLabels t (i,j)) =
      rectangleLabels t (σ j i,j) := by
  apply (rectangleColumnPermutation t σ : Equiv.Perm _).injective
  simp

theorem rectangleColumn_preserved (t : YoungTableau (minorRectangle s r))
    (q : YoungTableau.colSubgroup t) (k : Fin (minorRectangle s r).card) :
    rectangleColumn t ((q : Equiv.Perm _) k) = rectangleColumn t k := by
  apply Fin.ext
  rw [rectangleColumn_val, rectangleColumn_val]
  exact YoungTableau.mem_colSubgroup.mp q.property k

def rectangleColumnRows (t : YoungTableau (minorRectangle s r))
    (q : YoungTableau.colSubgroup t) (j : Fin r) : Equiv.Perm (Fin s) where
  toFun i := rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t (i,j)))
  invFun i := rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j)))
  left_inv i := by
    have hp : (rectangleLabels t).symm
        ((q : Equiv.Perm _).symm (rectangleLabels t (i,j))) =
        (rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t (i,j))),j) := by
      apply Prod.ext
      · rfl
      · have hc := rectangleColumn_preserved t q
          ((q : Equiv.Perm _).symm (rectangleLabels t (i,j)))
        rw [Equiv.apply_symm_apply] at hc
        exact hc.symm.trans (rectangleColumn_labels t i j)
    change rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t
      (rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t (i,j))),j))) = i
    rw [← hp,Equiv.apply_symm_apply,Equiv.apply_symm_apply,rectangleRow_labels]
  right_inv i := by
    have hp : (rectangleLabels t).symm ((q : Equiv.Perm _) (rectangleLabels t (i,j))) =
        (rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j))),j) := by
      apply Prod.ext
      · rfl
      · exact (rectangleColumn_preserved t q (rectangleLabels t (i,j))).trans
          (rectangleColumn_labels t i j)
    change rectangleRow t ((q : Equiv.Perm _).symm (rectangleLabels t
      (rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j))),j))) = i
    rw [← hp,Equiv.apply_symm_apply,Equiv.symm_apply_apply,rectangleRow_labels]

def rectangleColumnPermutationEquiv (t : YoungTableau (minorRectangle s r)) :
    (Fin r → Equiv.Perm (Fin s)) ≃ YoungTableau.colSubgroup t where
  toFun := rectangleColumnPermutation t
  invFun := rectangleColumnRows t
  left_inv σ := by
    funext j
    apply Equiv.ext
    intro i
    simp [rectangleColumnRows]
  right_inv q := by
    apply Subtype.ext
    apply Equiv.ext
    intro k
    obtain ⟨⟨i,j⟩,rfl⟩ := (rectangleLabels t).surjective k
    rw [rectangleColumnPermutation_apply]
    change rectangleLabels t (rectangleRow t ((q : Equiv.Perm _) (rectangleLabels t (i,j))),j) = _
    apply (rectangleLabels t).symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · exact ((rectangleColumn_preserved t q (rectangleLabels t (i,j))).trans
        (rectangleColumn_labels t i j)).symm

@[simp] theorem rectangleColumnPermutationEquiv_apply
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s)) :
    rectangleColumnPermutationEquiv t σ = rectangleColumnPermutation t σ := rfl

theorem rectangleColumnPermutation_sign (t : YoungTableau (minorRectangle s r))
    (σ : Fin r → Equiv.Perm (Fin s)) :
    Equiv.Perm.sign (rectangleColumnPermutation t σ).val =
      ∏ j, Equiv.Perm.sign (σ j) := by
  simp only [rectangleColumnPermutation,Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_prodCongrLeft,Equiv.Perm.sign_symm]

theorem rectangularRowMonomial_column_relabel
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) (σ : Fin r → Equiv.Perm (Fin s)) :
    rectangularRowMonomial v
      (YoungTableau.relabel (rectangleColumnPermutation t σ : Equiv.Perm _) t) =
      ∏ j, ∏ i, (X (σ j i,v (rectangleLabels t (i,j))) :
        MvPolynomial (Fin s × Fin n) ℚ) := by
  classical
  rw [rectangularRowMonomial,← Equiv.prod_comp (rectangleLabels t)]
  rw [Fintype.prod_prod_type,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  apply Fin.ext
  rw [rectangleRow_val,YoungTableau.rowIndex_relabel]
  rw [← rectangleRow_val]
  change (rectangleRow t ((rectangleColumnPermutation t σ : Equiv.Perm _).symm
    (rectangleLabels t (i,j)))).val = _
  simp only [rectangleColumnPermutation_inv_apply, rectangleRow_labels]

/-- Actual products of maximal minors, with arbitrary column values before
straightening. Repeated values are permitted at this intermediate stage. -/
def rectangularMinorProduct
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) : MvPolynomial (Fin s × Fin n) ℚ :=
  ∏ j, Matrix.det (Matrix.of (fun i k : Fin s => X (i,v (rectangleLabels t (k,j)))))

/-- Normalize the sign scalar before instantiating it at the large polynomial
and permutation-module expressions. This is the ordinary product-smul law. -/
private theorem rational_units_smul_prod
    {A : Type*} [CommRing A] [Algebra ℚ A]
    {ι : Type*} [Fintype ι] (c : ι → ℤˣ) (f : ι → A) :
    (((∏ i, c i : ℤˣ) : ℤ) : ℚ) • (∏ i, f i) = ∏ i, c i • f i := by
  rw [Finset.prod_smul]
  simp only [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- One actual column-antisymmetrizer summand maps to the corresponding
product of determinant summands. All relabeling and scalar conversions are
proved before the outer sum is formed. -/
theorem rectangularTabloidMap_signed_column
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r))
    (σ : Fin r → Equiv.Perm (Fin s)) :
    rectangularTabloidMap v
      (((Equiv.Perm.sign (rectangleColumnPermutation t σ).val : ℤ) : ℚ) •
        MonoidAlgebra.single
          ((rectangleColumnPermutation t σ).val • YoungTableau.tabloid t) (1 : ℚ)) =
      ∏ j, Equiv.Perm.sign (σ j) •
        ∏ i, (X (σ j i, v (rectangleLabels t (i,j))) :
          MvPolynomial (Fin s × Fin n) ℚ) := by
  rw [map_smul, ← YoungTableau.tabloid_relabel, rectangularTabloidMap_single,
    rectangleColumnPermutation_sign, rectangularRowMonomial_column_relabel]
  exact rational_units_smul_prod
    (fun j => Equiv.Perm.sign (σ j))
    (fun j => ∏ i, (X (σ j i, v (rectangleLabels t (i,j))) :
      MvPolynomial (Fin s × Fin n) ℚ))

theorem rectangularTabloidMap_polytabloid
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularTabloidMap v (YoungTableau.polytabloid t) = rectangularMinorProduct v t := by
  classical
  rw [YoungTableau.polytabloid_eq_sum,map_sum,
    ← Equiv.sum_comp (rectangleColumnPermutationEquiv t)]
  simp only [rectangleColumnPermutationEquiv_apply, rectangularMinorProduct,
    Matrix.det_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact rectangularTabloidMap_signed_column v t σ

/-- The exact rational Specht straightening theorem transported through the
literal matrix-monomial map. -/
theorem rectangularMinorProduct_mem_span_standard
    (v : Fin (minorRectangle s r).card → Fin n)
    (t : YoungTableau (minorRectangle s r)) :
    rectangularMinorProduct v t ∈ Submodule.span ℚ
      (Set.range fun T : StandardYoungTableau (minorRectangle s r) =>
        rectangularMinorProduct v T.toTableau) := by
  rw [← rectangularTabloidMap_polytabloid]
  have h := YoungTableau.polytabloid_mem_span_polytabloid_standard t
  refine Submodule.span_induction
    (p := fun x _ => rectangularTabloidMap v x ∈ Submodule.span ℚ
      (Set.range fun T : StandardYoungTableau (minorRectangle s r) =>
        rectangularMinorProduct v T.toTableau)) ?_ ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨T,rfl⟩ := hx
    rw [rectangularTabloidMap_polytabloid]
    exact Submodule.subset_span ⟨T,rfl⟩
  · simpa only [map_zero] using (Submodule.span ℚ _).zero_mem
  · intro x y hx hy hmx hmy
    simpa only [map_add] using (Submodule.span ℚ _).add_mem hmx hmy
  · intro a x hx hmx
    simpa only [map_smul] using (Submodule.span ℚ _).smul_mem a hmx

end PaperVerification.AlternatingForms
