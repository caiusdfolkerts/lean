module

public import PaperVerification.FermionNewtonRestrictionNumerator
public import PaperVerification.FermionHomogeneousFreeHilbert

/-!
# Linear restriction, its exact kernel, and its homogeneous shift

The smaller numerator is defined by the actual division forced by the normal
relations. Cancellation of its nonzero divisor proves additivity, scalar
linearity, the deletion kernel, and the precise loss of homogeneous degree.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

theorem coordinateProduct_homogeneous (T : Finset (Fin n)) :
    (coordinateProduct (F := F) T).IsHomogeneous T.card := by
  have h := IsHomogeneous.prod T (X : Fin n → MvPolynomial (Fin n) F) (fun _ ↦ 1)
    (fun i hi ↦ isHomogeneous_X F i)
  simpa only [coordinateProduct, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one] using h

def numeratorRestriction
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q) :
    numeratorModule β δ σ →ₗ[F]
      numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove) where
  toFun a := ⟨restrictedNumerator β δ σ hβ q hq a,
    restrictedNumerator_mem β δ σ hβ q hq a⟩
  map_add' a b := by
    apply Subtype.ext
    funext i
    apply mul_left_cancel₀ (coordinateProduct_ne_zero (F := F) (negativeNeighbours σ q))
    change coordinateProduct (negativeNeighbours σ q) * restrictedNumerator β δ σ hβ q hq (a + b) i =
      coordinateProduct (negativeNeighbours σ q) *
        (restrictedNumerator β δ σ hβ q hq a i + restrictedNumerator β δ σ hβ q hq b i)
    rw [mul_add, restrictedNumerator_relation, restrictedNumerator_relation,
      restrictedNumerator_relation]
    exact map_add (removeCoordinate q) _ _
  map_smul' c a := by
    apply Subtype.ext
    funext i
    apply mul_left_cancel₀ (coordinateProduct_ne_zero (F := F) (negativeNeighbours σ q))
    change _ = coordinateProduct (negativeNeighbours σ q) * (c • _)
    rw [mul_smul_comm, restrictedNumerator_relation, restrictedNumerator_relation]
    exact map_smul (removeCoordinate q) c _

@[simp] theorem numeratorRestriction_apply
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (i : Fin n) :
    (numeratorRestriction β δ σ hβ q hq a).val i = restrictedNumerator β δ σ hβ q hq a i := rfl

theorem numeratorRestriction_eq_zero_iff
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) :
    numeratorRestriction β δ σ hβ q hq a = 0 ↔
      ∀ i : Fin n, removeCoordinate q (a.val (q.succAbove i)) = 0 := by
  constructor
  · intro h i
    rw [← restrictedNumerator_relation β δ σ hβ q hq a i]
    have hi := congrArg (fun z ↦ z.val i) h
    change restrictedNumerator β δ σ hβ q hq a i = 0 at hi
    rw [hi,mul_zero]
  · intro h
    apply Subtype.ext
    funext i
    apply mul_left_cancel₀ (coordinateProduct_ne_zero (F := F) (negativeNeighbours σ q))
    change coordinateProduct (negativeNeighbours σ q) * restrictedNumerator β δ σ hβ q hq a i =
      coordinateProduct (negativeNeighbours σ q) * 0
    rw [mul_zero]
    exact (restrictedNumerator_relation β δ σ hβ q hq a i).trans (h i)

def deletionMultiplication
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q) :
    numeratorModule β (deletedMultiplicity δ q) σ →ₗ[F] numeratorModule β δ σ where
  toFun a := ⟨X q • a.val,
    (smul_mem_numeratorModule_iff_deleted β δ σ q hq a.val).mpr a.property⟩
  map_add' a b := by apply Subtype.ext; exact smul_add _ _ _
  map_smul' c a := by apply Subtype.ext; exact smul_comm _ _ _

theorem deletionMultiplication_injective
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q) :
    Function.Injective (deletionMultiplication β δ σ q hq) := by
  intro a b h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z ↦ z.val i) h
  exact mul_left_cancel₀ (X_ne_zero q) hi

/-- The kernel is exactly the deleted module multiplied by the removed
coordinate, inside the actual source numerator module. -/
theorem numeratorRestriction_ker
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q) :
    LinearMap.ker (numeratorRestriction β δ σ hβ q hq) =
      LinearMap.range (deletionMultiplication β δ σ q hq) := by
  ext a
  rw [LinearMap.mem_ker, numeratorRestriction_eq_zero_iff,
    removed_restriction_kernel β δ σ q hq a.val a.property]
  constructor
  · rintro ⟨b,hb,hab⟩
    exact ⟨⟨b,hb⟩,Subtype.ext hab.symm⟩
  · rintro ⟨b,hb⟩
    exact ⟨b.val,b.property,(congrArg Subtype.val hb).symm⟩

theorem homogeneous_quotient_of_relation
    {D A p : MvPolynomial (Fin n) F} {d e : ℕ}
    (hD : D.IsHomogeneous d) (hD0 : D ≠ 0) (hp : p.IsHomogeneous e)
    (h : D * A = p) (hde : d ≤ e) : A.IsHomogeneous (e - d) := by
  by_cases hA : A = 0
  · rw [hA]
    exact isHomogeneous_zero (Fin n) F _
  · have hprod : (D * A).IsHomogeneous e := by rw [h]; exact hp
    have hprod0 := mul_ne_zero hD0 hA
    have ha := hprod.of_mul_right hprod0
    have hd := hprod.totalDegree hprod0
    rw [totalDegree_mul_of_isDomain hD0 hA, hD.totalDegree hD0] at hd
    have hdegree : A.totalDegree = e - d := by omega
    simpa only [hdegree] using ha

theorem quotient_zero_of_homogeneous_relation_lt
    {D A p : MvPolynomial (Fin n) F} {d e : ℕ}
    (hD : D.IsHomogeneous d) (hD0 : D ≠ 0) (hp : p.IsHomogeneous e)
    (h : D * A = p) (hde : e < d) : A = 0 := by
  by_contra hA
  have hprod : (D * A).IsHomogeneous e := by rw [h]; exact hp
  have hd := hprod.totalDegree (mul_ne_zero hD0 hA)
  rw [totalDegree_mul_of_isDomain hD0 hA, hD.totalDegree hD0] at hd
  omega

/-- The degree shift is the number of incident negative edges. -/
theorem numeratorRestriction_homogeneous
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (e : ℕ)
    (ha : a ∈ GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ)
      (e + (negativeNeighbours σ q).card)) :
    numeratorRestriction β δ σ hβ q hq a ∈
      GradedHilbert.vectorHomogeneousPiece
        (numeratorModule (β ∘ q.succAbove) (restrictedMultiplicity δ σ q) (σ ∘ q.succAbove)) e := by
  intro i
  have h := homogeneous_quotient_of_relation
    (coordinateProduct_homogeneous (F := F) (negativeNeighbours σ q))
    (coordinateProduct_ne_zero (F := F) (negativeNeighbours σ q))
    (removeCoordinate_homogeneous q (ha (q.succAbove i)))
    (restrictedNumerator_relation β δ σ hβ q hq a i)
    (Nat.le_add_left _ _)
  change (restrictedNumerator β δ σ hβ q hq a i).IsHomogeneous e
  simpa only [Nat.add_sub_cancel] using h

theorem numeratorRestriction_zero_of_degree_lt
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (hβ : ∀ i, β i ≠ 0) (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β δ σ) (e : ℕ)
    (ha : a ∈ GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ) e)
    (he : e < (negativeNeighbours σ q).card) :
    numeratorRestriction β δ σ hβ q hq a = 0 := by
  apply Subtype.ext
  funext i
  exact quotient_zero_of_homogeneous_relation_lt
    (coordinateProduct_homogeneous (F := F) (negativeNeighbours σ q))
    (coordinateProduct_ne_zero (F := F) (negativeNeighbours σ q))
    (removeCoordinate_homogeneous q (ha (q.succAbove i)))
    (restrictedNumerator_relation β δ σ hβ q hq a i) he

theorem deletionMultiplication_homogeneous
    (β : Fin (n + 1) → F) (δ : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → ℤ)
    (q : Fin (n + 1)) (hq : 0 < δ q)
    (a : numeratorModule β (deletedMultiplicity δ q) σ) (e : ℕ)
    (ha : a ∈ GradedHilbert.vectorHomogeneousPiece
      (numeratorModule β (deletedMultiplicity δ q) σ) e) :
    deletionMultiplication β δ σ q hq a ∈
      GradedHilbert.vectorHomogeneousPiece (numeratorModule β δ σ) (e + 1) := by
  intro i
  change (X q * a.val i).IsHomogeneous (e + 1)
  simpa only [Nat.add_comm] using (isHomogeneous_X F q).mul (ha i)

end PaperVerification.Fermion.Newton
