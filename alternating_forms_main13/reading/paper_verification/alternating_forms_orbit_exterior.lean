module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Basis.Prod
public import TauCeti.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Exterior relation matrices and invariance under a change of basis

The relation map is the actual map (x,y) ↦ f ∧ x + g ∧ y between exterior powers.
Its coefficient matrix is polynomial in the coordinates of f and g. An invertible
linear change of variables gives isomorphic relation spaces, hence preserves their ranks.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.AlternatingForms

open Module MvPolynomial

variable {K M N : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- An invertible linear map induces an equivalence on each actual exterior power. -/
def orbitExteriorPowerEquiv (e : M ≃ₗ[K] N) (q : ℕ) :
    (⋀[K]^q M) ≃ₗ[K] (⋀[K]^q N) :=
  LinearEquiv.ofBijective (exteriorPower.map q e.toLinearMap)
    ⟨exteriorPower.map_injective_field (n := q) e.injective,
      exteriorPower.map_surjective (n := q) e.surjective⟩

@[simp]
theorem orbitExteriorPowerEquiv_apply (e : M ≃ₗ[K] N) (q : ℕ) (x : ⋀[K]^q M) :
    orbitExteriorPowerEquiv e q x = exteriorPower.map q e.toLinearMap x := rfl

/-- Naturality of the actual exterior multiplication. -/
theorem orbitExteriorPower_map_wedge (e : M ≃ₗ[K] N) (a b : ℕ)
    (x : ⋀[K]^a M) (y : ⋀[K]^b M) :
    exteriorPower.map (a + b) e.toLinearMap (exteriorPower.wedge K M a b x y) =
      exteriorPower.wedge K N a b
        (exteriorPower.map a e.toLinearMap x) (exteriorPower.map b e.toLinearMap y) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, map_mul]

/-- The two-form relation map into degree 2+q. -/
def orbitExteriorRelationMap (f g : ⋀[K]^2 M) (q : ℕ) :
    ((⋀[K]^q M) × (⋀[K]^q M)) →ₗ[K] (⋀[K]^(2 + q) M) :=
  (exteriorPower.wedge K M 2 q f).coprod (exteriorPower.wedge K M 2 q g)

theorem orbitExteriorRelationMap_natural (e : M ≃ₗ[K] N)
    (f g : ⋀[K]^2 M) (q : ℕ) (x y : ⋀[K]^q M) :
    orbitExteriorPowerEquiv e (2 + q) (orbitExteriorRelationMap f g q (x, y)) =
      orbitExteriorRelationMap (orbitExteriorPowerEquiv e 2 f)
        (orbitExteriorPowerEquiv e 2 g) q
        (orbitExteriorPowerEquiv e q x, orbitExteriorPowerEquiv e q y) := by
  simp only [orbitExteriorRelationMap, LinearMap.coprod_apply, map_add,
    orbitExteriorPowerEquiv_apply, orbitExteriorPower_map_wedge]

theorem orbitExteriorRelationMap_intertwines (e : M ≃ₗ[K] N)
    (f g : ⋀[K]^2 M) (q : ℕ) :
    (orbitExteriorPowerEquiv e (2 + q)).toLinearMap.comp (orbitExteriorRelationMap f g q) =
      (orbitExteriorRelationMap (orbitExteriorPowerEquiv e 2 f)
        (orbitExteriorPowerEquiv e 2 g) q).comp
        ((orbitExteriorPowerEquiv e q).prodCongr (orbitExteriorPowerEquiv e q)).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  exact orbitExteriorRelationMap_natural e f g q x y

theorem orbitExteriorRelationRange_map (e : M ≃ₗ[K] N)
    (f g : ⋀[K]^2 M) (q : ℕ) :
    (orbitExteriorRelationMap f g q).range.map
        (orbitExteriorPowerEquiv e (2 + q)).toLinearMap =
      (orbitExteriorRelationMap (orbitExteriorPowerEquiv e 2 f)
        (orbitExteriorPowerEquiv e 2 g) q).range := by
  have hsurj :
      ((orbitExteriorPowerEquiv e q).prodCongr
        (orbitExteriorPowerEquiv e q)).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr
      ((orbitExteriorPowerEquiv e q).prodCongr (orbitExteriorPowerEquiv e q)).surjective
  rw [← LinearMap.range_comp, orbitExteriorRelationMap_intertwines,
    LinearMap.range_comp, hsurj, Submodule.map_top]

/-- The actual spaces of exterior relations are equivalent under a change of basis. -/
def orbitExteriorRelationRangeEquiv (e : M ≃ₗ[K] N)
    (f g : ⋀[K]^2 M) (q : ℕ) :
    (orbitExteriorRelationMap f g q).range ≃ₗ[K]
      (orbitExteriorRelationMap (orbitExteriorPowerEquiv e 2 f)
        (orbitExteriorPowerEquiv e 2 g) q).range :=
  (orbitExteriorPowerEquiv e (2 + q)).ofSubmodules _ _
    (orbitExteriorRelationRange_map e f g q)

theorem orbitExteriorRelation_finrank_invariant (e : M ≃ₗ[K] N)
    (f g : ⋀[K]^2 M) (q : ℕ) :
    Module.finrank K (orbitExteriorRelationMap f g q).range =
      Module.finrank K (orbitExteriorRelationMap (orbitExteriorPowerEquiv e 2 f)
        (orbitExteriorPowerEquiv e 2 g) q).range :=
  (orbitExteriorRelationRangeEquiv e f g q).finrank_eq

section Coordinates

variable {I J B : Type*} [Fintype I] [Fintype J] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq B]
  (q : ℕ) (b₂ : Basis I K (⋀[K]^2 M))
  (bq : Basis J K (⋀[K]^q M)) (bout : Basis B K (⋀[K]^(2 + q) M))

/-- Two actual exterior two-forms with the specified coefficients. -/
def orbitFormsFromCoordinates (x : (I ⊕ I) → K) : (⋀[K]^2 M) × (⋀[K]^2 M) :=
  (∑ i, x (Sum.inl i) • b₂ i, ∑ i, x (Sum.inr i) • b₂ i)

/-- The actual exterior relation matrix, written as a polynomial in all two-form
coefficients. Its entries use the structure constants of exterior multiplication. -/
def orbitRelationPolynomialMatrix :
    Matrix B (J ⊕ J) (MvPolynomial (I ⊕ I) K) :=
  Matrix.of fun r c ↦ match c with
    | Sum.inl j =>
      ∑ i, C (bout.coord r (exteriorPower.wedge K M 2 q (b₂ i) (bq j))) * X (Sum.inl i)
    | Sum.inr j =>
      ∑ i, C (bout.coord r (exteriorPower.wedge K M 2 q (b₂ i) (bq j))) * X (Sum.inr i)

/-- Evaluation gives the matrix of multiplication by the two actual forms,
not a surrogate matrix with an expected rank built into its definition. -/
theorem orbitRelationPolynomialMatrix_eval (x : (I ⊕ I) → K) :
    (orbitRelationPolynomialMatrix q b₂ bq bout).map (eval x) =
      LinearMap.toMatrix (bq.prod bq) bout
        (orbitExteriorRelationMap (orbitFormsFromCoordinates b₂ x).1
          (orbitFormsFromCoordinates b₂ x).2 q) := by
  have hzero (z : ⋀[K]^2 M) :
      (GradedMonoid.GMul.mul (A := fun r : ℕ => ↥(⋀[K]^r M))
        z (0 : ⋀[K]^q M) : ⋀[K]^(2+q) M) = 0 := by
    apply Subtype.ext
    change (z : ExteriorAlgebra K M) * 0 = 0
    exact mul_zero _
  ext r c
  cases c with
  | inl j =>
    simp [orbitRelationPolynomialMatrix, orbitFormsFromCoordinates,
      LinearMap.toMatrix_apply, ← Basis.coord_apply, orbitExteriorRelationMap,
      Basis.prod_apply, LinearMap.coprod_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, map_sum, map_smul, mul_comm, hzero]
  | inr j =>
    simp [orbitRelationPolynomialMatrix, orbitFormsFromCoordinates,
      LinearMap.toMatrix_apply, ← Basis.coord_apply, orbitExteriorRelationMap,
      Basis.prod_apply, LinearMap.coprod_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, map_sum, map_smul, mul_comm, hzero]

theorem orbitRelationMatrix_rank_invariant (e : M ≃ₗ[K] M) (f g : ⋀[K]^2 M) :
    (LinearMap.toMatrix (bq.prod bq) bout (orbitExteriorRelationMap f g q)).rank =
      (LinearMap.toMatrix (bq.prod bq) bout
        (orbitExteriorRelationMap (orbitExteriorPowerEquiv e 2 f)
          (orbitExteriorPowerEquiv e 2 g) q)).rank := by
  rw [LinearMap.rank_toMatrix, LinearMap.rank_toMatrix]
  exact orbitExteriorRelation_finrank_invariant e f g q

end Coordinates

end PaperVerification.AlternatingForms
