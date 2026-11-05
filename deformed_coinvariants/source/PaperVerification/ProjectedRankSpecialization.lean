module

public import PaperVerification.RankSpecialization
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Tactic.Abel

/-!
# Rank specialization after an actual projection

Given a complex `F G = 0` and compatible projections, replace its first map
by `F P` and its second map by `[G Q, 1-P]`. The extra summand is essential:
it removes the complement of the projected middle space. Exactness at the
specified fiber is proved directly. Applied to Reynolds projections on full
linear-map spaces, this gives the multiplicity-space version of Lemma2.1
without assuming bases or scalar-extension identities for invariant spaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix

namespace PaperVerification.ProjectedRankSpecialization

variable {R : Type*} [CommRing R]
variable {u v w : Type*} [Fintype u] [Fintype v] [Fintype w]
local instance : DecidableEq u := Classical.decEq u
local instance : DecidableEq v := Classical.decEq v

def augmentedSecond (G : Matrix v u R) (P : Matrix v v R) (Q : Matrix u u R) :
    Matrix v (u ⊕ v) R :=
  Matrix.fromCols (G * Q) (1-P)

/-- The augmentation is an actual complex over the parameter ring. -/
theorem augmented_complex (F : Matrix w v R) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix u u R)
    (hFG : F * G = 0) (hP : P * P = P) (hPG : P * G = G * Q) :
    (F * P) * augmentedSecond G P Q = 0 := by
  have hleft : (F * P) * (G * Q) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P G Q, hPG,
      Matrix.mul_assoc G Q Q, ← Matrix.mul_assoc F G (Q * Q), hFG, Matrix.zero_mul]
  have hright : (F * P) * (1-P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hP, sub_self]
  rw [augmentedSecond, Matrix.mul_fromCols, hleft, hright]
  ext i j
  cases j <;> rfl

/-- Exactness of the full complex at a fiber implies exactness of the
augmented projected complex at that same fiber. -/
theorem augmented_exact (F : Matrix w v R) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix u u R)
    (hFG : F * G = 0) (hP : P * P = P) (hPG : P * G = G * Q)
    (hexact : LinearMap.range G.mulVecLin = LinearMap.ker F.mulVecLin) :
    LinearMap.range (augmentedSecond G P Q).mulVecLin =
      LinearMap.ker (F * P).mulVecLin := by
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul, augmented_complex F G P Q hFG hP hPG,
      Matrix.mulVecLin_zero]
  · intro x hx
    have hPx : P *ᵥ x ∈ LinearMap.ker F.mulVecLin := by
      change F *ᵥ (P *ᵥ x) = 0
      rw [Matrix.mulVec_mulVec]
      exact hx
    obtain ⟨y, hy⟩ := hexact.ge hPx
    change G *ᵥ y = P *ᵥ x at hy
    refine ⟨Sum.elim y x, ?_⟩
    change Matrix.fromCols (G * Q) (1-P) *ᵥ Sum.elim y x = x
    rw [Matrix.fromCols_mulVec_sumElim, ← hPG, ← Matrix.mulVec_mulVec, hy,
      Matrix.mulVec_mulVec, hP, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel

section Specialization

variable [IsDomain R] {K K₀ : Type*} [Field K] [Field K₀]

theorem map_augmentedSecond (φ : R →+* K) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix u u R) :
    (augmentedSecond G P Q).map φ =
      augmentedSecond (G.map φ) (P.map φ) (Q.map φ) := by
  ext i j
  cases j with
  | inl j => simp only [augmentedSecond, Matrix.map_apply, Matrix.fromCols_apply_inl,
      ← Matrix.map_mul]
  | inr j => simp only [augmentedSecond, Matrix.map_apply, Matrix.fromCols_apply_inr,
      Matrix.sub_apply, Matrix.one_apply, map_sub]
             split_ifs <;> simp only [map_one, map_zero]

/-- The rank comparison for the projected family, with exactness only in
the original good fiber. Idempotence and compatibility are identities over
the parameter ring, and the augmentation is constructed explicitly. -/
theorem rank_le_at_exact_fiber
    (F : Matrix w v R) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix u u R)
    (hFG : F * G = 0) (hP : P * P = P) (hPG : P * G = G * Q)
    (φ₀ : R →+* K₀) (φ : R →+* K)
    (hexact : LinearMap.range (G.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin) :
    ((F * P).map φ).rank ≤ ((F * P).map φ₀).rank := by
  have hFG₀ : F.map φ₀ * G.map φ₀ = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    exact map_zero φ₀
  have hP₀ : P.map φ₀ * P.map φ₀ = P.map φ₀ := by
    rw [← Matrix.map_mul, hP]
  have hPG₀ : P.map φ₀ * G.map φ₀ = G.map φ₀ * Q.map φ₀ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPG]
  have he : LinearMap.range ((augmentedSecond G P Q).map φ₀).mulVecLin =
      LinearMap.ker ((F * P).map φ₀).mulVecLin := by
    rw [map_augmentedSecond, Matrix.map_mul]
    exact augmented_exact _ _ _ _ hFG₀ hP₀ hPG₀ hexact
  exact RankSpecialization.rank_le_at_exact_fiber_of_distinct_fields
    (F * P) (augmentedSecond G P Q) (augmented_complex F G P Q hFG hP hPG) φ₀ φ he

end Specialization

end PaperVerification.ProjectedRankSpecialization
