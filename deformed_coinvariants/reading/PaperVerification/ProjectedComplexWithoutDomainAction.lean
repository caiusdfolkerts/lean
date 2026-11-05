module

public import PaperVerification.ProjectedRankSpecialization

/-!
# Projecting a complex without an action on its relation generators

The first differential intertwines the two actual projections.  The second
differential need not intertwine any prescribed action: projecting its image
and adding the complement of the middle projection gives an actual complex,
exact at every fiber where the original complex is exact.  This is useful for
ordered-pair presentations of Lie--Rinehart syzygies, whose chosen generators
need not form a natural group representation.

This source is supporting mathematics and has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.ProjectedComplex

open Matrix

variable {R : Type*} [CommRing R]
variable {u v w : Type*} [Fintype u] [Fintype v] [Fintype w]
local instance : DecidableEq v := Classical.decEq v

/-- The actual second matrix, including the full complementary summand. -/
def augmentedSecond (G : Matrix v u R) (P : Matrix v v R) :
    Matrix v (u ⊕ v) R := Matrix.fromCols (P * G) (1-P)

theorem complex (F : Matrix w v R) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix w w R)
    (hFG : F * G = 0) (hP : P * P = P) (hFP : F * P = Q * F) :
    (F * P) * augmentedSecond G P = 0 := by
  have hleft : (F * P) * (P * G) = 0 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc F P P, hP, hFP,
      Matrix.mul_assoc, hFG, Matrix.mul_zero]
  have hright : (F * P) * (1-P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hP, sub_self]
  rw [augmentedSecond, Matrix.mul_fromCols, hleft, hright]
  ext i j
  cases j <;> rfl

/-- The full exactness statement, not just one inclusion of relation spaces. -/
theorem augmented_exact (F : Matrix w v R) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix w w R)
    (hFG : F * G = 0) (hP : P * P = P) (hFP : F * P = Q * F)
    (he : LinearMap.range G.mulVecLin = LinearMap.ker F.mulVecLin) :
    LinearMap.range (augmentedSecond G P).mulVecLin =
      LinearMap.ker (F * P).mulVecLin := by
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.mulVecLin_mul, complex F G P Q hFG hP hFP,
      Matrix.mulVecLin_zero]
  · intro x hx
    have hPx : P *ᵥ x ∈ LinearMap.ker F.mulVecLin := by
      change F *ᵥ (P *ᵥ x) = 0
      rw [Matrix.mulVec_mulVec]
      exact hx
    obtain ⟨y,hy⟩ := he.ge hPx
    change G *ᵥ y = P *ᵥ x at hy
    refine ⟨Sum.elim y x,?_⟩
    change Matrix.fromCols (P * G) (1-P) *ᵥ Sum.elim y x = x
    rw [Matrix.fromCols_mulVec_sumElim,←Matrix.mulVec_mulVec,hy,
      Matrix.mulVec_mulVec,hP,Matrix.sub_mulVec,Matrix.one_mulVec]
    abel

theorem map_augmentedSecond {S : Type*} [CommRing S]
    (φ : R →+* S) (G : Matrix v u R) (P : Matrix v v R) :
    (augmentedSecond G P).map φ = augmentedSecond (G.map φ) (P.map φ) := by
  ext i j
  cases j with
  | inl j =>
      simp only [augmentedSecond,Matrix.map_apply,Matrix.fromCols_apply_inl,
        ←Matrix.map_mul]
  | inr j =>
      simp only [augmentedSecond,Matrix.map_apply,Matrix.fromCols_apply_inr,
        Matrix.sub_apply,Matrix.one_apply,map_sub]
      split_ifs <;> simp only [map_one,map_zero]

section Specialization

variable [IsDomain R] {K K₀ : Type*} [Field K] [Field K₀]

/-- Every specialization has projected first rank at most that of an exact
fiber. Only the first map needs compatibility with the two projections. -/
theorem rank_le_at_exact_fiber
    (F : Matrix w v R) (G : Matrix v u R)
    (P : Matrix v v R) (Q : Matrix w w R)
    (hFG : F * G = 0) (hP : P * P = P) (hFP : F * P = Q * F)
    (φ₀ : R →+* K₀) (φ : R →+* K)
    (he : LinearMap.range (G.map φ₀).mulVecLin =
      LinearMap.ker (F.map φ₀).mulVecLin) :
    ((F * P).map φ).rank ≤ ((F * P).map φ₀).rank := by
  have hFG₀ : F.map φ₀ * G.map φ₀ = 0 := by
    rw [←Matrix.map_mul,hFG]
    ext i j
    exact map_zero φ₀
  have hP₀ : P.map φ₀ * P.map φ₀ = P.map φ₀ := by
    rw [←Matrix.map_mul,hP]
  have hFP₀ : F.map φ₀ * P.map φ₀ = Q.map φ₀ * F.map φ₀ := by
    rw [←Matrix.map_mul,←Matrix.map_mul,hFP]
  have hexact : LinearMap.range ((augmentedSecond G P).map φ₀).mulVecLin =
      LinearMap.ker ((F * P).map φ₀).mulVecLin := by
    rw [map_augmentedSecond,Matrix.map_mul]
    exact augmented_exact _ _ _ _ hFG₀ hP₀ hFP₀ he
  exact RankSpecialization.rank_le_at_exact_fiber_of_distinct_fields
    (F*P) (augmentedSecond G P) (complex F G P Q hFG hP hFP) φ₀ φ hexact

end Specialization
end PaperVerification.ProjectedComplex
