module
public import Papers.GaleRankIdentity
public import Papers.RationalityTenSupportBasics
public import Mathlib.LinearAlgebra.StdBasis
@[expose] public section
noncomputable section
open Matrix Module Set
open scoped BigOperators
namespace Papers.RationalityTen.ChirotopeDensity

theorem range_restricted_family {ι W : Type*} (p : ι → W) (S : Set ι) :
    Set.range (fun i : S => p i) = p '' S := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,i.2,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

theorem range_finset_family {ι W : Type*} (p : ι → W) (S : Finset ι) :
    Set.range (fun i : S => p i.val)=p '' (↑S : Set ι) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩

theorem range_eq_span_standard_columns {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module ℝ W] (L : (ι → ℝ) →ₗ[ℝ] W) :
    L.range = Submodule.span ℝ (Set.range (fun i => L (Pi.single i 1))) := by
  rw [LinearMap.range_eq_map,← (Pi.basisFun ℝ ι).span_eq,
    Submodule.map_span,← Set.range_comp]
  congr 1
  congr 1
  funext i
  exact congrArg L (Pi.basisFun_apply ℝ ι i)

theorem insideInjection_single {n : ℕ} (S : Finset (Fin n)) (i : S) :
    insideInjection (K := ℝ) S (Pi.single i 1) = Pi.single i.1 1 := by
  classical
  ext j
  by_cases hj : j∈S
  · simp [insideInjection,hj,Pi.single_apply,Subtype.ext_iff]
  · have hji : j ≠ i.1 := by
      intro h
      apply hj
      simpa only [h] using i.2
    simp [insideInjection,hj,Pi.single_apply,hji]

theorem restricted_columns_range {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (S : Finset (Fin n)) :
    (A.mulVecLin.comp (insideInjection (K := ℝ) S)).range =
      Submodule.span ℝ (A.col '' (↑S : Set (Fin n))) := by
  classical
  rw [range_eq_span_standard_columns]
  have hfun : (fun i : S =>
      (A.mulVecLin.comp (insideInjection (K := ℝ) S)) (Pi.single i 1)) =
      (fun i : S => A.col i.1) := by
    funext i
    change A.mulVec (insideInjection (K := ℝ) S (Pi.single i 1)) = _
    rw [insideInjection_single,Matrix.mulVec_single_one]
  rw [hfun,range_finset_family]


end Papers.RationalityTen.ChirotopeDensity
