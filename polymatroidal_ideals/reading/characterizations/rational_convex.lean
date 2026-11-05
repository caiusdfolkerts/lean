import Characterizations.RealHull
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Rational coefficients for rational points in finite real convex hulls -/

noncomputable section
namespace Characterizations
universe u
open CommAlg.Polymatroid Finset Matrix
open scoped BigOperators

theorem rational_solution_of_injective_matrix
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix J I ℚ) (hinj : Function.Injective A.mulVec)
    (b : J → ℚ) (y : I → ℝ)
    (hy : A.map (Rat.castHom ℝ) *ᵥ y = fun j => (b j : ℝ)) :
    ∃ x : I → ℚ, ∀ i, (x i : ℝ) = y i := by
  have hker : LinearMap.ker A.toLin' = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨L, hL⟩ := A.toLin'.exists_leftInverse_of_injective hker
  let M := LinearMap.toMatrix' L
  have hMA : M * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hL
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id, M] using h
  have hreal : M.map (Rat.castHom ℝ) * A.map (Rat.castHom ℝ) = 1 := by
    rw [← Matrix.map_mul, hMA]
    exact Matrix.map_one _ (by simp) (by simp)
  refine ⟨M *ᵥ b, ?_⟩
  intro i
  change (Rat.castHom ℝ) ((M *ᵥ b) i) = y i
  rw [RingHom.map_mulVec (Rat.castHom ℝ)]
  change (M.map (Rat.castHom ℝ) *ᵥ (fun j => (b j : ℝ))) i = y i
  rw [← hy, Matrix.mulVec_mulVec, hreal, Matrix.one_mulVec]

variable {V : Type u} {I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def affineMatrix (p : I → V → ℚ) : Matrix (Option V) I ℚ :=
  fun j i => j.elim 1 (p i)

theorem affineMatrix_injective (p : I → V → ℚ)
    (hp : AffineIndependent ℝ (fun i v => (p i v : ℝ))) :
    Function.Injective (affineMatrix p).mulVec := by
  intro x y hxy
  let w : I → ℝ := fun i => (x i : ℝ) - y i
  have hs : ∑ i, w i = 0 := by
    have h := congrFun hxy none
    simp only [Matrix.mulVec, dotProduct, affineMatrix, Option.elim_none, one_mul] at h
    have hr : (∑ i, (x i : ℝ)) = ∑ i, (y i : ℝ) := by exact_mod_cast h
    simpa only [w, sum_sub_distrib, sub_eq_zero] using hr
  have hv : ∑ i, w i • (fun v => (p i v : ℝ)) = (0 : V → ℝ) := by
    funext v
    have h := congrFun hxy (some v)
    simp only [Matrix.mulVec, dotProduct, affineMatrix, Option.elim_some] at h
    have hr : (∑ i, (p i v : ℝ) * x i) = ∑ i, (p i v : ℝ) * y i := by exact_mod_cast h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      w, sub_mul, sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using hr
  have hzero := (affineIndependent_iff_of_fintype ℝ _).mp hp w hs (by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w _ hs 0,
      Finset.weightedVSubOfPoint_apply]
    simpa only [vsub_eq_sub, sub_zero] using hv)
  funext i
  have h := hzero i
  change (x i : ℝ) - y i = 0 at h
  exact_mod_cast sub_eq_zero.mp h

/-- Real barycentric coordinates on a rational affine-independent family are
rational whenever the represented point is rational. -/
theorem rational_barycentric_weights (p : I → V → ℚ) (b : V → ℚ)
    (hp : AffineIndependent ℝ (fun i v => (p i v : ℝ))) (w : I → ℝ)
    (hs : ∑ i, w i = 1) (hb : ∀ v, ∑ i, w i * (p i v : ℝ) = b v) :
    ∃ q : I → ℚ, ∀ i, (q i : ℝ) = w i := by
  apply rational_solution_of_injective_matrix (affineMatrix p) (affineMatrix_injective p hp)
    (fun j : Option V => j.elim 1 b) w
  funext j
  cases j with
  | none => simpa [Matrix.mulVec, dotProduct, affineMatrix] using hs
  | some v => simpa [Matrix.mulVec, dotProduct, affineMatrix, mul_comm] using hb v

/-- Every integral point in the real convex hull of a finite integral family
has a finite rational convex combination of actual members of that family. -/
theorem rational_combination_of_mem_convexHull (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    ∃ (J : Type u) (_ : Fintype J) (p : J → Exponent V) (q : J → ℚ),
      (∀ j, p j ∈ B) ∧ (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧
        ∀ v, ∑ j, q j * (p j v : ℚ) = a v := by
  classical
  let T := Caratheodory.minCardFinsetOfMemConvexHull ha
  have hTsub := Caratheodory.minCardFinsetOfMemConvexHull_subseteq ha
  have hTI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull ha
  have hTa := Caratheodory.mem_minCardFinsetOfMemConvexHull ha
  change AffineIndependent ℝ (fun j : T => j.val) at hTI
  change realExponent a ∈ convexHull ℝ (T : Set (V → ℝ)) at hTa
  have hpre : ∀ j : T, ∃ b ∈ B, realExponent b = j.val := by
    intro j
    exact hTsub j.property
  choose p hp hpeq using hpre
  rw [Finset.convexHull_eq] at hTa
  obtain ⟨w, hw, hsum, hcomb⟩ := hTa
  let α : T → ℝ := fun j => w j.val
  have hsum' : ∑ j : T, α j = 1 := by
    simpa only [α, Finset.sum_coe_sort] using hsum
  have hpI : AffineIndependent ℝ (fun j : T => fun v => ((p j v : ℚ) : ℝ)) := by
    have he : (fun j : T => fun v => ((p j v : ℚ) : ℝ)) = fun j : T => j.val := by
      funext j v
      simpa [realExponent] using congrFun (hpeq j) v
    rw [he]
    exact hTI
  have hcomb' : ∀ v, ∑ j : T, α j * ((p j v : ℚ) : ℝ) = ((a v : ℚ) : ℝ) := by
    intro v
    have hh := congrFun hcomb v
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum] at hh
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id_eq, realExponent] at hh
    have he : (∑ j : T, α j * ((p j v : ℚ) : ℝ)) = ∑ z ∈ T, w z * z v := by
      calc
        _ = ∑ j : T, w j.val * j.val v := by
          apply Finset.sum_congr rfl
          intro j _
          have hj := congrFun (hpeq j) v
          simp only [realExponent] at hj
          simpa [α] using congrArg (fun r : ℝ => w j.val * r) hj
        _ = _ := Finset.sum_coe_sort T (fun z => w z * z v)
    rw [he]
    simpa using hh
  obtain ⟨q, hq⟩ := rational_barycentric_weights
    (fun j : T => fun v => (p j v : ℚ)) (fun v => (a v : ℚ)) hpI α hsum' hcomb'
  refine ⟨↥T, inferInstance, p, q, hp, ?_, ?_, ?_⟩
  · intro j
    have h : 0 ≤ (q j : ℝ) := by rw [hq]; exact hw j.val j.property
    exact_mod_cast h
  · have h : (∑ j, (q j : ℝ)) = 1 := by simpa only [hq] using hsum'
    exact_mod_cast h
  · intro v
    have h : (∑ j, (q j : ℝ) * ((p j v : ℚ) : ℝ)) = ((a v : ℚ) : ℝ) := by
      simpa only [hq] using hcomb' v
    exact_mod_cast h

end Characterizations
