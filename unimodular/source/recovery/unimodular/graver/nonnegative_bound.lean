module

public import Recovery.Unimodular.Graver.KernelSlice
public import Mathlib.Data.Fintype.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology Matrix
open Set

namespace Unimodular.EffectiveGraver
open RationalVertices KernelSlice

variable {n m : ℕ}

/-- The actual integer matrix map. -/
def matrixHom (A : Matrix (Fin m) (Fin n) ℤ) : (Fin n → ℤ) →+ (Fin m → ℤ) :=
  (Matrix.mulVecLin A).toAddMonoidHom

@[simp] theorem matrixHom_apply (A : Matrix (Fin m) (Fin n) ℤ) (g : Fin n → ℤ) :
    matrixHom A g = A *ᵥ g := rfl

noncomputable section

theorem ratEmbed_injective : Function.Injective (ratEmbed : (Fin n → ℚ) → Ambient n) := by
  intro q r h
  ext j
  have hj : (q j : ℝ) = (r j : ℝ) := congrFun h j
  exact_mod_cast hj

/-- The sum of the computably enumerated vertex denominators bounds every
nonnegative primitive kernel vector. No rank or coefficient restriction occurs. -/
theorem nonnegative_primitive_bound (A : Matrix (Fin m) (Fin n) ℤ)
    {g : Lattice n} (hg : Graver.Primitive (matrixHom A).ker g)
    (hgn : ∀ j, 0 ≤ g j) : (∑ j, g j) ≤ (KernelSlice.bound A : ℤ) := by
  classical
  let S : ℝ := ∑ j, (g j : ℝ)
  have hS : 0 < S := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hg.2.1
    have hjp : 0 < g j := lt_of_le_of_ne (hgn j) (by simpa using Ne.symm hj)
    exact Finset.sum_pos' (fun k _ => by exact_mod_cast hgn k)
      ⟨j, Finset.mem_univ _, by exact_mod_cast hjp⟩
  have hAg : (A.map (fun z => (z : ℝ))) *ᵥ embed g = 0 := by
    ext i
    have hi := congrFun hg.1 i
    change (∑ j, A i j * g j) = 0 at hi
    change (∑ j, (A i j : ℝ) * (g j : ℝ)) = 0
    exact_mod_cast hi
  let x : Ambient n := S⁻¹ • embed g
  have hx : x ∈ slice A := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      change 0 ≤ S⁻¹ * (g j : ℝ)
      exact mul_nonneg (inv_nonneg.2 hS.le) (by exact_mod_cast hgn j)
    · change (A.map (fun z => (z : ℝ))) *ᵥ (S⁻¹ • embed g) = 0
      rw [Matrix.mulVec_smul, hAg, smul_zero]
    · change (∑ j, S⁻¹ * (g j : ℝ)) = 1
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hS.ne'
  have hxj (j : Fin n) : S * x j = (g j : ℝ) := by
    change S * (S⁻¹ * (g j : ℝ)) = (g j : ℝ)
    rw [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul]
  let V : Finset (Ambient n) := (KernelSlice.vertices A).image ratEmbed
  have hvset : (V : Set (Ambient n)) = ratEmbed '' (KernelSlice.vertices A : Set (Fin n → ℚ)) :=
    Finset.coe_image
  have hxconv : x ∈ convexHull ℝ (V : Set (Ambient n)) := by
    rw [hvset, ← slice_eq_convexHull]
    exact hx
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hxconv
  have hqV {q : Fin n → ℚ} (hq : q ∈ KernelSlice.vertices A) : ratEmbed q ∈ V :=
    Finset.mem_image.2 ⟨q, hq, rfl⟩
  have hw0' {q : Fin n → ℚ} (hq : q ∈ KernelSlice.vertices A) : 0 ≤ w (ratEmbed q) :=
    hw0 _ (hqV hq)
  have hweights : (∑ q ∈ KernelSlice.vertices A, w (ratEmbed q)) = 1 := by
    have h := hw1
    change (∑ y ∈ (KernelSlice.vertices A).image ratEmbed, w y) = 1 at h
    rw [Finset.sum_image] at h
    · exact h
    · intro q hq r hr he
      exact ratEmbed_injective he
  have hvalue (j : Fin n) :
      (∑ q ∈ KernelSlice.vertices A, w (ratEmbed q) * (q j : ℝ)) = x j := by
    have h := congrFun hwx j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    change (∑ y ∈ (KernelSlice.vertices A).image ratEmbed, w y * y j) = x j at h
    rw [Finset.sum_image] at h
    · exact h
    · intro q hq r hr he
      exact ratEmbed_injective he
  have hbound : S ≤ (KernelSlice.bound A : ℝ) := by
    by_contra hnot
    have hbig : (KernelSlice.bound A : ℝ) < S := lt_of_not_ge hnot
    have hex : ∃ q ∈ KernelSlice.vertices A,
        (denominator q : ℝ) ≤ S * w (ratEmbed q) := by
      by_contra! hsmall
      have hh : (∑ q ∈ KernelSlice.vertices A, S * w (ratEmbed q)) ≤
          ∑ q ∈ KernelSlice.vertices A, (denominator q : ℝ) :=
        Finset.sum_le_sum fun q hq => (hsmall q hq).le
      rw [← Finset.mul_sum, hweights, mul_one] at hh
      have hb : (∑ q ∈ KernelSlice.vertices A, (denominator q : ℝ)) =
          (KernelSlice.bound A : ℝ) := by simp only [KernelSlice.bound, Nat.cast_sum]
      rw [hb] at hh
      exact (not_le_of_gt hbig) hh
    obtain ⟨q, hq, hcoeff⟩ := hex
    have hle : ∀ j, cleared q j ≤ g j := by
      intro j
      have hqnonneg := (vertex_mem_slice A hq).1 j
      have hterm : w (ratEmbed q) * (q j : ℝ) ≤ x j := by
        rw [← hvalue]
        exact Finset.single_le_sum (fun r hr =>
          mul_nonneg (hw0' hr) ((vertex_mem_slice A hr).1 j)) hq
      have hreal : (cleared q j : ℝ) ≤ (g j : ℝ) := by
        calc
          (cleared q j : ℝ) = (denominator q : ℝ) * (q j : ℝ) :=
            congrFun (embed_cleared q) j
          _ ≤ (S * w (ratEmbed q)) * (q j : ℝ) :=
            mul_le_mul_of_nonneg_right hcoeff hqnonneg
          _ = S * (w (ratEmbed q) * (q j : ℝ)) := mul_assoc _ _ _
          _ ≤ S * x j := mul_le_mul_of_nonneg_left hterm hS.le
          _ = (g j : ℝ) := hxj j
      exact_mod_cast hreal
    have hconf : Graver.ConformalLE (cleared q) g :=
      (Graver.conformalLE_iff _ _).2 fun j => Or.inl ⟨cleared_nonnegative A hq j, hle j⟩
    have heq : cleared q = g := hg.2.2 _ (cleared_in_kernel A hq)
      (cleared_ne_zero A hq) hconf
    have hsum : S = (denominator q : ℝ) := by
      have h := cleared_sum A hq
      rw [heq] at h
      dsimp [S]
      exact_mod_cast h
    have hdle : denominator q ≤ KernelSlice.bound A :=
      Finset.single_le_sum (fun r hr => Nat.zero_le _) hq
    have hdleR : (denominator q : ℝ) ≤ (KernelSlice.bound A : ℝ) := by exact_mod_cast hdle
    rw [hsum] at hbig
    exact (not_le_of_gt hbig) hdleR
  have hcast : ((∑ j, g j : ℤ) : ℝ) ≤ ((KernelSlice.bound A : ℤ) : ℝ) := by
    simpa only [Int.cast_sum, Int.cast_natCast] using hbound
  exact_mod_cast hcast

end
end Unimodular.EffectiveGraver

#print axioms Unimodular.EffectiveGraver.nonnegative_primitive_bound
#check Unimodular.EffectiveGraver.nonnegative_primitive_bound
