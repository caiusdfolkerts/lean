module

public import ToricPower.KernelOrthant

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

theorem primitive_circuit_of_orthant_extreme
    (A : Matrix (Fin s) (Fin n) ℤ) (sign : Fin s → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    {q : Fin s → ℝ} (hq : q ∈ (orthantKernel A sign).extremePoints ℝ) :
    ∃ h : Fin s → ℤ, IsCircuit A h ∧
      ∃ c : ℝ, 0 < c ∧ q = c • (fun i => (h i : ℝ)) := by
  obtain ⟨D, z, hD, hz⟩ := orthant_extreme_integral_multiple A sign hq
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hqdata := (mem_orthantKernel_iff A sign q).mp hq.1
  have hqne : q ≠ 0 := by
    intro hqzero
    have hn := hqdata.2.2
    simp [hqzero] at hn
  have hz0 : z ≠ 0 := by
    intro hz0
    have hsc : (D : ℝ) • q = 0 := by
      rw [← hz, hz0]
      ext i
      simp
    exact hqne ((smul_eq_zero.mp hsc).resolve_left hDr.ne')
  obtain ⟨d, h, hd, hprim, hzh⟩ := TauCeti.exists_eq_zsmul_isPrimitive hz0
  let c : ℝ := (d : ℝ) / (D : ℝ)
  have hc : 0 < c := div_pos (by exact_mod_cast hd) hDr
  have hqeq : q = c • (fun i => (h i : ℝ)) := by
    ext i
    have hzi := congrFun hz i
    rw [hzh] at hzi
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul] at hzi
    change q i = c * (h i : ℝ)
    dsimp [c]
    apply (mul_right_cancel₀ hDr.ne')
    calc
      q i * (D : ℝ) = (d : ℝ) * (h i : ℝ) := by nlinarith [hzi]
      _ = ((d : ℝ) / (D : ℝ) * (h i : ℝ)) * (D : ℝ) := by
        field_simp
  have hker : h ∈ rayRelations A := by
    rw [mem_rayRelations]
    intro j
    have hh := hqdata.1 j
    rw [hqeq] at hh
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    have heq : (∑ i, (A i j : ℝ) * (c * (h i : ℝ))) =
        c * ∑ i, (A i j : ℝ) * (h i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq] at hh
    have hh0 := (mul_eq_zero.mp hh).resolve_left hc.ne'
    exact_mod_cast hh0
  refine ⟨h, ⟨hprim, hker, ?_⟩, c, hc, hqeq⟩
  intro k hk hs
  by_contra hk0
  let kr : Fin s → ℝ := fun i => (k i : ℝ)
  have hkr : ∀ j, ∑ i, (A i j : ℝ) * kr i = 0 := by
    intro j
    dsimp [kr]
    exact_mod_cast ((mem_rayRelations A k).mp hk j)
  have hks : Function.support kr ⊆ Function.support q := by
    intro i hi
    change (k i : ℝ) ≠ 0 at hi
    have hki : k i ≠ 0 := by exact_mod_cast hi
    have hhi : h i ≠ 0 := hs.subset hki
    rw [Function.mem_support, hqeq]
    change c * (h i : ℝ) ≠ 0
    exact mul_ne_zero hc.ne' (by exact_mod_cast hhi)
  have heq := orthant_extreme_supported_relation A sign hsign hq kr hkr hks
  let l : ℝ := ∑ i, (sign i : ℝ) * kr i
  have hl : l ≠ 0 := by
    intro hl0
    have hkreal : kr = 0 := by
      change kr = l • q at heq
      simpa only [hl0, zero_smul] using heq
    apply hk0
    ext i
    have hi := congrFun hkreal i
    change (k i : ℝ) = 0 at hi
    change k i = 0
    exact_mod_cast hi
  have hback : Function.support h ⊆ Function.support k := by
    intro i hi hki
    change h i ≠ 0 at hi
    have hqi : q i ≠ 0 := by
      rw [hqeq]
      change c * (h i : ℝ) ≠ 0
      exact mul_ne_zero hc.ne' (by exact_mod_cast hi)
    have hei := congrFun heq i
    change (k i : ℝ) = l * q i at hei
    have hz : l * q i = 0 := by simpa only [hki, Int.cast_zero] using hei.symm
    exact (mul_ne_zero hl hqi) hz
  exact hs.not_subset hback

end ToricPower

