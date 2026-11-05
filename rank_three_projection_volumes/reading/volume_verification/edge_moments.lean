module
public import VolumeVerification.CycleObstruction
public import VolumeVerification.ConeMeasureDecomposition
public import Mathlib.Tactic.FunProp
@[expose] public section
set_option autoImplicit false

/-!
# Endpoint moments in the polygonal measure decomposition

Every endpoint moment used in the cyclic rank contradiction is derived from
the original centered measures and their positive decomposition.  The only
geometric input here is the measure identity and the endpoint-zero pattern
of the actual cone rays.
-/
namespace VolumeVerification.EdgeMoments
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set
variable {n : ℕ}

def next (i : Fin n) : Fin n := finRotate n i
def prev (i : Fin n) : Fin n := (finRotate n).symm i

@[simp] theorem next_prev (i : Fin n) : next (prev i) = i := by
  exact (finRotate n).apply_symm_apply i

@[simp] theorem prev_next (i : Fin n) : prev (next i) = i := by
  exact (finRotate n).symm_apply_apply i

theorem next_ne (hn : 2 ≤ n) (i : Fin n) : next i ≠ i := by
  letI : NeZero n := i.neZero
  intro h
  have he : i + 1 = i + 0 := by simpa [next, finRotate_apply] using h
  have h1 : (1 : Fin n) = 0 := add_left_cancel he
  have hv := congrArg Fin.val h1
  change 1 % n = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
  omega

theorem prev_ne (hn : 2 ≤ n) (i : Fin n) : prev i ≠ i := by
  intro h
  have he := congrArg next h
  rw [next_prev] at he
  exact next_ne hn i he.symm

theorem prev_ne_next (hn : 3 ≤ n) (i : Fin n) : prev i ≠ next i := by
  letI : NeZero n := i.neZero
  intro h
  have he : i = next (next i) := by
    calc
      i = next (prev i) := (next_prev i).symm
      _ = next (next i) := congrArg next h
  simp only [next, finRotate_apply] at he
  have htwo : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    simp only [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have h2 : (2 : Fin n) = 0 := by
    apply add_left_cancel (a := i)
    calc
      i + 2 = (i + 1) + 1 := by
        rw [← htwo, add_assoc]
      _ = i := he.symm
      _ = i + 0 := by simp
  have hv := congrArg Fin.val h2
  change 2 % n = 0 at hv
  rw [Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
  omega

section Compact
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

theorem continuous_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C,hC⟩ := (isCompact_range hf.norm).bddAbove
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hC ⟨x,rfl⟩)

def coordinate (Z : Matrix (Fin n) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (i : Fin n) (x : Ω) : ℝ := (Z *ᵥ φ x) i

theorem coordinate_continuous (Z : Matrix (Fin n) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ) (i : Fin n) :
    Continuous (coordinate Z φ i) := by
  unfold coordinate
  fun_prop

theorem integral_matrix_row {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Matrix (Fin m) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ) (i : Fin m) :
    (∫ x, (A *ᵥ φ x) i ∂μ) = ∑ j, A i j * ∫ x, φ x j ∂μ := by
  have hj : ∀ j, Integrable (fun x => A i j * φ x j) μ := by
    intro j
    exact (continuous_integrable μ _ ((continuous_apply j).comp hφ)).const_mul _
  simp only [Matrix.mulVec, dotProduct]
  rw [integral_finsetSum Finset.univ (fun j _ => hj j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_const_mul _ _

theorem integral_coordinate (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (φ : Ω → Fin n → ℝ) (hφ : Continuous φ) (i : Fin n) :
    (∫ x, coordinate Z φ i x ∂μ) =
      ∑ j, Z i j * ∫ x, φ x j ∂μ := by
  exact integral_matrix_row μ Z φ hφ i

variable (μ : Fin n → Measure Ω) (ν : Fin n → Measure Ω)
  [∀ i, IsFiniteMeasure (μ i)] [∀ e, IsFiniteMeasure (ν e)]
  (r : Fin n → Fin n → ℝ)

def RayPattern : Prop :=
  (∀ e, r e e = 0) ∧
  (∀ e, r e (next e) = 0) ∧
  (∀ e i, i ≠ e → i ≠ next e → 0 < r e i)

theorem ray_nonnegative (hr : RayPattern r) : ∀ e i, 0 ≤ r e i := by
  intro e i
  by_cases hi : i = e
  · subst i; rw [hr.1]
  by_cases hin : i = next e
  · rw [hin, hr.2.1]
  exact (hr.2.2 e i hi hin).le

theorem transfer_ae (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (e i : Fin n) (hi : i ≠ e) (hin : i ≠ next e)
    {p : Ω → Prop} (hp : ∀ᵐ x ∂μ i, p x) :
    ∀ᵐ x ∂ν e, p x := by
  have hri := hr.2.2 e i hi hin
  have hle : ENNReal.ofReal (r e i) • ν e ≤ μ i := by
    rw [hdecomp]
    exact Finset.single_le_sum
      (f := fun j => ENNReal.ofReal (r j i) • ν j)
      (fun j _ => Measure.zero_le _) (Finset.mem_univ e)
  have hs : ∀ᵐ x ∂ENNReal.ofReal (r e i) • ν e, p x :=
    hp.filter_mono (ae_mono hle)
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hri).ne').mp hs

theorem integral_decomposition (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (g : Ω → ℝ) (hg : Continuous g) (i : Fin n) :
    (∫ x, g x ∂μ i) = ∑ e, r e i * ∫ x, g x ∂ν e := by
  rw [hdecomp]
  rw [integral_finsetSum_measure
    (fun e _ => (continuous_integrable (ν e) g hg).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (ray_nonnegative r hr e i)]
  rfl

theorem isolate_outgoing (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (i : Fin n) (g : Ω → ℝ) (hg : Continuous g)
    (hzero : ∀ e, i ≠ e → i ≠ next e → g =ᵐ[ν e] 0) :
    (∫ x, g x ∂μ (prev i)) = r i (prev i) * ∫ x, g x ∂ν i := by
  rw [integral_decomposition μ ν r hr hdecomp g hg]
  apply Finset.sum_eq_single i
  · intro e _ hei
    by_cases h : i = next e
    · have he : e = prev i := by rw [h, prev_next]
      subst e
      rw [hr.1, zero_mul]
    · rw [integral_eq_zero_of_ae (hzero e (Ne.symm hei) h), mul_zero]
  · simp

theorem isolate_incoming (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (i : Fin n) (g : Ω → ℝ) (hg : Continuous g)
    (hzero : ∀ e, i ≠ e → i ≠ next e → g =ᵐ[ν e] 0) :
    (∫ x, g x ∂μ (next i)) = r (prev i) (next i) * ∫ x, g x ∂ν (prev i) := by
  rw [integral_decomposition μ ν r hr hdecomp g hg]
  apply Finset.sum_eq_single (prev i)
  · intro e _ hei
    by_cases he : i = e
    · subst e
      rw [hr.2.1, zero_mul]
    · have hin : i ≠ next e := by
        intro h
        apply hei
        rw [h, prev_next]
      rw [integral_eq_zero_of_ae (hzero e he hin), mul_zero]
  · simp

variable (P Z : Matrix (Fin n) (Fin n) ℝ)
  (φ : Ω → Fin n → ℝ) (hφ : Continuous φ)
  (hdiag : ∀ i, P i i = 0)
  (hpos : ∀ i j, i ≠ j → 0 < P i j)
  (hpair : ∀ i j, P i j = ∫ x, |coordinate Z φ j x| ∂μ i)
  (hcenter : ∀ i j, ∫ x, φ x j ∂μ i = 0)

include hφ hdiag hpair in
theorem coordinate_zero_on_original (i : Fin n) :
    coordinate Z φ i =ᵐ[μ i] 0 := by
  have hi : (∫ x, |coordinate Z φ i x| ∂μ i) = 0 := by
    rw [← hpair, hdiag]
  have hz := (integral_eq_zero_iff_of_nonneg
    (fun x => abs_nonneg _) (continuous_integrable (μ i) _
      (coordinate_continuous Z φ hφ i).abs)).mp hi
  filter_upwards [hz] with x hx
  exact abs_eq_zero.mp hx

include hφ hdiag hpair in
theorem coordinate_zero_off_edge (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
    (e i : Fin n) (hi : i ≠ e) (hin : i ≠ next e) :
    coordinate Z φ i =ᵐ[ν e] 0 :=
  transfer_ae μ ν r hr hdecomp e i hi hin
    (coordinate_zero_on_original μ P Z φ hφ hdiag hpair i)

include hφ hcenter in
theorem original_coordinate_centered (i j : Fin n) :
    (∫ x, coordinate Z φ j x ∂μ i) = 0 := by
  rw [integral_coordinate (μ i) Z φ hφ j]
  simp [hcenter]

include hφ hdiag hpos hpair hcenter in
theorem outgoing_moments (hn : 3 ≤ n) (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e) (i : Fin n) :
    (∫ x, coordinate Z φ i x ∂ν i) = 0 ∧
      0 < ∫ x, |coordinate Z φ i x| ∂ν i := by
  have hc := coordinate_continuous Z φ hφ i
  have hz := coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp
  have hs := isolate_outgoing μ ν r hr hdecomp i _ hc (fun e => hz e i)
  have ha := isolate_outgoing μ ν r hr hdecomp i _ hc.abs
    (fun e hi hin => (hz e i hi hin).mono fun x hx => by simp [hx])
  have hrpos := hr.2.2 i (prev i) (prev_ne (by omega) i) (prev_ne_next hn i)
  rw [original_coordinate_centered μ Z φ hφ hcenter] at hs
  have hs0 : (∫ x, coordinate Z φ i x ∂ν i) = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left hrpos.ne'
  refine ⟨hs0, ?_⟩
  have hp := hpos (prev i) i (prev_ne (by omega) i)
  rw [hpair, ha] at hp
  by_contra h
  have hle : (∫ x, |coordinate Z φ i x| ∂ν i) ≤ 0 := le_of_not_gt h
  have := mul_nonpos_of_nonneg_of_nonpos hrpos.le hle
  linarith

include hφ hdiag hpos hpair hcenter in
theorem incoming_moments (hn : 3 ≤ n) (hr : RayPattern r)
    (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e) (i : Fin n) :
    (∫ x, coordinate Z φ i x ∂ν (prev i)) = 0 ∧
      0 < ∫ x, |coordinate Z φ i x| ∂ν (prev i) := by
  have hc := coordinate_continuous Z φ hφ i
  have hz := coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp
  have hs := isolate_incoming μ ν r hr hdecomp i _ hc (fun e => hz e i)
  have ha := isolate_incoming μ ν r hr hdecomp i _ hc.abs
    (fun e hi hin => (hz e i hi hin).mono fun x hx => by simp [hx])
  have hnex : next i ≠ prev i := Ne.symm (prev_ne_next hn i)
  have hne2 : next i ≠ next (prev i) := by simpa using next_ne (by omega) i
  have hrpos := hr.2.2 (prev i) (next i) hnex hne2
  rw [original_coordinate_centered μ Z φ hφ hcenter] at hs
  have hs0 : (∫ x, coordinate Z φ i x ∂ν (prev i)) = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left hrpos.ne'
  refine ⟨hs0, ?_⟩
  have hp := hpos (next i) i (next_ne (by omega) i)
  rw [hpair, ha] at hp
  by_contra h
  have hle : (∫ x, |coordinate Z φ i x| ∂ν (prev i)) ≤ 0 := le_of_not_gt h
  have := mul_nonpos_of_nonneg_of_nonpos hrpos.le hle
  linarith

end Compact
end VolumeVerification.EdgeMoments

