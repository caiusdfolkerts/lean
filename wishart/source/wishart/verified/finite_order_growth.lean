module

public import wishart.verified.real_remainder12

/-!
# Finite-order polynomial bounds on a support set

The radial mean lemma needs only two derivatives on the positive semidefinite
cone.  These helpers retain the set on which a polynomial envelope is known;
they impose neither smoothness of higher order nor growth away from that set.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Filter Set
open WishartVerification
open scoped Topology ENNReal

namespace Wishart.FiniteOrder

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedAddCommGroup H]

/-- A polynomial bound for the value of a function, restricted to a specified
set.  No differentiability condition is part of this definition. -/
def PolynomialBoundOn (s : Set E) (f : E → F) : Prop :=
  ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k

namespace PolynomialBoundOn

theorem const (s : Set E) (c : F) : PolynomialBoundOn s (fun _ => c) :=
  ⟨0, ‖c‖, norm_nonneg _, fun _ _ => by simp only [pow_zero, mul_one, le_refl]⟩

theorem id (s : Set E) : PolynomialBoundOn s (fun x : E => x) := by
  refine ⟨1, 1, zero_le_one, ?_⟩
  intro x hx
  simp only [pow_one, one_mul]
  linarith

theorem mono_set {s t : Set E} {f : E → F}
    (hf : PolynomialBoundOn t f) (hst : s ⊆ t) : PolynomialBoundOn s f := by
  obtain ⟨k, C, hC, hb⟩ := hf
  exact ⟨k, C, hC, fun x hx => hb x (hst hx)⟩

theorem mono {s : Set E} {f : E → F} {g : E → G}
    (hg : PolynomialBoundOn s g) (hfg : ∀ x ∈ s, ‖f x‖ ≤ ‖g x‖) :
    PolynomialBoundOn s f := by
  obtain ⟨k, C, hC, hb⟩ := hg
  exact ⟨k, C, hC, fun x hx => (hfg x hx).trans (hb x hx)⟩

theorem congr {s : Set E} {f g : E → F}
    (hf : PolynomialBoundOn s f) (hfg : EqOn f g s) : PolynomialBoundOn s g :=
  hf.mono fun x hx => by rw [hfg hx]

theorem norm {s : Set E} {f : E → F} (hf : PolynomialBoundOn s f) :
    PolynomialBoundOn s (fun x => ‖f x‖) :=
  hf.mono fun _ _ => by simp only [norm_norm, le_refl]

theorem add {s : Set E} {f g : E → F}
    (hf : PolynomialBoundOn s f) (hg : PolynomialBoundOn s g) :
    PolynomialBoundOn s (fun x => f x + g x) := by
  obtain ⟨k, C, hC, hb⟩ := hf
  obtain ⟨l, D, hD, hc⟩ := hg
  refine ⟨k + l, C + D, add_nonneg hC hD, ?_⟩
  intro x hx
  have hbase : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hkl := pow_le_pow_right₀ hbase (Nat.le_add_right k l)
  have hlk := pow_le_pow_right₀ hbase (Nat.le_add_left l k)
  calc
    ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ C * (1 + ‖x‖) ^ k + D * (1 + ‖x‖) ^ l := add_le_add (hb x hx) (hc x hx)
    _ ≤ C * (1 + ‖x‖) ^ (k + l) + D * (1 + ‖x‖) ^ (k + l) :=
      add_le_add (mul_le_mul_of_nonneg_left hkl hC) (mul_le_mul_of_nonneg_left hlk hD)
    _ = (C + D) * (1 + ‖x‖) ^ (k + l) := by ring

theorem neg {s : Set E} {f : E → F} (hf : PolynomialBoundOn s f) :
    PolynomialBoundOn s (fun x => -f x) :=
  hf.mono fun _ _ => by simp only [norm_neg, le_refl]

theorem sub {s : Set E} {f g : E → F}
    (hf : PolynomialBoundOn s f) (hg : PolynomialBoundOn s g) :
    PolynomialBoundOn s (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul {s : Set E} {f g : E → ℝ}
    (hf : PolynomialBoundOn s f) (hg : PolynomialBoundOn s g) :
    PolynomialBoundOn s (fun x => f x * g x) := by
  obtain ⟨k, C, hC, hb⟩ := hf
  obtain ⟨l, D, hD, hc⟩ := hg
  refine ⟨k + l, C * D, mul_nonneg hC hD, ?_⟩
  intro x hx
  rw [norm_mul]
  calc
    ‖f x‖ * ‖g x‖ ≤ (C * (1 + ‖x‖) ^ k) * (D * (1 + ‖x‖) ^ l) :=
      mul_le_mul (hb x hx) (hc x hx) (norm_nonneg _) (by positivity)
    _ = (C * D) * (1 + ‖x‖) ^ (k + l) := by rw [pow_add]; ring

theorem comp {s : Set E} {t : Set F} {f : F → G} {g : E → F}
    (hf : PolynomialBoundOn t f) (hg : PolynomialBoundOn s g) (hgt : MapsTo g s t) :
    PolynomialBoundOn s (fun x => f (g x)) := by
  obtain ⟨k, C, hC, hb⟩ := hf
  obtain ⟨l, D, hD, hc⟩ := hg
  refine ⟨l * k, C * (1 + D) ^ k, by positivity, ?_⟩
  intro x hx
  have hbase : 1 ≤ (1 + ‖x‖) ^ l := one_le_pow₀ (by linarith [norm_nonneg x])
  have hnorm : 1 + ‖g x‖ ≤ (1 + D) * (1 + ‖x‖) ^ l := by
    nlinarith [hc x hx]
  calc
    ‖f (g x)‖ ≤ C * (1 + ‖g x‖) ^ k := hb _ (hgt hx)
    _ ≤ C * ((1 + D) * (1 + ‖x‖) ^ l) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm k) hC
    _ = (C * (1 + D) ^ k) * (1 + ‖x‖) ^ (l * k) := by
      rw [mul_pow, pow_mul]
      ring

theorem of_temperate [NormedSpace ℝ E] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} (hf : f.HasTemperateGrowth) : PolynomialBoundOn s f := by
  obtain ⟨k, C, hC⟩ := hf.2 0
  refine ⟨k, max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hb : ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := by simpa using hC x
  exact hb.trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem clm_apply [NormedSpace ℝ F] [NormedSpace ℝ G]
    {s : Set E} {f : E → F →L[ℝ] G} {g : E → F}
    (hf : PolynomialBoundOn s f) (hg : PolynomialBoundOn s g) :
    PolynomialBoundOn s (fun x => f x (g x)) := by
  apply (hf.norm.mul hg.norm).mono
  intro x hx
  simpa only [norm_mul, norm_norm] using (f x).le_opNorm (g x)

theorem clm_comp [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
    {s : Set E} {f : E → F →L[ℝ] G} {g : E → H →L[ℝ] F}
    (hf : PolynomialBoundOn s f) (hg : PolynomialBoundOn s g) :
    PolynomialBoundOn s (fun x => (f x).comp (g x)) := by
  apply (hf.norm.mul hg.norm).mono
  intro x hx
  simpa only [norm_mul, norm_norm] using ContinuousLinearMap.opNorm_comp_le (f x) (g x)

theorem clm_flip [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
    {s : Set E} {f : E → F →L[ℝ] G →L[ℝ] H}
    (hf : PolynomialBoundOn s f) : PolynomialBoundOn s (fun x => (f x).flip) :=
  hf.mono fun _ _ => by simp only [ContinuousLinearMap.opNorm_flip, le_refl]

theorem bilinear [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {s : Set E} {f : E → F} {g : E → G}
    (hf : PolynomialBoundOn s f) (hg : PolynomialBoundOn s g) :
    PolynomialBoundOn s (fun x => B (f x) (g x)) :=
  ((const s B).clm_apply hf).clm_apply hg

theorem finset_sum {ι : Type*} (I : Finset ι) {s : Set E} (f : ι → E → F)
    (hf : ∀ i ∈ I, PolynomialBoundOn s (f i)) :
    PolynomialBoundOn s (fun x => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const s (0 : F)
  | @insert i I hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i I)).add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem memLp [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {s : Set E} {f : E → F} (hf : PolynomialBoundOn s f)
    (hmeas : AEStronglyMeasurable f μ) (hs : ∀ᵐ x ∂μ, x ∈ s)
    {q : ℝ≥0∞} (hq : q ≠ ∞) : MemLp f q μ := by
  obtain ⟨k, C, hC, hb⟩ := hf
  have hp : HasAllFiniteMoments (fun x : E => C * (1 + ‖x‖) ^ k) μ := by
    have h := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
      (show 0 ≤ (k : ℝ) by positivity)
    simpa only [Real.rpow_natCast] using h.const_mul C
  apply (hp q hq).mono' hmeas
  filter_upwards [hs] with x hx
  exact hb x hx

theorem integrable [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {s : Set E} {f : E → F} (hf : PolynomialBoundOn s f)
    (hmeas : AEStronglyMeasurable f μ) (hs : ∀ᵐ x ∂μ, x ∈ s) : Integrable f μ :=
  memLp_one_iff_integrable.mp (hf.memLp hμ hmeas hs (by simp))

theorem allFiniteMoments_norm [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {s : Set E} {f : E → F} (hf : PolynomialBoundOn s f)
    (hmeas : AEStronglyMeasurable f μ) (hs : ∀ᵐ x ∂μ, x ∈ s) :
    HasAllFiniteMoments (fun x => ‖f x‖) μ :=
  fun q hq => (hf.memLp hμ hmeas hs hq).norm

end PolynomialBoundOn

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Global C¹ regularity with polynomial bounds only for the value and first
derivative, and only on the specified set. -/
structure C1PolynomialOn (s : Set E) (f : E → F) : Prop where
  regular : ContDiff ℝ 1 f
  value : PolynomialBoundOn s f
  derivative : PolynomialBoundOn s (fderiv ℝ f)

/-- The exact finite-order growth data used by the radial mean argument. -/
structure C2PolynomialOn (s : Set E) (f : E → F) : Prop where
  regular : ContDiff ℝ 2 f
  value : PolynomialBoundOn s f
  derivative : PolynomialBoundOn s (fderiv ℝ f)
  second : PolynomialBoundOn s (fderiv ℝ (fderiv ℝ f))

namespace C1PolynomialOn

theorem of_temperate {s : Set E} {f : E → F} (hf : f.HasTemperateGrowth) :
    C1PolynomialOn s f :=
  ⟨hf.1.of_le (by simp), PolynomialBoundOn.of_temperate hf,
    PolynomialBoundOn.of_temperate (WishartVerification.hasTemperateGrowth_fderiv hf)⟩

theorem comp {s : Set E} {t : Set F} {f : F → G} {g : E → F}
    (hf : C1PolynomialOn t f) (hg : C1PolynomialOn s g) (hgt : MapsTo g s t) :
    C1PolynomialOn s (fun x => f (g x)) := by
  refine ⟨hf.regular.comp hg.regular, hf.value.comp hg.value hgt, ?_⟩
  apply ((hf.derivative.comp hg.value hgt).clm_comp hg.derivative).congr
  intro x hx
  exact (fderiv_comp x (hf.regular.differentiable (by norm_num) (g x))
    (hg.regular.differentiable (by norm_num) x)).symm

theorem const (s : Set E) (c : F) : C1PolynomialOn s (fun _ => c) :=
  of_temperate (.const c)

theorem add {s : Set E} {f g : E → F}
    (hf : C1PolynomialOn s f) (hg : C1PolynomialOn s g) :
    C1PolynomialOn s (fun x => f x + g x) := by
  refine ⟨hf.regular.add hg.regular, hf.value.add hg.value, ?_⟩
  apply (hf.derivative.add hg.derivative).congr
  intro x hx
  exact (fderiv_add (hf.regular.differentiable (by norm_num) x)
    (hg.regular.differentiable (by norm_num) x)).symm

theorem clm_apply {s : Set E} {f : E → F →L[ℝ] G} {g : E → F}
    (hf : C1PolynomialOn s f) (hg : C1PolynomialOn s g) :
    C1PolynomialOn s (fun x => f x (g x)) := by
  refine ⟨hf.regular.clm_apply hg.regular, hf.value.clm_apply hg.value, ?_⟩
  apply ((hf.value.clm_comp hg.derivative).add
    (hf.derivative.clm_flip.clm_apply hg.value)).congr
  intro x hx
  exact (fderiv_clm_apply (hf.regular.differentiable (by norm_num) x)
    (hg.regular.differentiable (by norm_num) x)).symm

theorem linear (L : F →L[ℝ] G) {s : Set E} {f : E → F}
    (hf : C1PolynomialOn s f) : C1PolynomialOn s (fun x => L (f x)) :=
  (of_temperate L.hasTemperateGrowth).comp hf (fun _ _ => mem_univ _)

theorem bilinear [NormedSpace ℝ H] (B : F →L[ℝ] G →L[ℝ] H)
    {s : Set E} {f : E → F} {g : E → G}
    (hf : C1PolynomialOn s f) (hg : C1PolynomialOn s g) :
    C1PolynomialOn s (fun x => B (f x) (g x)) :=
  (hf.linear B).clm_apply hg

theorem mul {s : Set E} {f g : E → ℝ}
    (hf : C1PolynomialOn s f) (hg : C1PolynomialOn s g) :
    C1PolynomialOn s (fun x => f x * g x) :=
  bilinear (ContinuousLinearMap.mul ℝ ℝ) hf hg

theorem smul {s : Set E} {f : E → ℝ} {g : E → F}
    (hf : C1PolynomialOn s f) (hg : C1PolynomialOn s g) :
    C1PolynomialOn s (fun x => f x • g x) :=
  bilinear (ContinuousLinearMap.lsmul ℝ ℝ) hf hg

theorem clm_comp [NormedSpace ℝ H]
    {s : Set E} {f : E → F →L[ℝ] G} {g : E → H →L[ℝ] F}
    (hf : C1PolynomialOn s f) (hg : C1PolynomialOn s g) :
    C1PolynomialOn s (fun x => (f x).comp (g x)) :=
  bilinear (ContinuousLinearMap.compL ℝ H F G) hf hg

theorem congr {s : Set E} {f g : E → F}
    (hf : C1PolynomialOn s f) (hfg : f = g) : C1PolynomialOn s g := hfg ▸ hf

end C1PolynomialOn

namespace C2PolynomialOn

theorem of_temperate {s : Set E} {f : E → F} (hf : f.HasTemperateGrowth) :
    C2PolynomialOn s f :=
  ⟨hf.1.of_le (by simp), PolynomialBoundOn.of_temperate hf,
    PolynomialBoundOn.of_temperate (hasTemperateGrowth_fderiv hf),
    PolynomialBoundOn.of_temperate (hasTemperateGrowth_fderiv (hasTemperateGrowth_fderiv hf))⟩

theorem toC1 {s : Set E} {f : E → F} (hf : C2PolynomialOn s f) :
    C1PolynomialOn s f :=
  ⟨hf.regular.of_le (by norm_num), hf.value, hf.derivative⟩

theorem fderiv {s : Set E} {f : E → F} (hf : C2PolynomialOn s f) :
    C1PolynomialOn s (fderiv ℝ f) := by
  refine ⟨?_, hf.derivative, hf.second⟩
  exact (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f from hf.regular)).2.2

theorem mul {s : Set E} {f g : E → ℝ}
    (hf : C2PolynomialOn s f) (hg : C2PolynomialOn s g) :
    C2PolynomialOn s (fun x => f x * g x) := by
  have hd := (hf.toC1.smul hg.fderiv).add (hg.toC1.smul hf.fderiv)
  have heq : (fun x => f x • _root_.fderiv ℝ g x + g x • _root_.fderiv ℝ f x) =
      _root_.fderiv ℝ (fun x => f x * g x) := by
    funext x
    exact (fderiv_fun_mul (hf.regular.differentiable (by norm_num) x)
      (hg.regular.differentiable (by norm_num) x)).symm
  have hd' := hd.congr heq
  exact ⟨hf.regular.mul hg.regular, hf.value.mul hg.value, hd'.value, hd'.derivative⟩

theorem comp_linear {s : Set E} {t : Set F} {f : F → G}
    (hf : C2PolynomialOn t f) (L : E →L[ℝ] F) (hL : MapsTo L s t) :
    C2PolynomialOn s (fun x => f (L x)) := by
  have hpoly : C1PolynomialOn s (fun x => _root_.fderiv ℝ f (L x)) :=
    hf.fderiv.comp (C1PolynomialOn.of_temperate L.hasTemperateGrowth) hL
  have hd := hpoly.clm_comp (C1PolynomialOn.const s L)
  have heq : (fun x => (_root_.fderiv ℝ f (L x)).comp L) =
      _root_.fderiv ℝ (fun x => f (L x)) := by
    funext x
    simpa only [L.fderiv, Function.comp_def] using
      (fderiv_comp x (hf.regular.differentiable (by norm_num) (L x)) L.differentiableAt).symm
  have hd' := hd.congr heq
  exact ⟨hf.regular.comp L.contDiff,
    hf.value.comp (PolynomialBoundOn.of_temperate L.hasTemperateGrowth) hL,
    hd'.value, hd'.derivative⟩

end C2PolynomialOn

/-- The closed positive semidefinite cone in the real symmetric matrix space. -/
def psdCone (p : ℕ) : Set (SymmetricMatrix p) :=
  {X | (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef}

/-- The support condition for a background positive semidefinite matrix and
an unrestricted Gaussian row. -/
def radialSupport (p : ℕ) : Set (RadialInputSpace p) :=
  {Y | Y.1 ∈ psdCone p}

theorem radialInput_mapsTo {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    MapsTo (radialInput v r) (radialSupport p) (psdCone p) := by
  intro Y hY
  exact hY.add (rankOneSymmetric_posSemidef _)

theorem radialInput_parameter_mapsTo {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    MapsTo (fun q : ℝ × RadialInputSpace p => radialInput v q.1 q.2)
      (univ ×ˢ radialSupport p) (psdCone p) := by
  intro q hq
  exact radialInput_mapsTo v q.1 hq.2

theorem add_psd_mapsTo {p : ℕ} {T : SymmetricMatrix p} (hT : T ∈ psdCone p) :
    MapsTo (fun X : SymmetricMatrix p => X + T) (psdCone p) (psdCone p) :=
  fun _ hX => hX.add hT

end Wishart.FiniteOrder
