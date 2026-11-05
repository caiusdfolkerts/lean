module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Actual Wulff first variation: a source-preserving dependency extraction

The declaration bodies below are copied from the OpenAI mathematics repository
at commit `4eaee87548250b2682affda7d05d947c05554bae`. Only the support-function,
spherical-measure, gauge, and first-variation declarations needed here are
included; the unrelated Petty projection inequality is not imported.

The extraction script and the exact source-range/hash manifest are retained in
`work/extract_wulff_variation.py` and `work/wulff-extraction-manifest.json`.
Import adaptation and the modern Lean module header are local changes.
-/

@[expose] public section
set_option autoImplicit false

namespace OAI.PettyProjection
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def unitBall (n : ℕ) : Set (Space n) := Metric.closedBall 0 1

def kappa (n : ℕ) : ℝ := volume.real (unitBall n)


end
end OAI.PettyProjection

namespace OAI.PettyProjection.Spherical
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := sphere (0 : Space n) 1

def surface (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

def sigma (n : ℕ) : Measure (Sphere n) :=
  (surface n univ)⁻¹ • surface n

instance surface_finite (n : ℕ) : IsFiniteMeasure (surface n) := by
  unfold surface
  infer_instance

lemma surface_ne_zero (n : ℕ) [NeZero n] : surface n ≠ 0 := by
  exact Measure.toSphere_ne_zero _

instance sigma_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (sigma n) := by
  constructor
  rw [sigma, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_ne_zero.mpr (surface_ne_zero n)) (measure_ne_top _ _)

instance surface_open_pos (n : ℕ) : (surface n).IsOpenPosMeasure := by
  unfold surface
  infer_instance

instance sigma_open_pos (n : ℕ) : (sigma n).IsOpenPosMeasure := by
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

/-- Spherical means in the probability normalization. -/
def mean {n : ℕ} (f : Sphere n → ℝ) : ℝ := ∫ u, f u ∂sigma n

lemma mean_const (n : ℕ) [NeZero n] (c : ℝ) : mean (fun _ : Sphere n => c) = c := by
  simp [mean]

instance sphere_compact (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Space n) 1)

lemma norm_coe {n : ℕ} (u : Sphere n) : ‖(u : Space n)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property


end
end OAI.PettyProjection.Spherical

namespace OAI.PettyProjection
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
/-- The actual support function of a compact body, not a surrogate gauge. -/
def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x => ⟪u,x⟫) '' K)

lemma support_attained {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u : Space n) : ∃ x ∈ K, support K u = ⟪u,x⟫ :=
  hK.exists_sSup_image_eq hKn (by fun_prop)

lemma inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {x : Space n} (hx : x ∈ K) (u : Space n) : ⟪u,x⟫ ≤ support K u := by
  exact le_csSup (hK.bddAbove_image (by fun_prop)) (mem_image_of_mem _ hx)

lemma support_le_iff {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {u : Space n} {a : ℝ} : support K u ≤ a ↔ ∀ x ∈ K, ⟪u,x⟫ ≤ a := by
  constructor
  · intro h x hx; exact (inner_le_support hK hx u).trans h
  · intro h
    obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]; exact h x hx

lemma support_continuous {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    Continuous (support K) :=
  hK.continuous_sSup (by fun_prop)

lemma support_lipschitz {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {R : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) : LipschitzWith R (support K) := by
  apply LipschitzWith.of_le_add_mul
  intro u v
  obtain ⟨x,hx,he⟩ := support_attained hK hKn u
  rw [he]
  have hi := inner_le_support hK hx v
  have hbound : ⟪u-v,x⟫ ≤ R*dist u v := by
    calc
      _ ≤ ‖u-v‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖u-v‖*R := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _)
      _ = _ := by rw [dist_eq_norm]; ring
  rw [inner_sub_left] at hbound
  linarith

lemma support_smul {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (u : Space n) : support K (r • u) = r*support K u := by
  apply le_antisymm
  · apply (support_le_iff hK hKn).mpr
    intro x hx
    rw [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) hr
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_left] using inner_le_support hK hx (r • u)

lemma support_add_le {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u v : Space n) : support K (u+v) ≤ support K u+support K v := by
  apply (support_le_iff hK hKn).mpr
  intro x hx
  rw [inner_add_left]
  exact add_le_add (inner_le_support hK hx u) (inner_le_support hK hx v)

lemma support_nonneg {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (h0 : 0 ∈ K)
    (u : Space n) : 0 ≤ support K u := by
  simpa only [inner_zero_right] using inner_le_support hK h0 u

lemma support_minkowski {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hLn : L.Nonempty)
    (u : Space n) : support (K+L) u = support K u+support L u := by
  apply le_antisymm
  · apply (support_le_iff (hK.add hL) (hKn.add hLn)).mpr
    rintro _ ⟨x,hx,y,hy,rfl⟩
    rw [inner_add_right]
    exact add_le_add (inner_le_support hK hx u) (inner_le_support hL hy u)
  · obtain ⟨x,hx,hxe⟩ := support_attained hK hKn u
    obtain ⟨y,hy,hye⟩ := support_attained hL hLn u
    rw [hxe,hye,← inner_add_right]
    exact inner_le_support (hK.add hL) (add_mem_add hx hy) u

lemma support_linear_image {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (T : Space n →L[ℝ] Space n) (u : Space n) :
    support (T '' K) u = support K (T.adjoint u) := by
  apply le_antisymm
  · apply (support_le_iff (hK.image T.continuous) (hKn.image T)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support hK hx _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn (T.adjoint u)
    rw [he,ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support (hK.image T.continuous) (mem_image_of_mem T hx) u

lemma mem_iff_inner_le_support {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) {x : Space n} :
    x ∈ K ↔ ∀ u : Space n, ⟪u,x⟫ ≤ support K u := by
  constructor
  · intro hx u; exact inner_le_support hK hx u
  · intro hx
    by_contra hn
    obtain ⟨f,a,hfa,hax⟩ := geometric_hahn_banach_closed_point hc hK.isClosed hn
    let u := (InnerProductSpace.toDual ℝ (Space n)).symm f
    have hu (y : Space n) : ⟪u,y⟫ = f y := by
      change (InnerProductSpace.toDual ℝ (Space n)) u y = f y
      rw [LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨y,hy,he⟩ := support_attained hK hKn u
    have h := hx u
    rw [he,hu,hu] at h
    exact (not_lt_of_ge h) ((hfa y hy).trans hax)

lemma support_eq_iff {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hLn : L.Nonempty) :
    support K = support L ↔ K = L := by
  constructor
  · intro h
    ext x
    rw [mem_iff_inner_le_support hK hcK hKn,mem_iff_inner_le_support hL hcL hLn,h]
  · rintro rfl; rfl


end
end OAI.PettyProjection

namespace OAI.PettyProjection.Spherical
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
lemma sphere_ae_of_radial {n : ℕ} {P : Space n → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (Space n)), P x)
    (hr : ∀ (u : Sphere n) (r : ℝ), 0 < r → P (r • (u : Space n)) → P u) :
    ∀ᵐ (u : Sphere n) ∂sigma n, P (u : Space n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n) - 1)
  have hν : ν ≠ 0 := by
    intro h
    have he := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n) - 1)
      (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))
    change ν _ = _ at he
    rw [h] at he
    have hp : 0 < (1 : ℝ) ^ (Module.finrank ℝ (Space n) - 1 + 1) /
        ((Module.finrank ℝ (Space n) - 1 : ℕ) + 1) := by positivity
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) he.symm
  let : NeZero ν := ⟨hν⟩
  have hs : ∀ᵐ (x : ({0}ᶜ : Set (Space n))) ∂(volume : Measure (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n), P (x : Space n) :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space n)).compl).mp
      (ae_restrict_of_ae hP)
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hi := hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hh := hi.quasiMeasurePreserving.ae hs
  have hh' : ∀ᵐ z ∂(surface n).prod ν, P (z.2.1 • (z.1 : Space n)) := by
    change ∀ᵐ z ∂(surface n).prod ν, P (((homeomorphUnitSphereProd (Space n)).symm z : ({0}ᶜ : Set (Space n))) : Space n) at hh
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh
  apply Measure.ae_smul_measure (μ := surface n) _ ((surface n univ)⁻¹)
  filter_upwards [Measure.ae_ae_of_ae_prod hh'] with u hu
  obtain ⟨r, hr'⟩ := hu.exists
  exact hr u r r.property hr'


end
end OAI.PettyProjection.Spherical

namespace OAI.PettyProjection
noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
open Spherical (Sphere norm_coe)

/-- Intersection of the actual supporting constraints, with no evenness or
convexity condition on the constraint function. -/
def wulff {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  {x | ∀ u : Sphere n, ⟪(u : Space n),x⟫ ≤ s u}

lemma wulff_closed {n : ℕ} (s : Sphere n → ℝ) : IsClosed (wulff s) := by
  unfold wulff
  rw [ofPred_forall]
  exact isClosed_iInter (fun _ => isClosed_le (by fun_prop) continuous_const)

lemma wulff_convex {n : ℕ} (s : Sphere n → ℝ) : Convex ℝ (wulff s) := by
  intro x hx y hy a b ha hb hab u
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
  calc
    _ ≤ a*s u+b*s u := add_le_add (mul_le_mul_of_nonneg_left (hx u) ha)
      (mul_le_mul_of_nonneg_left (hy u) hb)
    _ = s u := by rw [← add_mul,hab,one_mul]

lemma closedBall_subset_wulff {n : ℕ} {s : Sphere n → ℝ} {r : ℝ}
    (hr : ∀ u, r ≤ s u) : closedBall (0 : Space n) r ⊆ wulff s := by
  intro x hx u
  calc
    _ ≤ ‖(u : Space n)‖*‖x‖ := real_inner_le_norm _ _
    _ = ‖x‖ := by rw [norm_coe,one_mul]
    _ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
    _ ≤ s u := hr u

lemma wulff_subset_closedBall {n : ℕ} {s : Sphere n → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ u, s u ≤ R) : wulff s ⊆ closedBall (0 : Space n) R := by
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  by_cases h : x = 0
  · simpa [h] using hR
  · let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩
    have hu : ⟪(u : Space n),x⟫ = ‖x‖ := by
      dsimp only [u]
      rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
      field_simp
    exact hu ▸ (hx u).trans (hs u)

lemma positive_constraint_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ u, m ≤ s u ∧ s u ≤ M := by
  have hne : (univ : Set (Sphere n)).Nonempty := by
    obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
    exact ⟨⟨u,hu⟩,mem_univ _⟩
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn hne s.continuous.continuousOn
  obtain ⟨v,_,hv⟩ := isCompact_univ.exists_isMaxOn hne s.continuous.continuousOn
  exact ⟨s u,s v,hs u,hs v,fun w => ⟨hu (mem_univ w),hv (mem_univ w)⟩⟩

lemma wulff_nhds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulff s ∈ 𝓝 (0 : Space n) := by
  obtain ⟨m,M,hm,_,hb⟩ := positive_constraint_bounds s hs
  exact Metric.mem_nhds_iff.mpr ⟨m,hm,ball_subset_closedBall.trans
    (closedBall_subset_wulff (fun u => (hb u).1))⟩

lemma wulff_compact {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulff s) := by
  obtain ⟨m,M,_,hM,hb⟩ := positive_constraint_bounds s hs
  exact (isCompact_closedBall (0 : Space n) M).of_isClosed_subset (wulff_closed _)
    (wulff_subset_closedBall hM.le (fun u => (hb u).2))

lemma wulff_body {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsConvexBody (wulff s) :=
  ⟨wulff_compact s hs,wulff_convex s,⟨0,mem_interior_iff_mem_nhds.mpr (wulff_nhds s hs)⟩⟩

lemma wulff_support {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) :
    wulff (fun u : Sphere n => support K u) = K := by
  ext x
  rw [mem_iff_inner_le_support hK hc hKn]
  constructor
  · intro h u
    by_cases hu : u = 0
    · subst u
      obtain ⟨y,hy,he⟩ := support_attained hK hKn 0
      simpa only [inner_zero_left] using he.ge
    · let v : Sphere n := ⟨‖u‖⁻¹ • u, by
        rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]⟩
      have he : u = ‖u‖ • (v : Space n) := by dsimp [v]; rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr hu)]
      rw [he,real_inner_smul_left,support_smul hK hKn (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
  · intro h u; exact h u

/-- Compact coefficient set of the maximum formula. -/
def wulffCoefficients {n : ℕ} (s : Sphere n → ℝ) : Set (Space n) :=
  range (fun u : Sphere n => (s u)⁻¹ • (u : Space n))

def wulffMax {n : ℕ} (s : Sphere n → ℝ) (x : Space n) : ℝ :=
  support (wulffCoefficients s) x

lemma wulffCoefficients_compact {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    IsCompact (wulffCoefficients s) :=
  isCompact_range ((s.continuous.inv₀ (fun u => (hs u).ne')).smul continuous_subtype_val)

lemma wulffCoefficients_nonempty {n : ℕ} [NeZero n] (s : Sphere n → ℝ) :
    (wulffCoefficients s).Nonempty := by
  obtain ⟨u,hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : Space n))).mpr (by norm_num : (0:ℝ) ≤ 1)
  exact ⟨_,⟨⟨u,hu⟩,rfl⟩⟩

lemma wulffMax_attained {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : ∃ u : Sphere n, wulffMax s x = ⟪x,(u : Space n)⟫ / s u := by
  obtain ⟨y,⟨u,rfl⟩,he⟩ := support_attained (wulffCoefficients_compact s hs)
    (wulffCoefficients_nonempty s) x
  exact ⟨u,by simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using he⟩

lemma le_wulffMax {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) (u : Sphere n) : ⟪x,(u : Space n)⟫ / s u ≤ wulffMax s x := by
  simpa only [wulffMax,real_inner_smul_right,div_eq_inv_mul] using
    inner_le_support (wulffCoefficients_compact s hs) (mem_range_self u) x

lemma wulffMax_pos {n : ℕ} (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    {x : Space n} (hx : x ≠ 0) : 0 < wulffMax s x := by
  let u : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
  have he : ⟪x,(u : Space n)⟫ = ‖x‖ := by
    dsimp only [u]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  apply lt_of_lt_of_le _ (le_wulffMax s hs x u)
  rw [he]
  exact div_pos (norm_pos_iff.mpr hx) (hs u)

lemma wulffMax_zero {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    wulffMax s (0 : Space n) = 0 := by
  obtain ⟨u,he⟩ := wulffMax_attained s hs 0
  simpa only [inner_zero_left,zero_div] using he

lemma mem_smul_wulff {n : ℕ} {s : Sphere n → ℝ} {a : ℝ} (ha : 0 < a) {x : Space n} :
    x ∈ a • wulff s ↔ ∀ u : Sphere n, ⟪x,(u : Space n)⟫ ≤ a*s u := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ha.ne']
  change (∀ u : Sphere n, ⟪(u : Space n),a⁻¹ • x⟫ ≤ s u) ↔ _
  simp_rw [real_inner_smul_right,real_inner_comm (y := x),← div_eq_inv_mul,div_le_iff₀ ha]
  simp only [mul_comm]

lemma gauge_wulff_eq_max {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u)
    (x : Space n) : gauge (wulff s) x = wulffMax s x := by
  by_cases hx : x = 0
  · subst x; rw [gauge_zero,wulffMax_zero s hs]
  have hp := wulffMax_pos s hs hx
  have hmem : x ∈ wulffMax s x • wulff s := by
    apply (mem_smul_wulff hp).mpr
    intro u
    have h := (div_le_iff₀ (hs u)).mp (le_wulffMax s hs x u)
    simpa only [mul_comm] using h
  apply le_antisymm (gauge_le_of_mem hp.le hmem)
  rw [gauge_def]
  refine le_csInf (s := {r : ℝ | r ∈ Ioi 0 ∧ x ∈ r • wulff s})
    ⟨wulffMax s x,hp,hmem⟩ ?_
  rintro a ⟨ha,hax⟩
  obtain ⟨u,he⟩ := wulffMax_attained s hs x
  rw [he]
  exact (div_le_iff₀ (hs u)).mpr ((mem_smul_wulff ha).mp hax u)

lemma gauge_ae_differentiable_sphere {n : ℕ} {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n)) :
    ∀ᵐ (u : Sphere n) ∂Spherical.sigma n, DifferentiableAt ℝ (gauge K) (u : Space n) := by
  obtain ⟨C,hC⟩ := hc.lipschitz_gauge h0
  apply Spherical.sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hh : DifferentiableAt ℝ (fun x : Space n => r⁻¹ * gauge K (r • x)) (u : Space n) :=
    (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_mul r⁻¹
  have he : (fun x : Space n => r⁻¹ * gauge K (r • x)) = gauge K := by
    funext x
    rw [gauge_smul_of_nonneg (α := ℝ) hr.le,smul_eq_mul,← mul_assoc,
      inv_mul_cancel₀ hr.ne',one_mul]
  rwa [he] at hh


end
end OAI.PettyProjection

namespace OAI

universe uU

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma support_gradient_of_active {n : ℕ} {C : Set (Space n)}
    (hC : IsCompact C) {x y : Space n} (hy : y ∈ C)
    (hxy : support C x = ⟪x,y⟫)
    (hd : DifferentiableAt ℝ (support C) x) : ∇ (support C) x = y := by
  let l : Space n →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Space n) y
  have he (z : Space n) : l z = ⟪z,y⟫ := by
    change ⟪y,z⟫ = ⟪z,y⟫
    exact real_inner_comm z y
  have hl : IsLocalMin (fun z => support C z-l z) x := by
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [he,he,hxy,sub_self]
    exact sub_nonneg.mpr (inner_le_support hC hy z)
  have hz := hl.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub l.hasFDerivAt)
  have hd' : fderiv ℝ (support C) x = l := sub_eq_zero.mp hz
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,hd',he]
  exact real_inner_comm _ _

lemma wulff_gradient_of_active {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} {u : Sphere n}
    (hu : wulffMax s x = ⟪x,(u : Space n)⟫ / s u)
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    ∇ (gauge (wulff s)) x = (s u)⁻¹ • (u : Space n) := by
  have he : gauge (wulff s) = support (wulffCoefficients s) :=
    funext (gauge_wulff_eq_max s hs)
  rw [he] at hd ⊢
  apply support_gradient_of_active (wulffCoefficients_compact s hs) (mem_range_self u) _ hd
  simpa only [real_inner_smul_right,div_eq_inv_mul,wulffMax] using hu

lemma wulff_active_unique {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x)
    {u v : Sphere n} (hu : wulffMax s x = ⟪x,(u : Space n)⟫/s u)
    (hv : wulffMax s x = ⟪x,(v : Space n)⟫/s v) : u = v := by
  have he := (wulff_gradient_of_active s hs hu hd).symm.trans (wulff_gradient_of_active s hs hv hd)
  have hn := congrArg norm he
  simp only [norm_smul,norm_coe,mul_one,Real.norm_eq_abs,abs_inv,abs_of_pos (hs u),
    abs_of_pos (hs v)] at hn
  have hsuv : s u = s v := inv_injective hn
  apply Subtype.ext
  rw [hsuv] at he
  exact (smul_right_injective _ (inv_ne_zero (hs v).ne')) he

end PettyProjection
end

noncomputable section
open Set Filter Topology
namespace PettyProjection

/-- Convergence of maximizers at a unique maximum, with a compact parameter
space and joint continuity only at the limiting parameter. -/
lemma selected_max_tendsto {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f : ℝ → U → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u ≤ f t (a t))
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀) :
    Tendsto a (𝓝 0) (𝓝 u₀) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro u hu'
  obtain ⟨l,hl,hat⟩ := mapClusterPt_iff_ultrafilter.mp hu'
  apply hu
  intro v
  have ht : Tendsto (fun t : ℝ => t) (l : Filter ℝ) (𝓝 0) := hl
  have hv : Tendsto (fun t => f t v) (l : Filter ℝ) (𝓝 (f 0 v)) :=
    (hc v).tendsto.comp (ht.prodMk_nhds tendsto_const_nhds)
  have hav : Tendsto (fun t => f t (a t)) (l : Filter ℝ) (𝓝 (f 0 u)) :=
    (hc u).tendsto.comp (ht.prodMk_nhds hat)
  exact le_of_tendsto_of_tendsto hv hav (hl (hm.mono (fun t h => h v)))

lemma quotient_bounds {a b z t : ℝ} (ht : t ≠ 0) (hl : t*a ≤ z) (hh : z ≤ t*b) :
    min a b ≤ z/t ∧ z/t ≤ max a b := by
  have he : z/t*t = z := div_mul_cancel₀ z ht
  rcases lt_or_gt_of_ne ht with ht | ht
  · have hb : b ≤ z/t := by nlinarith
    have ha : z/t ≤ a := by nlinarith
    exact ⟨(min_le_right a b).trans hb,ha.trans (le_max_left a b)⟩
  · have ha : a ≤ z/t := by nlinarith
    have hb : z/t ≤ b := by nlinarith
    exact ⟨(min_le_left a b).trans ha,hb.trans (le_max_right a b)⟩

/-- Envelope differentiation from an exact continuous difference quotient.
The statement does not require a smooth boundary or a smooth maximizer. -/
lemma hasDerivAt_selected_max {U : Type uU} [TopologicalSpace U] [CompactSpace U]
    {f d : ℝ → U → ℝ} {q : ℝ → ℝ} {a : ℝ → U} {u₀ : U}
    (hc : ∀ u : U, ContinuousAt (fun p : ℝ × U => f p.1 p.2) (0,u))
    (hd : ContinuousAt (fun p : ℝ × U => d p.1 p.2) (0,u₀))
    (hq : ∀ᶠ t in 𝓝 (0 : ℝ), q t = f t (a t) ∧ ∀ u, f t u ≤ q t)
    (hq₀ : q 0 = f 0 u₀) (hm₀ : ∀ u, f 0 u ≤ q 0)
    (hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀)
    (he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u) :
    HasDerivAt q (d 0 u₀) 0 := by
  have ha : Tendsto a (𝓝 0) (𝓝 u₀) := selected_max_tendsto hc
    (hq.mono (fun t h u => h.1 ▸ h.2 u)) hu
  have hd₀ : Tendsto (fun t => d t u₀) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds tendsto_const_nhds)
  have hda : Tendsto (fun t => d t (a t)) (𝓝 0) (𝓝 (d 0 u₀)) :=
    hd.tendsto.comp (tendsto_id.prodMk_nhds ha)
  have hlo : Tendsto (fun t => min (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [min_self] using hd₀.min hda
  have hhi : Tendsto (fun t => max (d t u₀) (d t (a t))) (𝓝 0) (𝓝 (d 0 u₀)) := by
    simpa only [max_self] using hd₀.max hda
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add,smul_eq_mul,← div_eq_inv_mul]
  have hb : ∀ᶠ t in 𝓝[≠] (0 : ℝ), min (d t u₀) (d t (a t)) ≤ (q t-q 0)/t ∧
      (q t-q 0)/t ≤ max (d t u₀) (d t (a t)) := by
    filter_upwards [hq.filter_mono nhdsWithin_le_nhds,he.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht he ht0
    have htn : t ≠ 0 := ht0
    have hl : t*d t u₀ ≤ q t-q 0 := by
      rw [← he u₀,hq₀]
      exact sub_le_sub_right (ht.2 u₀) _
    have hh : q t-q 0 ≤ t*d t (a t) := by
      rw [← he (a t),ht.1]
      exact sub_le_sub_left (hm₀ (a t)) _
    exact quotient_bounds htn hl hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (hlo.mono_left nhdsWithin_le_nhds) (hhi.mono_left nhdsWithin_le_nhds)
    (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma positive_constraints_eventually {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M) := by
  obtain ⟨a,b,ha,hb,hab⟩ := positive_constraint_bounds s hs
  refine ⟨a/2,b+a/2,by positivity,by positivity,?_⟩
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| *(‖φ‖+1) < a/2 := by
    have h : Tendsto (fun t : ℝ => |t| *(‖φ‖+1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (‖φ‖+1)
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [ht] with t ht u
  have hφ : |φ u| ≤ ‖φ‖ := φ.norm_coe_le_norm u
  have hbound : |t*φ u| ≤ |t| *(‖φ‖+1) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφ.trans (by linarith)) (abs_nonneg _)
  have hlo := neg_abs_le (t*φ u)
  have hhi := le_abs_self (t*φ u)
  have hh := hab u
  change a/2 ≤ s u+t*φ u ∧ s u+t*φ u ≤ b+a/2
  constructor <;> linarith

lemma positive_constraints_nhds {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, 0 < (s+t • φ) u := by
  obtain ⟨m,M,hm,_,he⟩ := positive_constraints_eventually s φ hs
  exact he.mono (fun _ h u => hm.trans_le (h u).1)

lemma wulff_derivative_active {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) {x : Space n}
    (hd : DifferentiableAt ℝ (gauge (wulff s)) x) {u₀ : Sphere n}
    (hu₀ : wulffMax s x = ⟪x,(u₀ : Space n)⟫/s u₀) :
    HasDerivAt (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) x)
      (-(gauge (wulff s) x)*φ u₀/s u₀) 0 := by
  classical
  let f : ℝ → Sphere n → ℝ := fun t u => ⟪x,(u : Space n)⟫/(s u+t*φ u)
  let d : ℝ → Sphere n → ℝ := fun t u => -(⟪x,(u : Space n)⟫*φ u)/(s u*(s u+t*φ u))
  let a : ℝ → Sphere n := fun t => if hp : ∀ u, 0 < (s+t • φ) u then
    (wulffMax_attained (s+t • φ) hp x).choose else u₀
  have hpos := positive_constraints_nhds s φ hs
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), gauge (wulff ⇑(s+t • φ)) x = f t (a t) ∧
      ∀ u, f t u ≤ gauge (wulff ⇑(s+t • φ)) x := by
    filter_upwards [hpos] with t ht
    rw [gauge_wulff_eq_max (s+t • φ) ht]
    constructor
    · dsimp only [a]
      rw [dite_eq_left ht]
      exact (wulffMax_attained (s+t • φ) ht x).choose_spec
    · intro u; exact le_wulffMax (s+t • φ) ht x u
  have hq0 : gauge (wulff (s+(0:ℝ) • φ)) x = f 0 u₀ := by
    simpa only [zero_smul,add_zero,f,zero_mul] using (gauge_wulff_eq_max s hs x).trans hu₀
  have hm0 : ∀ u, f 0 u ≤ gauge (wulff (s+(0:ℝ) • φ)) x := by
    intro u
    simpa only [zero_smul,add_zero,f,zero_mul,gauge_wulff_eq_max s hs x] using le_wulffMax s hs x u
  have hc (u : Sphere n) : ContinuousAt (fun p : ℝ × Sphere n => f p.1 p.2) (0,u) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using (hs u).ne'
  have hdc : ContinuousAt (fun p : ℝ × Sphere n => d p.1 p.2) (0,u₀) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using mul_ne_zero (hs u₀).ne' (hs u₀).ne'
  have hu : ∀ u, (∀ v, f 0 v ≤ f 0 u) → u = u₀ := by
    intro u h
    apply wulff_active_unique s hs hd _ hu₀
    apply le_antisymm
    · simpa only [f,zero_mul,add_zero,← hu₀] using h u₀
    · exact le_wulffMax s hs x u
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u, f t u-f 0 u = t*d t u := by
    filter_upwards [hpos] with t ht u
    have hst : s u+t*φ u ≠ 0 := (ht u).ne'
    dsimp only [f,d]
    simp only [zero_mul,add_zero]
    field_simp [hst,(hs u).ne']
    ring
  have h := hasDerivAt_selected_max hc hdc hq hq0 hm0 hu he
  have he0 : d 0 u₀ = -(gauge (wulff s) x)*φ u₀/s u₀ := by
    rw [gauge_wulff_eq_max s hs x,hu₀]
    dsimp [d]
    ring
  rwa [he0] at h

/-- Wulff variation against an actual continuous positively homogeneous test.
No symmetry or boundary smoothness is assumed. -/
theorem wulff_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u, 0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ), 0 < a → ∀ x, φ (a • x) = a*φ x)
    {x : Space n} (hd : DifferentiableAt ℝ (gauge (wulff s)) x) :
    HasDerivAt (fun t : ℝ => gauge (wulff (s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) x)
      (-(gauge (wulff s) x)*φ (∇ (gauge (wulff s)) x)) 0 := by
  obtain ⟨u,hu⟩ := wulffMax_attained s hs x
  have he := wulff_gradient_of_active s hs hu hd
  have h := wulff_derivative_active s ⟨fun u : Sphere n => φ u,hφ.comp continuous_subtype_val⟩ hs hd hu
  rw [he,hh _ (inv_pos.mpr (hs u))]
  convert h using 1
  dsimp
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe surface sigma mean)

lemma kappa_pos (n : ℕ) : 0 < kappa n := by
  unfold kappa unitBall
  exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne'
    (measure_closedBall_lt_top.ne)

lemma surface_real_univ (n : ℕ) [NeZero n] : (surface n).real univ = n*kappa n := by
  rw [surface,Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace_fin]
  congr 1
  exact congrArg ENNReal.toReal (Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : Space n) (1:ℝ)).symm

/-- Polar integration of an arbitrary convex neighborhood of zero; the body
need not be symmetric or have a smooth boundary. -/
lemma gauge_volume_lintegral {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume K = ∫⁻ u : Sphere n, ENNReal.ofReal ((gauge K (u : Space n))⁻¹ ^ n / n)
      ∂surface n := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n)-1)
  let A : Set ({0}ᶜ : Set (Space n)) := Subtype.val ⁻¹' interior K
  let S : Set (Sphere n × Ioi (0:ℝ)) :=
    {z | z.2.1 < (gauge K (z.1 : Space n))⁻¹}
  have hA : MeasurableSet A := isOpen_interior.measurableSet.preimage measurable_subtype_coe
  have hS : MeasurableSet S := by
    apply isOpen_lt (by fun_prop) ?_ |>.measurableSet
    exact ((continuous_gauge hc h0).comp (continuous_subtype_val.comp continuous_fst)).inv₀
      (fun z => (hp z.1).ne')
  have he : (homeomorphUnitSphereProd (Space n)).symm ⁻¹' A = S := by
    ext z
    change (↑((homeomorphUnitSphereProd (Space n)).symm z) : Space n) ∈ interior K ↔ _
    rw [homeomorphUnitSphereProd_symm_apply_coe,← gauge_lt_one_iff_mem_interior hc h0,
      gauge_smul_of_nonneg (α := ℝ) z.2.property.le]
    change (z.2 : ℝ)*gauge K (z.1 : Space n) < 1 ↔ (z.2 : ℝ) < (gauge K (z.1 : Space n))⁻¹
    rw [inv_eq_one_div,lt_div_iff₀ (hp z.1)]
  have hm := ((volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd).symm
    (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hm' := hm.measure_preimage hA.nullMeasurableSet
  change (surface n).prod ν ((homeomorphUnitSphereProd (Space n)).symm ⁻¹' A) = _ at hm'
  rw [he, ((MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Space n)).compl)).comap_apply] at hm'
  have hi : Subtype.val '' A = interior K \ {0} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨hy,y.property⟩
    · intro hx; exact ⟨⟨x,hx.2⟩,hx.1,rfl⟩
  rw [hi,measure_sdiff_null (measure_singleton _),
    measure_interior_of_null_frontier (hc.addHaar_frontier volume)] at hm'
  rw [← hm',Measure.prod_apply hS]
  apply lintegral_congr
  intro u
  have hu : Prod.mk u ⁻¹' S = Iio (⟨(gauge K (u : Space n))⁻¹,inv_pos.mpr (hp u)⟩ : Ioi (0:ℝ)) := rfl
  rw [hu,Measure.volumeIoiPow_apply_Iio]
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have hnR := congrArg (fun j : ℕ => (j : ℝ)) hn
  simp only [Nat.cast_add,Nat.cast_one] at hnR
  simp only [finrank_euclideanSpace_fin,hn,hnR]

lemma gauge_volume {n : ℕ} [NeZero n] {K : Set (Space n)}
    (hc : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hp : ∀ u : Sphere n, 0 < gauge K (u : Space n)) :
    volume.real K = kappa n * mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) := by
  have hcont : Continuous (fun u : Sphere n => (gauge K (u : Space n))⁻¹ ^ n) :=
    (((continuous_gauge hc h0).comp continuous_subtype_val).inv₀ (fun u => (hp u).ne')).pow n
  have hnn : ∀ u : Sphere n, 0 ≤ (gauge K (u : Space n))⁻¹ ^ n := fun u => pow_nonneg (inv_nonneg.mpr (hp u).le) n
  have hv := congrArg ENNReal.toReal (gauge_volume_lintegral hc h0 hp)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.div_const n |>.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (Eventually.of_forall (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    ENNReal.toReal_ofReal (integral_nonneg (fun u => div_nonneg (hnn u) (Nat.cast_nonneg n))),
    integral_div] at hv
  change volume.real K = _ at hv
  rw [hv,mean,sigma,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _ = kappa n * (((surface n).real univ)⁻¹ * _)
  rw [surface_real_univ]
  field_simp [(kappa_pos n).ne',(Nat.cast_pos.mpr (NeZero.pos n) : (0:ℝ)<n).ne']

lemma wulff_volume {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ)) (hs : ∀ u, 0 < s u) :
    volume.real (wulff s) = kappa n * mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹ ^ n) := by
  apply gauge_volume (wulff_convex s) (wulff_nhds s hs)
  intro u
  rw [gauge_wulff_eq_max s hs]
  exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

lemma wulff_sphere_gauge_bounds {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    {m M : ℝ} (hm : 0 < m) (hs : ∀ u, m ≤ s u ∧ s u ≤ M)
    (u : Sphere n) : M⁻¹ ≤ gauge (wulff s) (u : Space n) ∧
      gauge (wulff s) (u : Space n) ≤ m⁻¹ := by
  have hp : ∀ v, 0 < s v := fun v => hm.trans_le (hs v).1
  rw [gauge_wulff_eq_max s hp]
  constructor
  · have h := le_wulffMax s hp (u : Space n) u
    rw [real_inner_self_eq_norm_sq,norm_coe,one_pow,one_div] at h
    exact (inv_anti₀ (hp u) (hs u).2).trans h
  · obtain ⟨v,hv⟩ := wulffMax_attained s hp (u : Space n)
    rw [hv]
    have hi : ⟪(u : Space n),(v : Space n)⟫ ≤ 1 := by
      simpa only [norm_coe,one_mul] using real_inner_le_norm (u : Space n) (v : Space n)
    calc
      _ ≤ 1 / s v := div_le_div_of_nonneg_right hi (hp v).le
      _ ≤ m⁻¹ := by simpa only [one_div] using inv_anti₀ hm (hs v).1

lemma quotient_perturb_bound {a b c t r m B : ℝ} (hm : 0 < m)
    (ht : m ≤ b+t*c) (hr : m ≤ b+r*c) (ha : |a| ≤ 1) (hc : |c| ≤ B) :
    |a/(b+t*c)-a/(b+r*c)| ≤ (B/m^2)*|t-r| := by
  have ht0 := hm.trans_le ht
  have hr0 := hm.trans_le hr
  have hB : 0 ≤ B := (abs_nonneg c).trans hc
  have he : a/(b+t*c)-a/(b+r*c) = a*c*(r-t)/((b+t*c)*(b+r*c)) := by
    rw [div_sub_div _ _ ht0.ne' hr0.ne']
    congr 1
    ring
  rw [he,abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos ht0,abs_of_pos hr0,abs_sub_comm r t]
  calc
    _ ≤ (1*B)*|t-r|/(m*m) := by gcongr
    _ = _ := by ring

lemma wulff_gauge_param_sub_le {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m t r : ℝ} (hm : 0 < m) (ht : ∀ u, m ≤ (s+t • φ) u)
    (hr : ∀ u, m ≤ (s+r • φ) u) (u : Sphere n) :
    gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n) ≤
      (‖φ‖/m^2)*|t-r| := by
  have htp : ∀ v, 0 < (s+t • φ) v := fun v => hm.trans_le (ht v)
  have hrp : ∀ v, 0 < (s+r • φ) v := fun v => hm.trans_le (hr v)
  rw [gauge_wulff_eq_max (s+t • φ) htp,gauge_wulff_eq_max (s+r • φ) hrp]
  obtain ⟨v,hv⟩ := wulffMax_attained (s+t • φ) htp (u : Space n)
  rw [hv]
  have hi : |⟪(u : Space n),(v : Space n)⟫| ≤ 1 := by
    simpa only [norm_coe,one_mul] using abs_real_inner_le_norm (u : Space n) (v : Space n)
  calc
    _ ≤ ⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v :=
      sub_le_sub_left (le_wulffMax (s+r • φ) hrp _ v) _
    _ ≤ |⟪(u : Space n),(v : Space n)⟫/(s+t • φ) v - ⟪(u : Space n),(v : Space n)⟫/(s+r • φ) v| := le_abs_self _
    _ ≤ _ := quotient_perturb_bound hm (ht v) (hr v) hi (φ.norm_coe_le_norm v)

lemma wulff_gauge_param_lipschitz {n : ℕ} [NeZero n] (s φ : C(Sphere n,ℝ))
    {m : ℝ} (hm : 0 < m) {T : Set ℝ} (hT : ∀ t ∈ T, ∀ u, m ≤ (s+t • φ) u)
    (u : Sphere n) : LipschitzOnWith ⟨‖φ‖/m^2,by positivity⟩
      (fun t : ℝ => gauge (wulff ⇑(s+t • φ)) (u : Space n)) T := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  change |gauge (wulff ⇑(s+t • φ)) (u : Space n)-gauge (wulff ⇑(s+r • φ)) (u : Space n)| ≤ (‖φ‖/m^2)*|t-r|
  apply abs_le.mpr
  constructor
  · have h := wulff_gauge_param_sub_le s φ hm (hT r hr) (hT t ht) u
    rw [abs_sub_comm r t] at h
    linarith
  · exact wulff_gauge_param_sub_le s φ hm (hT t ht) (hT r hr) u

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma measurable_gradient {n : ℕ} (f : Space n → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma wulff_invpow_param_lipschitz {n : ℕ} [NeZero n]
    (s φ : C(Sphere n,ℝ)) (hs : ∀ u,0 < s u) :
    ∃ T ∈ 𝓝 (0 : ℝ), ∃ C : ℝ≥0, ∀ u : Sphere n,
      LipschitzOnWith C (fun t : ℝ => (gauge (wulff ⇑(s+t • φ)) (u : Space n))⁻¹ ^ n) T := by
  obtain ⟨m,M,hm,hM,he⟩ := positive_constraints_eventually s φ hs
  let T : Set ℝ := {t | ∀ u, m ≤ (s+t • φ) u ∧ (s+t • φ) u ≤ M}
  have hT : T ∈ 𝓝 (0 : ℝ) := he
  have hc : ContDiffOn ℝ 1 (fun a : ℝ => a⁻¹^n) (Icc M⁻¹ m⁻¹) := by
    intro a ha
    exact ((contDiffAt_id.inv ((inv_pos.mpr hM).trans_le ha.1).ne').pow n).contDiffWithinAt
  obtain ⟨D,hD⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  let C : ℝ≥0 := ⟨‖φ‖/m^2,by positivity⟩
  refine ⟨T,hT,D*C,?_⟩
  intro u
  apply hD.comp (wulff_gauge_param_lipschitz s φ hm (fun t ht v => (ht v).1) u)
  intro t ht
  exact wulff_sphere_gauge_bounds (s+t • φ) hm ht u

lemma wulff_invpow_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x)
    {u : Sphere n} (hd : DifferentiableAt ℝ (gauge (wulff s)) (u : Space n)) :
    HasDerivAt (fun t : ℝ => (gauge (wulff ⇑(s+t • (⟨fun v : Sphere n => φ v,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))) (u : Space n))⁻¹^n)
      (n*(gauge (wulff s) (u : Space n))⁻¹^n*φ (∇ (gauge (wulff s)) (u : Space n))) 0 := by
  have hp : 0 < gauge (wulff s) (u : Space n) := by
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have h := ((wulff_derivative s hs φ hφ hh hd).inv
    (by simpa only [zero_smul,add_zero] using hp.ne')).pow n
  simp only [zero_smul,add_zero] at h
  apply h.congr_deriv
  simp only [Pi.inv_apply,zero_smul,add_zero]
  let q := gauge (wulff s) (u : Space n)
  have hn : n-1+1 = n := Nat.sub_add_cancel (NeZero.one_le : 1 ≤ n)
  have he : (q⁻¹)^(n-1)*q⁻¹ = (q⁻¹)^n := by rw [← pow_succ,hn]
  change (n:ℝ)*q⁻¹^(n-1)*(-(-q*_)/q^2) = (n:ℝ)*q⁻¹^n*_
  rw [← he]
  field_simp [show q ≠ 0 from hp.ne']

/-- Actual two-sided first variation in positive Wulff constraints. This is
valid for arbitrary continuous degree-one tests, not only support functions. -/
theorem wulff_volume_derivative {n : ℕ} [NeZero n] (s : C(Sphere n,ℝ))
    (hs : ∀ u,0 < s u) (φ : Space n → ℝ) (hφ : Continuous φ)
    (hh : ∀ (a : ℝ),0 < a → ∀ x,φ (a • x)=a*φ x) :
    HasDerivAt (fun t : ℝ => volume.real (wulff ⇑(s+t • (⟨fun u : Sphere n => φ u,
      hφ.comp continuous_subtype_val⟩ : C(Sphere n,ℝ)))))
      (n*kappa n*mean (fun u : Sphere n => (gauge (wulff s) (u : Space n))⁻¹^n*
        φ (∇ (gauge (wulff s)) (u : Space n)))) 0 := by
  let φs : C(Sphere n,ℝ) := ⟨fun u => φ u,hφ.comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => (gauge (wulff ⇑(s+t • φs)) (u : Space n))⁻¹^n
  let F' : Sphere n → ℝ := fun u => (n:ℝ)*(gauge (wulff s) (u : Space n))⁻¹^n*
    φ (∇ (gauge (wulff s)) (u : Space n))
  have hg : Continuous (gauge (wulff s)) := continuous_gauge (wulff_convex s) (wulff_nhds s hs)
  have hgp : ∀ u : Sphere n,0 < gauge (wulff s) (u : Space n) := by
    intro u
    rw [gauge_wulff_eq_max s hs]
    exact wulffMax_pos s hs (by intro h; simpa [h] using norm_coe u)
  have hc : Continuous (F 0) := by
    change Continuous (fun u : Sphere n => (gauge (wulff ⇑(s+0 • φs)) (u : Space n))⁻¹^n)
    simp only [zero_smul,add_zero]
    exact ((hg.comp continuous_subtype_val).inv₀ (fun u => (hgp u).ne')).pow n
  obtain ⟨T,hT,C,hC⟩ := wulff_invpow_param_lipschitz s φs hs
  have hFm : ∀ᶠ t in 𝓝 (0:ℝ), AEStronglyMeasurable (F t) (sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact (((continuous_gauge (wulff_convex _) (wulff_nhds (s+t • φs) ht)).comp
      continuous_subtype_val).measurable.inv.pow_const n).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' (sigma n) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.mul ((hg.measurable.comp measurable_subtype_coe).inv.pow_const n)).mul
      (hφ.measurable.comp ((measurable_gradient _).comp measurable_subtype_coe))
  have hder : ∀ᵐ u ∂sigma n, HasDerivAt (fun t => F t u) (F' u) 0 := by
    filter_upwards [gauge_ae_differentiable_sphere (wulff_convex s) (wulff_nhds s hs)] with u hu
    exact wulff_invpow_derivative s hs φ hφ hh hu
  have hI := (hasDerivAt_integral_of_dominated_loc_of_lip hT hFm
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hF'm
    (Eventually.of_forall (fun u => by simpa only [Real.nnabs_coe] using hC u))
    (integrable_const (C:ℝ)) hder).2
  have he : (fun t => volume.real (wulff ⇑(s+t • φs))) =ᶠ[𝓝 (0:ℝ)]
      (fun t => kappa n * ∫ u,F t u ∂sigma n) := by
    filter_upwards [positive_constraints_nhds s φs hs] with t ht
    exact wulff_volume (s+t • φs) ht
  have h := (hI.const_mul (kappa n)).congr_of_eventuallyEq he
  apply h.congr_deriv
  dsimp only [F']
  simp_rw [mul_assoc (n:ℝ)]
  rw [integral_const_mul]
  dsimp only [mean]
  ring

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe sigma mean)

lemma support_smul_set {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (u : Space n) : support (t • K) u = t*support K u := by
  have hn : (t • K).Nonempty := by obtain ⟨x,hx⟩ := hKn; exact ⟨t • x,smul_mem_smul_set hx⟩
  apply le_antisymm
  · apply (support_le_iff (hK.smul t) hn).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) ht
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_right] using
      inner_le_support (hK.smul t) (smul_mem_smul_set hx) u

lemma support_pos_of_nhds {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (h0 : K ∈ 𝓝 (0 : Space n)) (u : Sphere n) : 0 < support K u := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp h0
  have hx : (r/2) • (u : Space n) ∈ K := by
    apply hrK
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),norm_coe,mul_one]
    linarith
  have h := inner_le_support hK hx (u : Space n)
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe,one_pow,mul_one] at h
  linarith

/-- First-variation identity for actual Minkowski addition; the added
set is allowed to have any dimension. -/
theorem minkowski_volume_derivative {n : ℕ} [NeZero n] {K M : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (h0 : K ∈ 𝓝 (0 : Space n))
    (hM : IsCompact M) (hcM : Convex ℝ M) (hMn : M.Nonempty) :
    HasDerivWithinAt (fun t : ℝ => volume.real (K+t • M))
      (n*kappa n*mean (fun u : Sphere n => (gauge K (u : Space n))⁻¹^n*
        support M (∇ (gauge K) (u : Space n)))) (Ici 0) 0 := by
  have hKn : K.Nonempty := ⟨0,mem_of_mem_nhds h0⟩
  let s : C(Sphere n,ℝ) := ⟨fun u => support K u,(support_continuous hK).comp continuous_subtype_val⟩
  have hs : ∀ u,0 < s u := support_pos_of_nhds hK h0
  let φ : C(Sphere n,ℝ) := ⟨fun u => support M u,(support_continuous hM).comp continuous_subtype_val⟩
  have he : ∀ t : ℝ, 0 ≤ t → wulff ⇑(s+t • φ) = K+t • M := by
    intro t ht
    have hf : ⇑(s+t • φ) = fun u : Sphere n => support (K+t • M) u := by
      funext u
      simp only [ContinuousMap.coe_add,ContinuousMap.coe_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      change support K u+t*support M u = support (K+t • M) u
      rw [support_minkowski hK hKn (hM.smul t)
        (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩),
        support_smul_set hM hMn ht]
    rw [hf]
    exact wulff_support (hK.add (hM.smul t)) (hcK.add (hcM.smul t)) (hKn.add (by obtain ⟨x,hx⟩ := hMn; exact ⟨t • x,smul_mem_smul_set hx⟩))
  have h := (wulff_volume_derivative s hs (support M) (support_continuous hM)
    (fun a ha x => support_smul hM hMn ha.le x)).hasDerivWithinAt (s := Ici (0:ℝ))
  have hw : wulff s = K := wulff_support hK hcK hKn
  rw [hw] at h
  exact h.congr (fun t ht => congrArg volume.real (he t ht).symm)
    (congrArg volume.real (he 0 le_rfl).symm)

end PettyProjection
end

end OAI
