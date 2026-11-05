module

public import Projection.Basic
public import VolumeVerification.MatrixInertia
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Tactic.FunProp

/-!
# Relative-open strict counterexample families

This file concerns finite-dimensional matrix topology only. Its exclusion
hypothesis is explicit: the geometric obstruction must supply it. The proof
uses compactness of a unit sphere in one fixed negative hyperplane.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Module Filter
open scoped BigOperators Matrix Topology

namespace RankThreeProjection
open VolumeVerification.MatrixInertia

/-- The ambient space specified in the open-set assertion of Theorem 1.1. -/
abbrev HollowSymmetricArray (n : ℕ) :=
  {P : Array n // (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i)}

/-- Actual quadratic-form inertia, including absence of a radical. -/
def StrictLorentzian {n : ℕ} (P : Array n) : Prop :=
  sigPos P.toQuadraticForm' = 1 ∧
  sigNeg P.toQuadraticForm' = n - 1 ∧
  finrank ℝ P.toQuadraticForm'.radical = 0

theorem continuous_matrix_quadratic {n : ℕ} :
    Continuous (fun z : Array n × Space n => z.1.toQuadraticForm' z.2) := by
  simp only [quadratic_apply]
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- Strict negativity on a fixed hyperplane is an open matrix condition. -/
theorem isOpen_negative_on_kernel {n : ℕ} (l : Space n →ₗ[ℝ] ℝ) :
    IsOpen {P : Array n | ∀ x ∈ l.ker, x ≠ 0 → P.toQuadraticForm' x < 0} := by
  let S := Metric.sphere (0 : l.ker) 1
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : l.ker) 1)
  let bad : Set (Array n × S) :=
    {z | 0 ≤ z.1.toQuadraticForm' z.2.val.val}
  have hb : IsClosed bad := by
    have hS : Continuous (fun x : S => (x.val : l.ker)) := continuous_subtype_val
    have hker : Continuous (fun x : l.ker => (x.val : Space n)) :=
      continuous_subtype_val
    have hpoint : Continuous (fun z : Array n × S => (z.2.val.val : Space n)) :=
      hker.comp (hS.comp continuous_snd)
    have hquad : Continuous
        (fun z : Array n × S => z.1.toQuadraticForm' (z.2.val.val : Space n)) := by
      simp only [quadratic_apply]
      refine continuous_finsetSum _ (fun i _ => ?_)
      refine continuous_finsetSum _ (fun j _ => ?_)
      exact (((continuous_apply i).comp hpoint).mul
        ((continuous_apply j).comp hpoint)).mul
          ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
    exact isClosed_le continuous_const hquad
  have hopen : IsOpen (Prod.fst '' bad)ᶜ :=
    (isClosedMap_fst_of_compactSpace bad hb).isOpen_compl
  convert hopen using 1
  ext P
  constructor
  · intro hP hbad
    obtain ⟨⟨Q, x⟩, hx, he⟩ := hbad
    change Q = P at he
    subst Q
    have hnorm : ‖x.val‖ = 1 := by
      simpa only [S, Metric.mem_sphere, dist_zero_right] using x.property
    have hne : x.val.val ≠ 0 := by
      intro hzero
      have hx0 : x.val = 0 := Subtype.ext hzero
      rw [hx0, norm_zero] at hnorm
      norm_num at hnorm
    exact (not_le_of_gt (hP x.val.val x.val.property hne)) hx
  · intro hP x hx hne
    let y : l.ker := ⟨x, hx⟩
    have hy : y ≠ 0 := by
      intro he
      exact hne (congrArg Subtype.val he)
    let z : l.ker := ‖y‖⁻¹ • y
    have hz : z ∈ S := by
      simp only [S, z, Metric.mem_sphere, dist_zero_right]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    have hq : P.toQuadraticForm' z.val < 0 := by
      by_contra h
      apply hP
      exact ⟨(P, ⟨z, hz⟩), le_of_not_gt h, rfl⟩
    have hscale : 0 < ‖y‖⁻¹ * ‖y‖⁻¹ :=
      mul_pos (inv_pos.mpr (norm_pos_iff.mpr hy))
        (inv_pos.mpr (norm_pos_iff.mpr hy))
    change P.toQuadraticForm' (‖y‖⁻¹ • x) < 0 at hq
    rw [QuadraticMap.map_smul] at hq
    exact (smul_neg_iff_of_pos_left hscale).mp hq

theorem isOpen_positive_off_diagonal (n : ℕ) :
    IsOpen {P : Array n | ∀ i j, i ≠ j → 0 < P i j} := by
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _hij
  exact isOpen_lt continuous_const
    ((continuous_apply j).comp (continuous_apply i))

/-- The negative hyperplane and exclusion persist on a relative-open
neighborhood consisting of positive hollow matrices of inertia (1,n-1,0). -/
theorem exists_open_strict_family_of_negative_kernel {n : ℕ} (hn : 2 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P)
    (houtside : P ∉ closedProjectionLocus n)
    (l : Space n →ₗ[ℝ] ℝ)
    (hnegative : ∀ x ∈ l.ker, x ≠ 0 → P.toQuadraticForm' x < 0) :
    ∃ V : Set (HollowSymmetricArray n),
      IsOpen V ∧ V.Nonempty ∧
      ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧
        StrictLorentzian Q.val ∧ Q.val ∉ closedProjectionLocus n := by
  let V : Set (HollowSymmetricArray n) :=
    {Q | (∀ x ∈ l.ker, x ≠ 0 → Q.val.toQuadraticForm' x < 0) ∧
      (∀ i j, i ≠ j → 0 < Q.val i j) ∧ Q.val ∉ closedProjectionLocus n}
  refine ⟨V, ?_, ?_, ?_⟩
  · exact ((isOpen_negative_on_kernel l).inter
      ((isOpen_positive_off_diagonal n).inter
        (isClosed_closedProjectionLocus n).isOpen_compl)).preimage
      continuous_subtype_val
  · exact ⟨⟨P, hP.1, hP.2.1⟩, hnegative, hP.2.2, houtside⟩
  · intro Q hQ
    refine ⟨⟨Q.property.1, Q.property.2, hQ.2.1⟩, ?_, hQ.2.2⟩
    have hpositive : ∃ x, 0 < Q.val.toQuadraticForm' x := by
      let i : Fin n := ⟨0, by omega⟩
      let j : Fin n := ⟨1, by omega⟩
      have hij : i ≠ j := by
        intro h
        have he := congrArg Fin.val h
        simp [i, j] at he
      refine ⟨Pi.single i 1 + Pi.single j 1, ?_⟩
      rw [quadratic_pair Q.val Q.property.2 Q.property.1 i j]
      exact mul_pos (by norm_num) (hQ.2.1 i j hij)
    simpa only [StrictLorentzian, Space, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using
      strict_signature_of_negative_kernel Q.val.toQuadraticForm' l hQ.1 hpositive

/-- Exclusion persists for all sufficiently small positive parameters. -/
theorem strict_perturbations_outside {n : ℕ} (P : Array n) (a : Fin n → ℝ)
    (houtside : P ∉ closedProjectionLocus n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      strictPerturb P a ε ∉ closedProjectionLocus n := by
  have he : ∀ᶠ ε : ℝ in 𝓝 0,
      strictPerturb P a ε ∉ closedProjectionLocus n :=
    (strictPerturb_tendsto P a).eventually
      ((isClosed_closedProjectionLocus n).isOpen_compl.mem_nhds houtside)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  apply hball
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
    abs_of_pos hε] using hεδ

/-- All perturbation and relative-openness conclusions follow from the exact
rank-three exclusion. That geometric exclusion is an explicit hypothesis. -/
theorem rank_three_strict_family {n : ℕ} (hn : 5 ≤ n)
    (P : Array n) (hP : PositiveHollowSymmetric P) (hrank : P.rank = 3)
    (houtside : P ∉ closedProjectionLocus n) :
    ∃ a : Fin n → ℝ,
      (∀ i, 0 < a i) ∧
      Tendsto (strictPerturb P a) (𝓝 0) (𝓝 P) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        PositiveHollowSymmetric (strictPerturb P a ε) ∧
        StrictLorentzian (strictPerturb P a ε) ∧
        strictPerturb P a ε ∉ closedProjectionLocus n) ∧
      (∃ V : Set (HollowSymmetricArray n), IsOpen V ∧ V.Nonempty ∧
        ∀ Q ∈ V, PositiveHollowSymmetric Q.val ∧ StrictLorentzian Q.val ∧
          Q.val ∉ closedProjectionLocus n) := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀, i₁] at this
  have h02 : i₀ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₀, i₂] at this
  have h12 : i₁ ≠ i₂ := by intro h; have := congrArg Fin.val h; simp [i₁, i₂] at this
  obtain ⟨a,b,c,ha,_hnull,hfactor⟩ :=
    VolumeVerification.CircleFactorization.exists_lorentz_factorization
      P hP.2.1 hP.1 hP.2.2 hrank.le i₀ i₁ i₂ h01 h02 h12
  obtain ⟨δ, hδ, hout⟩ := strict_perturbations_outside P a houtside
  have hpert (ε : ℝ) (hε : 0 < ε) :
      PositiveHollowSymmetric (strictPerturb P a ε) :=
    ⟨strictPerturb_hollow P a ε hP.1,
      strictPerturb_symmetric P a ε hP.2.1,
      strictPerturb_positive P a ε ha hε.le hP.2.2⟩
  refine ⟨a, ha, strictPerturb_tendsto P a, ⟨δ, hδ, ?_⟩, ?_⟩
  · intro ε hε hεδ
    refine ⟨hpert ε hε, ?_, hout ε hε hεδ⟩
    simpa only [StrictLorentzian, Fintype.card_fin] using
      strictPerturb_signature P a b c ha hfactor hP.2.1 hP.1 hP.2.2 i₀ i₁ h01 ε hε
  · exact exists_open_strict_family_of_negative_kernel (by omega)
      (strictPerturb P a (δ / 2)) (hpert _ (by positivity))
      (hout _ (by positivity) (by linarith)) (dotLinear a)
      (strictPerturb_negative_kernel P a b c ha hfactor (δ / 2) (by positivity))

end RankThreeProjection

