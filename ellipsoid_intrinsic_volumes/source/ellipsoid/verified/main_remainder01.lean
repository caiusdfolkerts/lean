module

public import ellipsoid.verified.reconstruction_complete
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import tau_ceti.analysis.polynomial.continuity_of_roots.basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/- Generated ordinary proof stage. See audit/staged_ellipsoid_remainder/MainRemainder01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Ellipsoid/CompactInverse.lean -/



noncomputable section

open Set Filter
open scoped Topology

namespace EllipsoidVerification

/-- On a compact set, injectivity and invertible strict derivatives give a
uniform inverse Lipschitz estimate. The set need not be convex, nor does its
image need to be convex. The proof excludes the compact part outside a local
inverse chart before using its Lipschitz bound. -/
theorem compact_inverse_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : E → E} {K : Set E} (hK : IsCompact K) (hF : ContinuousOn F K)
    (hinj : Set.InjOn F K)
    (hder : ∀ x ∈ K, ∃ A : E ≃L[ℝ] E, HasStrictFDerivAt F (A : E →L[ℝ] E) x) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ L * ‖F x - F y‖ := by
  let g : E → E := Function.invFunOn F K
  have hg : ∀ x ∈ K, g (F x) = x := hinj.leftInvOn_invFunOn
  have hlocal : LocallyLipschitzOn (F '' K) g := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨A, hA⟩ := hder x hx
    let P := hA.toOpenPartialHomeomorph F
    let I := hA.localInverse F A x
    obtain ⟨L, U, hU, hLip⟩ := hA.to_localInverse.exists_lipschitzOnWith
    have hclosed : IsClosed (F '' (K \ P.source)) :=
      ((hK.diff P.open_source).image_of_continuousOn
        (hF.mono Set.diff_subset)).isClosed
    have hxnot : F x ∉ F '' (K \ P.source) := by
      rintro ⟨y, hy, heq⟩
      have hyx := hinj hy.1 hx heq
      exact hy.2 (hyx.symm ▸ hA.mem_toOpenPartialHomeomorph_source)
    let V : Set E := U ∩ (F '' (K \ P.source))ᶜ ∩ (F '' K)
    refine ⟨L, V, ?_, ?_⟩
    · exact inter_mem (inter_mem (mem_nhdsWithin_of_mem_nhds hU)
        (mem_nhdsWithin_of_mem_nhds (hclosed.isOpen_compl.mem_nhds hxnot)))
        self_mem_nhdsWithin
    · have hgi (y : E) (hy : y ∈ V) : g y = I y := by
        have hyK : g y ∈ K := Function.invFunOn_mem hy.2
        have hyF : F (g y) = y := Function.invFunOn_eq hy.2
        have hyP : g y ∈ P.source := by
          by_contra h
          exact hy.1.2 ⟨g y, ⟨hyK, h⟩, hyF⟩
        have hleft := P.left_inv hyP
        change I (F (g y)) = g y at hleft
        rw [hyF] at hleft
        exact hleft.symm
      intro y hy z hz
      simpa only [hgi y hy, hgi z hz] using hLip hy.1.1 hz.1.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hK.image_of_continuousOn hF) hlocal
  refine ⟨(L : ℝ) + 1, by positivity, ?_⟩
  intro x hx y hy
  have h := hLip.dist_le_mul (F x) ⟨x, hx, rfl⟩ (F y) ⟨y, hy, rfl⟩
  rw [hg x hx, hg y hy, dist_eq_norm, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- A convenient finite-dimensional form of the compact estimate. No
quantitative lower bound on the derivative is assumed. -/
theorem compact_inverse_lipschitz_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → E} {K : Set E} (hK : IsCompact K)
    (hF : ∀ x ∈ K, ContDiffAt ℝ 1 F x) (hinj : Set.InjOn F K)
    (hder : ∀ x ∈ K, Function.Injective (fderiv ℝ F x)) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ L * ‖F x - F y‖ := by
  apply compact_inverse_lipschitz hK
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt) hinj
  intro x hx
  let A := (LinearEquiv.ofBijective (fderiv ℝ F x).toLinearMap
    ⟨hder x hx, LinearMap.injective_iff_surjective.mp (hder x hx)⟩).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  exact (hF x hx).hasStrictFDerivAt one_ne_zero

end EllipsoidVerification
end
end CanonicalSource0

section CanonicalSource1
/- Source: Ellipsoid/AugmentedCoefficientRecovery.lean -/



noncomputable section

open Set Filter Matrix Polynomial
open scoped Topology BigOperators

namespace EllipsoidVerification

/-- The last coefficient is retained as an output, so this map controls
perturbations of the volume as well as of all internal intrinsic volumes. -/
def augmentedCoefficientMap (m : ℕ) (z : (Fin m → ℝ) × ℝ) : (Fin m → ℝ) × ℝ :=
  (coefficientMap m 1 z.2 z.1, z.2)

def augmentedCoefficientDomain (m : ℕ) : Set ((Fin m → ℝ) × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 < z.2}

theorem contDiff_variableEndpoints (m : ℕ) (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun z : (Fin m → ℝ) × ℝ => fixedEndpoints m 1 z.2 z.1) := by
  apply contDiff_pi.mpr
  intro j
  unfold fixedEndpoints
  split_ifs <;> fun_prop

theorem contDiffAt_augmentedCoefficientMap {m : ℕ} {z : (Fin m → ℝ) × ℝ}
    (hz : z ∈ augmentedCoefficientDomain m) :
    ContDiffAt ℝ 1 (augmentedCoefficientMap m) z := by
  have he := fixedEndpoints_admissible (by norm_num : (0 : ℝ) < 1) hz.2 hz.1
  have hU := (isOpen_positiveCoefficientDomain (m + 1)).mem_nhds
    (admissible_mem_positiveCoefficientDomain he)
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro k
    have hk : ContDiffAt ℝ 1
        (fun e : Coefficients (m + 1) => coefficientTransform e (k.val + 1))
        (fixedEndpoints m 1 z.2 z.1) :=
      ((contDiffOn_coefficientTransform (n := m + 1) (k := k.val + 1)
        (by omega) (by omega)).contDiffAt hU).of_le (by simp)
    exact ContDiffAt.comp
      (f := fun w : (Fin m → ℝ) × ℝ => fixedEndpoints m 1 w.2 w.1)
      (g := fun e : Coefficients (m + 1) => coefficientTransform e (k.val + 1))
      z hk (contDiff_variableEndpoints m 1).contDiffAt
  · exact contDiff_snd.contDiffAt

theorem augmentedCoefficientMap_injOn {m : ℕ} :
    Set.InjOn (augmentedCoefficientMap m) (augmentedCoefficientDomain m) := by
  intro x hx y hy hxy
  have hlast := congrArg (fun w : (Fin m → ℝ) × ℝ => w.2) hxy
  change x.2 = y.2 at hlast
  have hfirst : coefficientMap m 1 x.2 x.1 = coefficientMap m 1 x.2 y.1 := by
    simpa only [augmentedCoefficientMap, hlast] using congrArg Prod.fst hxy
  have hcoords := coefficientMap_injOn_nonnegative (by norm_num : (0 : ℝ) < 1)
    hx.2 hx.1 hy.1 hfirst
  exact Prod.ext hcoords hlast

theorem augmentedCoefficientMap_fderiv_injective {m : ℕ} {z : (Fin m → ℝ) × ℝ}
    (hz : z ∈ augmentedCoefficientDomain m) :
    Function.Injective (fderiv ℝ (augmentedCoefficientMap m) z) := by
  let L := fderiv ℝ (augmentedCoefficientMap m) z
  have hL : HasFDerivAt (augmentedCoefficientMap m) L z :=
    (contDiffAt_augmentedCoefficientMap hz).differentiableAt one_ne_zero |>.hasFDerivAt
  have hsnd : (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ).comp L =
      ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ :=
    hL.snd.unique hasFDerivAt_snd
  have hfirst : L.comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) ℝ) =
      (matrixDerivative (fixedCoefficientJacobian m 1 z.2 z.1)).prod 0 := by
    have ha : HasFDerivAt
        (fun v : Fin m → ℝ => augmentedCoefficientMap m (v, z.2))
        (L.comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) ℝ)) z.1 := by
      simpa only [Function.comp_def] using
        (HasFDerivAt.comp (𝕜 := ℝ)
          (f := fun v : Fin m → ℝ => (v, z.2))
          (g := augmentedCoefficientMap m) (g' := L)
          z.1 hL (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2))
    have hb := (hasFDerivAt_coefficientMap (by norm_num : (0 : ℝ) < 1) hz.2 hz.1).prodMk
      (hasFDerivAt_const z.2 z.1)
    exact ha.unique hb
  apply (injective_iff_map_eq_zero L).mpr
  intro w hw
  have hw2 : w.2 = 0 := by
    have h := congrArg (fun A : ((Fin m → ℝ) × ℝ) →L[ℝ] ℝ => A w) hsnd
    change (L w).2 = w.2 at h
    rw [hw] at h
    exact h.symm
  have hw1 : w.1 = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := (fixedCoefficientJacobian_diagonallyStable
      (by norm_num : (0 : ℝ) < 1) hz.2 hz.1).exists_positive_coordinate hne
    have hh := congrArg (fun A : (Fin m → ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) => A w.1) hfirst
    have hw' : (w.1, (0 : ℝ)) = w := Prod.ext rfl hw2.symm
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hw', hw,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply] at hh
    have hzero := congrArg (fun y : (Fin m → ℝ) × ℝ => y.1 i) hh
    change (0 : ℝ) = (fixedCoefficientJacobian m 1 z.2 z.1 *ᵥ w.1) i at hzero
    rw [← hzero, mul_zero] at hi
    exact (lt_irrefl 0) hi
  exact Prod.ext hw1 hw2

/-- This is a uniform estimate for the literal improper-integral map,
including variations of the leading coefficient. -/
theorem augmentedCoefficientMap_inverse_lipschitz {m : ℕ}
    {K : Set ((Fin m → ℝ) × ℝ)} (hK : IsCompact K)
    (hKD : K ⊆ augmentedCoefficientDomain m) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ L * ‖augmentedCoefficientMap m x - augmentedCoefficientMap m y‖ :=
  compact_inverse_lipschitz_of_contDiff hK
    (fun x hx => contDiffAt_augmentedCoefficientMap (hKD hx))
    (augmentedCoefficientMap_injOn.mono hKD)
    (fun x hx => augmentedCoefficientMap_fderiv_injective (hKD hx))

@[fun_prop] theorem continuous_axisCoefficients (n : ℕ) :
    Continuous (axisCoefficients (n := n)) := by
  apply continuous_pi
  intro j
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Polynomial.continuousAt_coeff_prod
  intro i hi k hk
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
  split_ifs <;>
    first
    | exact continuousAt_const
    | exact continuousAt_const.add ((continuous_apply i).continuousAt.pow 2)

def axisCoefficientData {m : ℕ} (a : Fin (m + 1) → ℝ) : (Fin m → ℝ) × ℝ :=
  (internalCoefficients m (axisCoefficients a), axisCoefficients a (Fin.last (m + 1)))

@[fun_prop] theorem continuous_axisCoefficientData (m : ℕ) :
    Continuous (axisCoefficientData (m := m)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact (continuous_apply _).comp (continuous_axisCoefficients (m + 1))
  · change Continuous (fun a : Fin (m + 1) → ℝ =>
      axisCoefficients a (Fin.last (m + 1)))
    exact (continuous_apply (Fin.last (m + 1))).comp
      (continuous_axisCoefficients (m + 1))

theorem axisCoefficientData_mem {m : ℕ} {a : Fin (m + 1) → ℝ}
    (ha : ∀ i, 0 < a i) : axisCoefficientData a ∈ augmentedCoefficientDomain m := by
  have h := axisCoefficients_admissible a ha
  exact ⟨fun i => h.1 _, h.2.2⟩

theorem axisCoefficientData_inverse_lipschitz (m : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y : Fin (m + 1) → ℝ,
      x ∈ Icc (fun _ => a) (fun _ => b) → y ∈ Icc (fun _ => a) (fun _ => b) →
      ‖axisCoefficientData x - axisCoefficientData y‖ ≤
        L * ‖augmentedCoefficientMap m (axisCoefficientData x) -
          augmentedCoefficientMap m (axisCoefficientData y)‖ := by
  obtain ⟨L, hL, hbound⟩ := augmentedCoefficientMap_inverse_lipschitz
    (isCompact_Icc.image (continuous_axisCoefficientData m)) (by
      rintro _ ⟨x, hx, rfl⟩
      exact axisCoefficientData_mem fun i => ha.trans_le (hx.1 i))
  exact ⟨L, hL, fun x y hx hy => hbound _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩⟩

end EllipsoidVerification
end
end CanonicalSource1

section CanonicalSource2
/- Source: Ellipsoid/RootCounts.lean -/



noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace EllipsoidVerification

theorem finite_vertical_separation (s : Finset ℂ) (c : ℝ)
    (hs : ∀ z ∈ s, z.re ≠ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ s, ε ≤ |z.re - c| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert z s hz ih =>
      obtain ⟨ε, hε, hsep⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw))
      refine ⟨min ε |z.re - c|, lt_min hε (abs_pos.mpr (sub_ne_zero.mpr
        (hs z (Finset.mem_insert_self _ _)))), ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hsep w hw)

theorem realPart_lt_iff_of_close {z w : ℂ} {c ε : ℝ}
    (hsep : ε ≤ |z.re - c|) (hclose : ‖z - w‖ < ε) :
    z.re < c ↔ w.re < c := by
  have hdist : |z.re - w.re| < ε := by
    have hreal : |z.re - w.re| ≤ ‖z - w‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
    exact hreal.trans_lt hclose
  rcases lt_or_ge z.re c with hz | hz
  · rw [abs_of_neg (sub_neg.mpr hz)] at hsep
    have hh := (abs_lt.mp hdist).1
    constructor
    · intro _
      linarith
    · intro _
      exact hz
  · have hz' : c ≤ z.re := hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz')] at hsep
    have hh := (abs_lt.mp hdist).2
    have hw : c < w.re := by linarith
    simp [not_lt.mpr hz, not_lt.mpr hw.le]

theorem countP_realPart_eq_of_rel {s t : Multiset ℂ} {c ε : ℝ}
    (hsep : ∀ z ∈ s, ε ≤ |z.re - c|)
    (hrel : s.Rel (fun z w => ‖z - w‖ < ε) t) :
    s.countP (fun z => z.re < c) = t.countP (fun z => z.re < c) := by
  classical
  obtain ⟨n, a, b, hs, ht, hab⟩ := Multiset.rel_iff_exists_fin.mp hrel
  rw [hs, ht, Multiset.countP_map, Multiset.countP_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro i hi
  exact realPart_lt_iff_of_close (hsep (a i) (by simp [hs])) (hab i)

/-- Root counts on one side of a vertical line are locally constant as
long as no root crosses the line. Multiplicities are retained throughout. -/
theorem isLocallyConstant_rootCount_left {B : Type*} [TopologicalSpace B]
    {F : B → ℂ[X]} {d : ℕ} (hF : ∀ k ≤ d, Continuous (fun b => (F b).coeff k))
    (hdeg : ∀ b, (F b).degree = d) (c : ℝ)
    (havoid : ∀ b z, z ∈ (F b).roots → z.re ≠ c) :
    IsLocallyConstant (fun b => (F b).roots.countP (fun z => z.re < c)) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro b
  obtain ⟨ε, hε, hsep⟩ := finite_vertical_separation (F b).roots.toFinset c
    (fun z hz => havoid b z (Multiset.mem_toFinset.mp hz))
  filter_upwards [Polynomial.eventually_rel_roots_norm_sub_lt
    (fun k hk => (hF k hk).continuousAt)
    (Filter.Eventually.of_forall hdeg) hε] with b' hb'
  exact (countP_realPart_eq_of_rel
    (fun z hz => hsep z (Multiset.mem_toFinset.mpr hz)) hb').symm

theorem rootCount_left_eq_on_connected {B : Type*} [TopologicalSpace B]
    [PreconnectedSpace B] {F : B → ℂ[X]} {d : ℕ}
    (hF : ∀ k ≤ d, Continuous (fun b => (F b).coeff k))
    (hdeg : ∀ b, (F b).degree = d) (c : ℝ)
    (havoid : ∀ b z, z ∈ (F b).roots → z.re ≠ c) (b₀ b₁ : B) :
    (F b₀).roots.countP (fun z => z.re < c) =
      (F b₁).roots.countP (fun z => z.re < c) :=
  (isLocallyConstant_rootCount_left hF hdeg c havoid).apply_eq_of_preconnectedSpace b₀ b₁

/-- A real interval longer than the sum of `n` interval lengths contains
a cut separated from all `n` centres. This replaces disk-boundary topology
in the quantitative matching argument. -/
theorem exists_cut_away_from_finite_centres {n : ℕ} (a : Fin n → ℝ)
    {u v ρ : ℝ} (hρ : 0 ≤ ρ) (hlength : 2 * n * ρ < v - u) :
    ∃ c ∈ Ioo u v, ∀ i, ρ < |c - a i| := by
  classical
  by_contra h
  push_neg at h
  have hsub : Ioo u v ⊆ ⋃ i, Metric.closedBall (a i) ρ := by
    intro c hc
    obtain ⟨i, hi⟩ := h c hc
    exact mem_iUnion.mpr ⟨i, by simpa only [Metric.mem_closedBall, Real.dist_eq] using hi⟩
  have hμ := (measure_mono hsub).trans
    (measure_iUnion_fintype_le volume (fun i => Metric.closedBall (a i) ρ))
  simp only [Real.volume_Ioo, Real.volume_closedBall, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hμ
  have hnn : 0 ≤ (2 : ℝ) * n * ρ := by positivity
  have hsum : (n : ℝ≥0∞) * ENNReal.ofReal (2 * ρ) = ENNReal.ofReal (2 * n * ρ) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [hsum] at hμ
  exact (not_le_of_gt hlength) ((ENNReal.ofReal_le_ofReal_iff hnn).mp hμ)

end EllipsoidVerification
end
end CanonicalSource2

section CanonicalSource3
/- Source: Ellipsoid/RootMatchingTopology.lean -/



noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def realTupleCount {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : ℕ :=
  (Finset.univ.filter fun i => a i < c).card

theorem realTupleCount_eq_countP {n : ℕ} (a : Fin n → ℝ) (c : ℝ) :
    realTupleCount a c = (Finset.univ.val.map (fun i => (a i : ℂ))).countP
      (fun z => z.re < c) := by
  rw [Multiset.countP_map]
  change (Finset.univ.filter fun i => a i < c).card =
    (Multiset.filter (fun i => a i < c) Finset.univ.val).card
  rw [← Finset.filter_val]
  rfl

theorem realTupleCount_perm {n : ℕ} (a : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (c : ℝ) : realTupleCount (a ∘ σ) c = realTupleCount a c := by
  rw [realTupleCount_eq_countP, realTupleCount_eq_countP]
  have hm : Finset.univ.val.map (fun i => ((a ∘ σ) i : ℂ)) =
      Finset.univ.val.map (fun i => (a i : ℂ)) := by
    change Finset.univ.val.map ((fun i => (a i : ℂ)) ∘ σ) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [hm]

theorem realTupleCount_ge_of_monotone {n : ℕ} {a : Fin n → ℝ}
    (ha : Monotone a) {k : Fin n} {c : ℝ} (hk : a k < c) :
    k.val + 1 ≤ realTupleCount a c := by
  rw [← Fin.card_Iic k]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
    (ha (Finset.mem_Iic.mp hi)).trans_lt hk⟩

theorem realTupleCount_le_of_monotone {n : ℕ} {a : Fin n → ℝ}
    (ha : Monotone a) {k : Fin n} {c : ℝ} (hk : c ≤ a k) :
    realTupleCount a c ≤ k.val := by
  rw [← Fin.card_Iio k]
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_Iio.mpr
  by_contra hki
  have h := ha (le_of_not_gt hki)
  have hic := (Finset.mem_filter.mp hi).2
  linarith

/-- A root-count identity at a cut in every sufficiently long interval
forces uniform matching of the sorted tuples. -/
theorem exists_perm_dist_le_of_cut_counts {n : ℕ} (a b : Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L)
    (hcut : ∀ u v : ℝ, L < v - u →
      ∃ c ∈ Ioo u v, realTupleCount a c = realTupleCount b c) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, |a i - b (σ i)| ≤ L := by
  let A := a ∘ Tuple.sort a
  let B := b ∘ Tuple.sort b
  have hA : Monotone A := Tuple.monotone_sort a
  have hB : Monotone B := Tuple.monotone_sort b
  have hdist (k : Fin n) : |A k - B k| ≤ L := by
    apply abs_le.mpr
    constructor
    · by_contra h
      have hlt : L < B k - A k := by linarith
      obtain ⟨c, hc, heq⟩ := hcut (A k) (B k) hlt
      have hleft := realTupleCount_ge_of_monotone hA hc.1
      have hright := realTupleCount_le_of_monotone hB hc.2.le
      rw [realTupleCount_perm] at hleft hright
      omega
    · by_contra h
      have hlt : L < A k - B k := by linarith
      obtain ⟨c, hc, heq⟩ := hcut (B k) (A k) hlt
      have hleft := realTupleCount_ge_of_monotone hB hc.1
      have hright := realTupleCount_le_of_monotone hA hc.2.le
      rw [realTupleCount_perm] at hleft hright
      omega
  refine ⟨(Tuple.sort a).symm.trans (Tuple.sort b), fun i => ?_⟩
  simpa [A, B, Function.comp_def] using hdist ((Tuple.sort a).symm i)

/-- Quantitative multiplicity-preserving matching from a continuous
polynomial homotopy whose roots stay within `rho` of the initial real roots.
The homotopy itself may have nonreal roots. -/
theorem exists_perm_dist_le_of_polynomial_homotopy {n : ℕ}
    (a b : Fin n → ℝ) {F : Icc (0 : ℝ) 1 → ℂ[X]}
    (hF : ∀ k ≤ n, Continuous (fun t => (F t).coeff k))
    (hdeg : ∀ t, (F t).degree = n)
    (hzero : (F ⟨0, by simp⟩).roots = Finset.univ.val.map (fun i => (a i : ℂ)))
    (hone : (F ⟨1, by simp⟩).roots = Finset.univ.val.map (fun i => (b i : ℂ)))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hnear : ∀ t z, z ∈ (F t).roots → ∃ i, ‖z - (a i : ℂ)‖ < ρ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, |a i - b (σ i)| ≤ 2 * n * ρ := by
  letI : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  apply exists_perm_dist_le_of_cut_counts a b (by positivity)
  intro u v huv
  obtain ⟨c, hc, hsep⟩ := exists_cut_away_from_finite_centres a hρ huv
  refine ⟨c, hc, ?_⟩
  have havoid : ∀ t z, z ∈ (F t).roots → z.re ≠ c := by
    intro t z hz hzc
    obtain ⟨i, hi⟩ := hnear t z hz
    have hreal := Complex.abs_re_le_norm (z - (a i : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, hzc] at hreal
    exact (not_lt_of_ge hreal) (hi.trans (hsep i))
  have hh := rootCount_left_eq_on_connected hF hdeg c havoid
    (⟨0, by simp⟩ : Icc (0 : ℝ) 1) (⟨1, by simp⟩ : Icc (0 : ℝ) 1)
  rw [hzero, hone, ← realTupleCount_eq_countP, ← realTupleCount_eq_countP] at hh
  exact hh

end EllipsoidVerification
end
end CanonicalSource3

section CanonicalSource4
/- Source: Ellipsoid/RootMatchingBounds.lean -/



noncomputable section

open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

def realRootPolynomial {n : ℕ} (a : Fin n → ℝ) : ℂ[X] :=
  ∏ i, (X - C (a i : ℂ))

def realRootCoefficients {n : ℕ} (a : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (realRootPolynomial a).coeff i.val

theorem realRootPolynomial_monic {n : ℕ} (a : Fin n → ℝ) : (realRootPolynomial a).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem realRootPolynomial_natDegree {n : ℕ} (a : Fin n → ℝ) :
    (realRootPolynomial a).natDegree = n := by
  simp [realRootPolynomial, natDegree_prod_of_monic, monic_X_sub_C]

theorem monicOfCoeff_realRootCoefficients {n : ℕ} (a : Fin n → ℝ) :
    TauCeti.Polynomial.monicOfCoeff (realRootCoefficients a) = realRootPolynomial a :=
  TauCeti.Polynomial.monicOfCoeff_coeff (realRootPolynomial_monic a)
    (realRootPolynomial_natDegree a)

@[fun_prop] theorem continuous_realRootCoefficients (n : ℕ) :
    Continuous (realRootCoefficients (n := n)) := by
  apply continuous_pi
  intro i
  exact (TauCeti.Polynomial.continuous_coeff_prod_X_sub_C Finset.univ i.val).comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))

def rootHomotopy {n : ℕ} (c d : Fin n → ℂ) (t : Icc (0 : ℝ) 1) : ℂ[X] :=
  TauCeti.Polynomial.monicOfCoeff ((1 - (t : ℝ)) • c + (t : ℝ) • d)

theorem rootHomotopy_degree {n : ℕ} (c d : Fin n → ℂ) (t : Icc (0 : ℝ) 1) :
    (rootHomotopy c d t).degree = n := by
  unfold rootHomotopy
  rw [Polynomial.degree_eq_natDegree (TauCeti.Polynomial.monic_monicOfCoeff _).ne_zero]
  simp only [TauCeti.Polynomial.natDegree_monicOfCoeff]

@[fun_prop] theorem continuous_rootHomotopy_coeff {n : ℕ} (c d : Fin n → ℂ) (k : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) 1 => (rootHomotopy c d t).coeff k) := by
  exact (TauCeti.Polynomial.continuous_coeff_monicOfCoeff k).comp (by fun_prop)

theorem root_norm_le_coefficient_norm_add_one {n : ℕ} (c : Fin n → ℂ)
    {z : ℂ} (hz : (TauCeti.Polynomial.monicOfCoeff c).IsRoot z) :
    ‖z‖ ≤ ‖c‖ + 1 := by
  have hm := TauCeti.Polynomial.monic_monicOfCoeff c
  have hroot := hz.norm_lt_cauchyBound hm.ne_zero
  have hbound : (TauCeti.Polynomial.monicOfCoeff c).cauchyBound ≤ ‖c‖₊ + 1 := by
    rw [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one,
      TauCeti.Polynomial.natDegree_monicOfCoeff]
    refine add_le_add ?_ (le_refl 1)
    apply Finset.sup_le
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    rw [TauCeti.Polynomial.coeff_monicOfCoeff c ⟨k, hk'⟩]
    exact nnnorm_le_pi_nnnorm c ⟨k, hk'⟩
  exact_mod_cast hroot.le.trans hbound

theorem rootHomotopy_root_norm_le {n : ℕ} (c d : Fin n → ℂ) {M : ℝ}
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M) (t : Icc (0 : ℝ) 1)
    {z : ℂ} (hz : (rootHomotopy c d t).IsRoot z) : ‖z‖ ≤ M + 1 := by
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  apply (root_norm_le_coefficient_norm_add_one _ hz).trans
  refine add_le_add ?_ (le_refl 1)
  calc
    ‖(1 - (t : ℝ)) • c + (t : ℝ) • d‖ ≤
        ‖(1 - (t : ℝ)) • c‖ + ‖(t : ℝ) • d‖ := norm_add_le _ _
    _ = (1 - (t : ℝ)) * ‖c‖ + (t : ℝ) * ‖d‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
    _ ≤ (1 - (t : ℝ)) * M + (t : ℝ) * M :=
      add_le_add (mul_le_mul_of_nonneg_left hc ht1) (mul_le_mul_of_nonneg_left hd ht0)
    _ = M := by ring

theorem eval_monicOfCoeff_sub_homotopy {n : ℕ} (c d : Fin n → ℂ)
    (t : Icc (0 : ℝ) 1) (z : ℂ) :
    (TauCeti.Polynomial.monicOfCoeff c).eval z - (rootHomotopy c d t).eval z =
      (t : ℝ) • ∑ i : Fin n, (c i - d i) * z ^ i.val := by
  simp only [rootHomotopy, TauCeti.Polynomial.eval_monicOfCoeff,
    Pi.add_apply, Pi.smul_apply, Complex.real_smul, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

theorem rootHomotopy_initial_eval_bound {n : ℕ} (hn : 0 < n)
    (c d : Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M) (t : Icc (0 : ℝ) 1)
    {z : ℂ} (hz : (rootHomotopy c d t).IsRoot z) :
    ‖(TauCeti.Polynomial.monicOfCoeff c).eval z‖ ≤
      n * (M + 1) ^ (n - 1) * ‖c - d‖ := by
  have hzB := rootHomotopy_root_norm_le c d hc hd t hz
  have hR : 1 ≤ M + 1 := by linarith
  have hval := eval_monicOfCoeff_sub_homotopy c d t z
  rw [hz, sub_zero] at hval
  rw [hval, norm_smul, Real.norm_of_nonneg t.property.1]
  have hs : ‖∑ i : Fin n, (c i - d i) * z ^ i.val‖ ≤
      ∑ i : Fin n, ‖c - d‖ * (M + 1) ^ (n - 1) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i.val ≤ n - 1 := by omega
    apply mul_le_mul (norm_le_pi_norm (c - d) i) ?_ (pow_nonneg (norm_nonneg z) _)
      (norm_nonneg (c - d))
    exact (pow_le_pow_left₀ (norm_nonneg z) hzB _).trans (pow_le_pow_right₀ hR hi')
  have hs' := mul_le_mul_of_nonneg_left hs t.property.1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs'
  apply hs'.trans
  have hnonneg : 0 ≤ (n : ℝ) * (‖c - d‖ * (M + 1) ^ (n - 1)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right t.property.2 hnonneg]

theorem rootHomotopy_root_near_initial {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (c d : Fin n → ℂ)
    (hcP : TauCeti.Polynomial.monicOfCoeff c = realRootPolynomial a)
    {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M)
    (hsmall : n * (M + 1) ^ (n - 1) * ‖c - d‖ < ρ ^ n)
    (t : Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ (rootHomotopy c d t).roots) :
    ∃ i, ‖z - (a i : ℂ)‖ < ρ := by
  have hroot := (Polynomial.mem_roots
    (TauCeti.Polynomial.monic_monicOfCoeff _).ne_zero).mp hz
  have heval := rootHomotopy_initial_eval_bound hn c d hM hc hd t hroot
  rw [hcP, realRootPolynomial, eval_prod] at heval
  simp only [eval_sub, eval_X, eval_C, norm_prod] at heval
  by_contra h
  push_neg at h
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hρ)
    (fun i _ => h i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  exact (not_lt_of_ge (hprod.trans heval)) hsmall

theorem roots_match_of_coefficient_bound {n : ℕ} (hn : 0 < n)
    (a b : Fin n → ℝ) {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (ha : ‖realRootCoefficients a‖ ≤ M) (hb : ‖realRootCoefficients b‖ ≤ M)
    (hsmall : n * (M + 1) ^ (n - 1) *
      ‖realRootCoefficients a - realRootCoefficients b‖ < ρ ^ n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, |a i - b (σ i)| ≤ 2 * n * ρ := by
  apply exists_perm_dist_le_of_polynomial_homotopy a b
    (F := rootHomotopy (realRootCoefficients a) (realRootCoefficients b))
  · intro k hk
    exact continuous_rootHomotopy_coeff _ _ k
  · exact rootHomotopy_degree _ _
  · simp [rootHomotopy, monicOfCoeff_realRootCoefficients, realRootPolynomial]
  · simp [rootHomotopy, monicOfCoeff_realRootCoefficients, realRootPolynomial]
  · exact hρ
  · intro t z hz
    exact rootHomotopy_root_near_initial hn a _ _ (monicOfCoeff_realRootCoefficients a)
      hM hρ ha hb hsmall t hz

end EllipsoidVerification
end
end CanonicalSource4

section CanonicalSource5
/- Source: Ellipsoid/UniformRootRecovery.lean -/



noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem realRootCoefficients_eq_implies_perm {n : ℕ} {a b : Fin n → ℝ}
    (h : realRootCoefficients a = realRootCoefficients b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a i = b (σ i) := by
  have hp : realRootPolynomial a = realRootPolynomial b := by
    rw [← monicOfCoeff_realRootCoefficients a, ← monicOfCoeff_realRootCoefficients b, h]
  have hr := congrArg Polynomial.roots hp
  simp only [realRootPolynomial, Polynomial.roots_prod_X_sub_C_map] at hr
  have hr' : Finset.univ.val.map a = Finset.univ.val.map b := by
    apply Multiset.map_injective Complex.ofReal_injective
    simpa only [Multiset.map_map, Function.comp_def] using hr
  exact exists_perm_of_multiset_map_eq hr'

/-- Uniform root matching with the optimal exponent on every bounded real
root family. This controls multiplicities and imposes no separation of the
roots. The constants depend only on the degree and the root bound. -/
theorem uniform_real_root_holder {n : ℕ} (hn : 0 < n) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : Fin n → ℝ,
      ‖a‖ ≤ B → ‖b‖ ≤ B →
      ∃ σ : Equiv.Perm (Fin n), ∀ i,
        |a i - b (σ i)| ≤ C *
          ‖realRootCoefficients a - realRootCoefficients b‖ ^ (1 / (n : ℝ)) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin n → ℝ) B).exists_bound_of_continuousOn
    (continuous_realRootCoefficients n).continuousOn
  let R := max M 0
  have hR : 0 ≤ R := le_max_right _ _
  have hcoeff (a : Fin n → ℝ) (ha : ‖a‖ ≤ B) : ‖realRootCoefficients a‖ ≤ R :=
    (hM a (by simpa using ha)).trans (le_max_left _ _)
  let H : ℝ := n * (R + 1) ^ (n - 1)
  have hH : 0 < H := mul_pos (Nat.cast_pos.mpr hn) (pow_pos (by linarith) _)
  let C : ℝ := 2 * n * (2 * H) ^ (1 / (n : ℝ))
  have hC : 0 < C := mul_pos (by positivity)
    (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨C, hC, ?_⟩
  intro a b ha hb
  let δ : ℝ := ‖realRootCoefficients a - realRootCoefficients b‖
  by_cases hδ : δ = 0
  · obtain ⟨σ, hσ⟩ := realRootCoefficients_eq_implies_perm
      (sub_eq_zero.mp (norm_eq_zero.mp hδ))
    refine ⟨σ, fun i => ?_⟩
    rw [hσ i, sub_self, abs_zero]
    positivity
  have hδpos : 0 < δ := (norm_nonneg _).lt_of_ne (Ne.symm hδ)
  let ρ : ℝ := (2 * H * δ) ^ (1 / (n : ℝ))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hρpow : ρ ^ n = 2 * H * δ := by
    have hbase : 0 ≤ 2 * H * δ := by positivity
    simpa only [ρ, one_div] using Real.rpow_inv_natCast_pow hbase hn.ne'
  obtain ⟨σ, hσ⟩ := roots_match_of_coefficient_bound hn a b hR hρ.le
    (hcoeff a ha) (hcoeff b hb) (by
      change H * δ < ρ ^ n
      rw [hρpow]
      nlinarith [mul_pos hH hδpos])
  refine ⟨σ, fun i => (hσ i).trans_eq ?_⟩
  change 2 * n * (2 * H * δ) ^ (1 / (n : ℝ)) =
    (2 * n * (2 * H) ^ (1 / (n : ℝ))) * δ ^ (1 / (n : ℝ))
  rw [Real.mul_rpow (by positivity) hδpos.le]
  ring

end EllipsoidVerification
end
end CanonicalSource5

section CanonicalSource6
/- Source: Ellipsoid/CoefficientVolumeBounds.lean -/



noncomputable section

open Polynomial Set
open scoped BigOperators

namespace EllipsoidVerification

theorem FullEllipsoid.volume_error_le {n : ℕ} (E F : FullEllipsoid n) (k : Fin n) :
    |E.volume (k.val + 1) - F.volume (k.val + 1)| ≤ E.volumeDistance F := by
  unfold FullEllipsoid.volumeDistance
  exact le_ciSup (f := fun k : Fin n =>
    |E.volume (k.val + 1) - F.volume (k.val + 1)|) (Set.finite_range _).bddAbove k

theorem FullEllipsoid.volumeDistance_nonneg {n : ℕ} (hn : 0 < n)
    (E F : FullEllipsoid n) : 0 ≤ E.volumeDistance F :=
  (abs_nonneg _).trans (E.volume_error_le F ⟨0, hn⟩)

theorem FullEllipsoid.axisDistance_le_of_perm {n : ℕ} (E F : FullEllipsoid n)
    (σ : Equiv.Perm (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (hσ : ∀ i, |E.semiaxis i - F.semiaxis (σ i)| ≤ C) : E.axisDistance F ≤ C := by
  apply (ciInf_le (Set.finite_range _).bddBelow σ).trans
  exact Real.iSup_le hσ hC

theorem axisCoefficientData_reconstruct {m : ℕ} (a : Fin (m + 1) → ℝ) :
    fixedEndpoints m 1 (axisCoefficientData a).2 (axisCoefficientData a).1 =
      axisCoefficients a := by
  simpa only [axisCoefficientData, axisCoefficients_zero] using
    fixedEndpoints_internalCoefficients m (axisCoefficients a)

theorem realRootCoefficients_squared_axes {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    realRootCoefficients (fun j => a j ^ 2) i =
      (((-1 : ℝ) ^ (n - i.val)) * axisCoefficients a ⟨n - i.val, by omega⟩ : ℝ) := by
  have hp : realRootPolynomial (fun j => a j ^ 2) =
      (∏ j : Fin n, (X + C (-(a j ^ 2)) : ℝ[X])).map Complex.ofRealHom := by
    simp [realRootPolynomial, Polynomial.map_prod, sub_eq_add_neg]
  rw [realRootCoefficients, hp, Polynomial.coeff_map]
  have h := coeff_prod_X_add_C (Finset.univ : Finset (Fin n)) (fun j => -(a j ^ 2))
    (k := n - i.val) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_sub_self i.isLt.le] at h
  rw [h]
  have hs := elementaryOn_scaling (Finset.univ : Finset (Fin n)) (fun j => a j ^ 2)
    (-1) (n - i.val)
  simpa only [neg_one_mul, elementaryOn, axisCoefficients, axisCoefficientPolynomial,
    Complex.ofRealHom_eq_coe] using
    congrArg (fun x : ℝ => (x : ℂ)) hs

theorem rootCoefficients_squared_axes_bound {m : ℕ} (a b : Fin (m + 1) → ℝ) :
    ‖realRootCoefficients (fun i => a i ^ 2) - realRootCoefficients (fun i => b i ^ 2)‖ ≤
      ‖axisCoefficientData a - axisCoefficientData b‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [Pi.sub_apply, realRootCoefficients_squared_axes, realRootCoefficients_squared_axes,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub,
    abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  by_cases hi : i.val = 0
  · have heq : (⟨m + 1 - i.val, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_last]
      omega
    rw [heq]
    exact (norm_snd_le (axisCoefficientData a - axisCoefficientData b))
  · let j : Fin m := ⟨m - i.val, by omega⟩
    have heq : (⟨m + 1 - i.val, by omega⟩ : Fin (m + 2)) =
        ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [heq]
    exact (norm_le_pi_norm ((axisCoefficientData a - axisCoefficientData b).1) j).trans
      (norm_fst_le _)

def volumeCoefficientBound (n : ℕ) (b : ℝ) : ℝ :=
  (∑ k : Fin n, (unitBallVolume (k.val + 1))⁻¹) +
    2 * b ^ n / unitBallVolume n + 1

theorem volumeCoefficientBound_pos {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    0 < volumeCoefficientBound n b := by
  have hs : 0 ≤ ∑ k : Fin n, (unitBallVolume (k.val + 1))⁻¹ :=
    Finset.sum_nonneg fun k _ => inv_nonneg.mpr (unitBallVolume_pos _).le
  have ht : 0 ≤ 2 * b ^ n / unitBallVolume n :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb n)) (unitBallVolume_pos n).le
  dsimp [volumeCoefficientBound]
  linarith

theorem volumeCoefficientBound_ge_inv {n : ℕ} {b : ℝ} (hb : 0 ≤ b) (k : Fin n) :
    (unitBallVolume (k.val + 1))⁻¹ ≤ volumeCoefficientBound n b := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      inv_nonneg.mpr (unitBallVolume_pos (j.val + 1)).le) (Finset.mem_univ k)
  have ht : 0 ≤ 2 * b ^ n / unitBallVolume n :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb n)) (unitBallVolume_pos n).le
  dsimp [volumeCoefficientBound]
  linarith

theorem volumeCoefficientBound_ge_top {n : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    2 * b ^ n / unitBallVolume n ≤ volumeCoefficientBound n b := by
  have hs : 0 ≤ ∑ k : Fin n, (unitBallVolume (k.val + 1))⁻¹ :=
    Finset.sum_nonneg fun k _ => inv_nonneg.mpr (unitBallVolume_pos _).le
  dsimp [volumeCoefficientBound]
  linarith

theorem FullEllipsoid.semiaxis_prod_le {n : ℕ} (E : FullEllipsoid n) {b : ℝ}
    (hb : ∀ i, E.semiaxis i ≤ b) : (∏ i, E.semiaxis i) ≤ b ^ n := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : Fin n => b)
      (fun i _ => (E.semiaxis_pos i).le) (fun i _ => hb i)

/-- The augmented coefficient output is controlled by the exact intrinsic
volume discrepancy, with a constant depending only on dimension and the
upper semiaxis bound. -/
theorem augmentedCoefficientMap_axisData_volume_bound {m : ℕ}
    (E F : FullEllipsoid (m + 1)) {b : ℝ} (hb : 0 ≤ b)
    (hE : ∀ i, E.semiaxis i ≤ b) (hF : ∀ i, F.semiaxis i ≤ b) :
    ‖augmentedCoefficientMap m (axisCoefficientData E.semiaxis) -
      augmentedCoefficientMap m (axisCoefficientData F.semiaxis)‖ ≤
      volumeCoefficientBound (m + 1) b * E.volumeDistance F := by
  have hD := E.volumeDistance_nonneg (by omega) F
  have hM := (volumeCoefficientBound_pos (n := m + 1) hb).le
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hD)).mpr
    intro k
    change |coefficientTransform (fixedEndpoints m 1 _ _) (k.val + 1) -
      coefficientTransform (fixedEndpoints m 1 _ _) (k.val + 1)| ≤ _
    rw [axisCoefficientData_reconstruct, axisCoefficientData_reconstruct]
    have hEvol := E.volume_eq_coefficientTransform (k := k.val + 1) (by omega) (by omega)
    have hFvol := F.volume_eq_coefficientTransform (k := k.val + 1) (by omega) (by omega)
    have hscale : |coefficientTransform (axisCoefficients E.semiaxis) (k.val + 1) -
        coefficientTransform (axisCoefficients F.semiaxis) (k.val + 1)| =
        (unitBallVolume (k.val + 1))⁻¹ *
          |E.volume (k.val + 1) - F.volume (k.val + 1)| := by
      rw [hEvol, hFvol, ← mul_sub, abs_mul,
        abs_of_pos (unitBallVolume_pos (k.val + 1))]
      field_simp [(unitBallVolume_pos (k.val + 1)).ne']
    rw [hscale]
    exact mul_le_mul
      (volumeCoefficientBound_ge_inv (n := m + 1) hb ⟨k.val, by omega⟩)
      (E.volume_error_le F (⟨k.val, by omega⟩ : Fin (m + 1))) (abs_nonneg _) hM
  · change |axisCoefficients E.semiaxis (Fin.last (m + 1)) -
        axisCoefficients F.semiaxis (Fin.last (m + 1))| ≤ _
    rw [axisCoefficients_last, axisCoefficients_last]
    let u := ∏ i, E.semiaxis i
    let v := ∏ i, F.semiaxis i
    have hu : 0 < u := Finset.prod_pos fun i _ => E.semiaxis_pos i
    have hv : 0 < v := Finset.prod_pos fun i _ => F.semiaxis_pos i
    have huB := E.semiaxis_prod_le hE
    have hvB := F.semiaxis_prod_le hF
    have hdiff : |u - v| ≤ E.volumeDistance F / unitBallVolume (m + 1) := by
      apply (le_div_iff₀ (unitBallVolume_pos (m + 1))).mpr
      have h := E.volume_error_le F (Fin.last m)
      simp only [Fin.val_last] at h
      rw [E.volume_top (by omega), F.volume_top (by omega), ← mul_sub,
        abs_mul, abs_of_pos (unitBallVolume_pos (m + 1))] at h
      simpa only [mul_comm] using h
    calc
      |u ^ 2 - v ^ 2| = |u - v| * (u + v) := by
        rw [sq_sub_sq, abs_mul, abs_of_pos (add_pos hu hv)]
        ring
      _ ≤ (E.volumeDistance F / unitBallVolume (m + 1)) * (2 * b ^ (m + 1)) :=
        mul_le_mul hdiff (by dsimp [u, v]; linarith) (add_pos hu hv).le
          (div_nonneg hD (unitBallVolume_pos (m + 1)).le)
      _ = (2 * b ^ (m + 1) / unitBallVolume (m + 1)) * E.volumeDistance F := by ring
      _ ≤ volumeCoefficientBound (m + 1) b * E.volumeDistance F :=
        mul_le_mul_of_nonneg_right (volumeCoefficientBound_ge_top hb) hD

end EllipsoidVerification
end
end CanonicalSource6

section CanonicalSource7
/- Source: Ellipsoid/UniformHolderTheorem.lean -/



noncomputable section

open Set
open scoped BigOperators

namespace EllipsoidVerification

/-- The exact quantitative assertion of Theorem 1.2. The coefficient inverse
estimate and the multiplicity-preserving polynomial root bound are both
proved dependencies; no separation of semiaxes is assumed. -/
theorem uniform_holder_recovery : UniformHolderRecovery := by
  intro n hn a b ha hab
  cases n with
  | zero => omega
  | succ m =>
    have hb : 0 < b := ha.trans_le hab
    obtain ⟨L, hL, hcoeff⟩ := axisCoefficientData_inverse_lipschitz m ha hab
    obtain ⟨R, hR, hroots⟩ := uniform_real_root_holder (n := m + 1) (by omega)
      (b ^ 2) (sq_nonneg b)
    let M := volumeCoefficientBound (m + 1) b
    have hM : 0 < M := volumeCoefficientBound_pos hb.le
    let η : ℝ := 1 / (m + 1 : ℕ)
    have hη : 0 < η := one_div_pos.mpr (by positivity)
    let C : ℝ := R * (L * M) ^ η / (2 * a)
    have hC : 0 < C := div_pos
      (mul_pos hR (Real.rpow_pos_of_pos (mul_pos hL hM) _)) (by positivity)
    refine ⟨C, hC, ?_⟩
    intro E F hE hF
    have hEbox : E.semiaxis ∈ Icc (fun _ => a) (fun _ => b) :=
      ⟨fun i => (hE i).1, fun i => (hE i).2⟩
    have hFbox : F.semiaxis ∈ Icc (fun _ => a) (fun _ => b) :=
      ⟨fun i => (hF i).1, fun i => (hF i).2⟩
    have hnormE : ‖fun i => E.semiaxis i ^ 2‖ ≤ b ^ 2 := by
      apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).mpr
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [E.semiaxis_pos i, (hE i).2]
    have hnormF : ‖fun i => F.semiaxis i ^ 2‖ ≤ b ^ 2 := by
      apply (pi_norm_le_iff_of_nonneg (sq_nonneg b)).mpr
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [F.semiaxis_pos i, (hF i).2]
    have hD := E.volumeDistance_nonneg (by omega) F
    have hfull : ‖realRootCoefficients (fun i => E.semiaxis i ^ 2) -
        realRootCoefficients (fun i => F.semiaxis i ^ 2)‖ ≤
        L * M * E.volumeDistance F := by
      calc
        _ ≤ ‖axisCoefficientData E.semiaxis - axisCoefficientData F.semiaxis‖ :=
          rootCoefficients_squared_axes_bound _ _
        _ ≤ L * ‖augmentedCoefficientMap m (axisCoefficientData E.semiaxis) -
            augmentedCoefficientMap m (axisCoefficientData F.semiaxis)‖ :=
          hcoeff _ _ hEbox hFbox
        _ ≤ L * (M * E.volumeDistance F) := mul_le_mul_of_nonneg_left
          (augmentedCoefficientMap_axisData_volume_bound E F hb.le
            (fun i => (hE i).2) (fun i => (hF i).2)) hL.le
        _ = _ := by ring
    obtain ⟨σ, hσ⟩ := hroots (fun i => E.semiaxis i ^ 2)
      (fun i => F.semiaxis i ^ 2) hnormE hnormF
    have hroot (i : Fin (m + 1)) :
        |E.semiaxis i ^ 2 - F.semiaxis (σ i) ^ 2| ≤
          R * (L * M) ^ η * (E.volumeDistance F) ^ η := by
      apply (hσ i).trans
      calc
        _ ≤ R * (L * M * E.volumeDistance F) ^ η :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hfull hη.le) hR.le
        _ = _ := by rw [Real.mul_rpow (mul_pos hL hM).le hD]; ring
    apply E.axisDistance_le_of_perm F σ (mul_nonneg hC.le (Real.rpow_nonneg hD _))
    intro i
    have hsum : 2 * a ≤ E.semiaxis i + F.semiaxis (σ i) := by
      linarith [(hE i).1, (hF (σ i)).1]
    have hfactor : |E.semiaxis i ^ 2 - F.semiaxis (σ i) ^ 2| =
        |E.semiaxis i - F.semiaxis (σ i)| * (E.semiaxis i + F.semiaxis (σ i)) := by
      rw [sq_sub_sq, abs_mul, abs_of_pos (add_pos (E.semiaxis_pos i) (F.semiaxis_pos (σ i)))]
      ring
    have hsmall : |E.semiaxis i - F.semiaxis (σ i)| * (2 * a) ≤
        R * (L * M) ^ η * (E.volumeDistance F) ^ η := by
      calc
        _ ≤ |E.semiaxis i - F.semiaxis (σ i)| *
            (E.semiaxis i + F.semiaxis (σ i)) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = _ := hfactor.symm
        _ ≤ _ := hroot i
    have h := (le_div_iff₀ (show 0 < 2 * a by positivity)).mpr hsmall
    simpa only [C, η, div_mul_eq_mul_div] using h

end EllipsoidVerification
end
end CanonicalSource7
