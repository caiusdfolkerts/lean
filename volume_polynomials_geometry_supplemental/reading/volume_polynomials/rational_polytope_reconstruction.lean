module

public import VolumePolynomials.ComputableFinitePaths
public import VolumePolynomials.RationalHausdorff
public import VolumePolynomials.RationalRejection
public import VolumePolynomials.CoefficientMap
public import VolumePolynomials.BoundedRealization
public import Mathlib.Logic.Encodable.Pi

@[expose] public section
set_option autoImplicit false

/-!
# Reconstruction by finite rational polytope paths

All finite states, adjacency tests, coefficient tests, and selected outputs are
computed from rational data. The geometric interpretation is the actual convex
hull of each output vertex list. Prefix stabilization proves convergence of the
entire output sequence whenever every finite level is nonempty. No rate of
convergence is claimed or used.
-/

open Set Filter Metric
open scoped BigOperators Topology

namespace VolumePolynomials.RationalReconstruction

open RationalHulls RationalCoefficientNets

/-- A wrapper gives finite rational tuples a fixed computable linear order. -/
structure State (n d : ℕ) where
  vertices : Fin n → List (RationalPoint d)
  deriving DecidableEq

instance stateEncodable (n d : ℕ) : Encodable (State n d) :=
  Encodable.ofEquiv (Fin n → List (RationalPoint d))
    { toFun := State.vertices
      invFun := State.mk
      left_inv := fun s => by cases s; rfl
      right_inv := fun _ => rfl }

instance stateLinearOrder (n d : ℕ) : LinearOrder (State n d) :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

instance stateInhabited (n d : ℕ) : Inhabited (State n d) := ⟨⟨fun _ => [0]⟩⟩

noncomputable def stateBodies {n d : ℕ} (s : State n d) : Fin n → Body d :=
  fun i => if h : 0 ∈ s.vertices i then body (s.vertices i) h else 0

theorem stateBodies_eq {n d : ℕ} (s : State n d) (h : ∀ i, 0 ∈ s.vertices i) :
    stateBodies s = fun i => body (s.vertices i) (h i) := by
  first
  | funext i
    simp only [stateBodies, dif_pos (h i)]

def stage (j : ℕ) : ℕ := 2 ^ (j + 2)

def tolerance (j : ℕ) : ℚ := samplingTolerance (stage j)

def dyadic (j : ℕ) : ℚ := (1 / 2) ^ (j + 2)

def edgeRadius (j : ℕ) : ℚ := 3 * dyadic (j + 1)

noncomputable def tailRadius (j : ℕ) : ℝ := 3 * (dyadic j : ℝ)

theorem tolerance_pos (j : ℕ) : 0 < tolerance j := samplingTolerance_pos _

theorem dyadic_pos (j : ℕ) : 0 < dyadic j := by unfold dyadic; positivity

theorem dyadic_succ (j : ℕ) : dyadic (j + 1) = dyadic j / 2 := by
  first
  | unfold dyadic
    rw [show j + 1 + 2 = (j + 2) + 1 by omega, pow_succ]
    ring

theorem tolerance_le_dyadic (j : ℕ) : tolerance j ≤ dyadic j := by
  first
  | have hp : (0 : ℚ) < 2 ^ (j + 2) := by positivity
    have h := one_div_le_one_div_of_le hp (le_add_of_nonneg_right (by norm_num : (0 : ℚ) ≤ 1))
    simpa only [tolerance, samplingTolerance, stage, Nat.cast_pow, Nat.cast_ofNat,
      dyadic, one_div, inv_pow] using h

theorem dyadic_tendsto : Tendsto (fun j => (dyadic j : ℝ)) atTop (𝓝 0) := by
  first
  | have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
      ((1 / 2 : ℝ) ^ 2)
    simpa only [dyadic, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      pow_add, zero_mul] using h

theorem tolerance_tendsto : Tendsto (fun j => (tolerance j : ℝ)) atTop (𝓝 0) := by
  first
  | apply squeeze_zero (fun j => by exact_mod_cast (tolerance_pos j).le)
      (fun j => by exact_mod_cast tolerance_le_dyadic j) dyadic_tendsto

theorem edgeRadius_nonneg (j : ℕ) : 0 ≤ edgeRadius j := by
  first
  | exact mul_nonneg (by norm_num) (dyadic_pos _).le

theorem tailRadius_nonneg (j : ℕ) : 0 ≤ tailRadius j := by
  first
  | unfold tailRadius
    have h : 0 ≤ (dyadic j : ℝ) := by exact_mod_cast (dyadic_pos j).le
    positivity

theorem tailRadius_tendsto : Tendsto tailRadius atTop (𝓝 0) := by
  first
  | change Tendsto (fun j => 3 * (dyadic j : ℝ)) atTop (𝓝 0)
    simpa only [mul_zero] using dyadic_tendsto.const_mul 3

theorem edgeRadius_eq_tail_sub (j : ℕ) :
    (edgeRadius j : ℝ) = tailRadius j - tailRadius (j + 1) := by
  first
  | have h : (dyadic (j + 1) : ℝ) = (dyadic j : ℝ) / 2 := by
      exact_mod_cast dyadic_succ j
    simp only [edgeRadius, Rat.cast_mul, Rat.cast_ofNat, tailRadius]
    linarith

theorem tolerance_add_le_edgeRadius (j : ℕ) :
    tolerance j + tolerance (j + 1) ≤ edgeRadius j := by
  first
  | have h₁ := tolerance_le_dyadic j
    have h₂ := tolerance_le_dyadic (j + 1)
    have h₃ := dyadic_succ j
    unfold edgeRadius
    linarith

def sampledCoefficients {n d : ℕ} (j : ℕ) (s : State n d) : MultiIndex n d → ℚ :=
  approximateCoefficients s.vertices (tolerance j) (tolerance_pos j)

def coefficientTest (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ)
    (j : ℕ) (s : State n d) : Prop :=
  ∀ α, |sampledCoefficients j s α - a (stage j) α| ≤ coordinateBudget n d R * tolerance j

instance coefficientTest_decidable (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ)
    (j : ℕ) (s : State n d) : Decidable (coefficientTest n d R a j s) := by
  first
  | unfold coefficientTest
    infer_instance

/-- A finite list computed by rational inequalities and rational volume search. -/
def states (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ) (j : ℕ) : List (State n d) :=
  ((candidateTuples n d R (resolution n d (stage j))).map State.mk).filter
    (coefficientTest n d R a j)

theorem mem_states {n d R j : ℕ} (a : ℕ → MultiIndex n d → ℚ) (s : State n d) :
    s ∈ states n d R a j ↔
      s.vertices ∈ candidateTuples n d R (resolution n d (stage j)) ∧
      coefficientTest n d R a j s := by
  first
  | cases s
    simp [states]

theorem state_contains_zero {n d R j : ℕ} {a : ℕ → MultiIndex n d → ℚ}
    {s : State n d} (hs : s ∈ states n d R a j) (i : Fin n) : 0 ∈ s.vertices i :=
  (Iff.mp (mem_candidates _) (Iff.mp (mem_candidateTuples _) (Iff.mp (mem_states a s) hs).1 i)).2

theorem state_bounded {n d R j : ℕ} {a : ℕ → MultiIndex n d → ℚ}
    {s : State n d} (hs : s ∈ states n d R a j) (i : Fin n) :
    (stateBodies s i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) := by
  first
  | rw [stateBodies_eq s (state_contains_zero hs)]
    exact candidate_bounded _ (Iff.mp (mem_candidateTuples _) (Iff.mp (mem_states a s) hs).1 i)

def edge {n d : ℕ} (j : ℕ) (s t : State n d) : Prop :=
  tupleHausdorffTest s.vertices t.vertices (edgeRadius j)

instance edge_decidable {n d : ℕ} (j : ℕ) : DecidableRel (@edge n d j) := by
  first
  | intro s t
    unfold edge
    infer_instance

theorem edge_distance {n d R j : ℕ} {a : ℕ → MultiIndex n d → ℚ}
    {s t : State n d} (hs : s ∈ states n d R a j)
    (ht : t ∈ states n d R a (j + 1)) (hst : edge j s t) :
    dist (stateBodies t) (stateBodies s) ≤ tailRadius j - tailRadius (j + 1) := by
  first
  | rw [← edgeRadius_eq_tail_sub, dist_comm,
      stateBodies_eq s (state_contains_zero hs), stateBodies_eq t (state_contains_zero ht)]
    exact Iff.mp (tupleHausdorffTest_correct _ _ (state_contains_zero hs) (state_contains_zero ht)
      (edgeRadius j) (edgeRadius_nonneg j)) hst

noncomputable def coefficientError (n d R j : ℕ) : ℝ :=
  ((coefficientExtractionBound n d + coordinateBudget n d R + 1 : ℚ) : ℝ) * (tolerance j : ℝ)

theorem coefficientError_nonneg (n d R j : ℕ) : 0 ≤ coefficientError n d R j := by
  first
  | have hE : 0 ≤ (coefficientExtractionBound n d : ℝ) := by
      exact_mod_cast coefficientExtractionBound_nonneg n d
    have hB : 0 ≤ (coordinateBudget n d R : ℝ) := by
      exact_mod_cast (coordinateBudget_pos n d R).le
    have he : 0 ≤ (tolerance j : ℝ) := by exact_mod_cast (tolerance_pos j).le
    simp only [coefficientError, Rat.cast_add, Rat.cast_one]
    positivity

theorem coefficientError_tendsto (n d R : ℕ) :
    Tendsto (coefficientError n d R) atTop (𝓝 0) := by
  first
  | change Tendsto (fun j =>
      (((coefficientExtractionBound n d + coordinateBudget n d R + 1 : ℚ) : ℝ)) *
        (tolerance j : ℝ)) atTop (𝓝 0)
    simpa only [mul_zero] using tolerance_tendsto.const_mul
      (((coefficientExtractionBound n d + coordinateBudget n d R + 1 : ℚ) : ℝ))

theorem state_coefficient_error {n d R j : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    {s : State n d} (hs : s ∈ states n d R a j) :
    dist (coefficientMap (stateBodies s)) c ≤ coefficientError n d R j := by
  first
  | apply (dist_pi_le_iff (coefficientError_nonneg n d R j)).mpr
    intro α
    have hzero := state_contains_zero hs
    have hreal : Realizes (fun i => body (s.vertices i) (hzero i))
        (coefficientMap (stateBodies s)) := by
      rw [← stateBodies_eq s hzero]
      exact coefficientMap_realizes _
    have happ := approximateCoefficients_correct s.vertices hzero hreal
      (tolerance j) (tolerance_pos j) α
    have htest : |(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| ≤
        (coordinateBudget n d R : ℝ) * (tolerance j : ℝ) := by
      exact_mod_cast (Iff.mp (mem_states a s) hs).2 α
    have hname : |c α - (a (stage j) α : ℝ)| ≤ (tolerance j : ℝ) := ha (stage j) α
    have hname' : |(a (stage j) α : ℝ) - c α| ≤ (tolerance j : ℝ) := by
      simpa only [abs_sub_comm] using hname
    change |coefficientMap (stateBodies s) α - c α| ≤ _
    calc
      _ ≤ |coefficientMap (stateBodies s) α - (sampledCoefficients j s α : ℝ)| +
          |(sampledCoefficients j s α : ℝ) - c α| := abs_sub_le _ _ _
      _ ≤ (coefficientExtractionBound n d : ℝ) * (tolerance j : ℝ) +
          (|(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| +
            |(a (stage j) α : ℝ) - c α|) := by
        apply add_le_add
        · simpa only [sampledCoefficients, abs_sub_comm] using happ
        · exact abs_sub_le _ _ _
      _ ≤ (coefficientExtractionBound n d : ℝ) * (tolerance j : ℝ) +
          ((coordinateBudget n d R : ℝ) * (tolerance j : ℝ) + (tolerance j : ℝ)) := by
        exact add_le_add le_rfl (add_le_add htest hname')
      _ = coefficientError n d R j := by
        simp only [coefficientError, Rat.cast_add, Rat.cast_one]
        ring

/-- Every actual bounded realization supplies an accepted state at each scale,
with the stated Hausdorff approximation to that same tuple. -/
theorem exists_state_near {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (K : Fin n → Body d)
    (hK : ∀ i, (0 : Space d) ∈ K i ∧
      (K i : Set (Space d)) ⊆ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))
    (hc : Realizes K c) (j : ℕ) :
    ∃ s ∈ states n d R a j, dist K (stateBodies s) ≤ (tolerance j : ℝ) := by
  first
  | classical
    choose L hL hdist using fun i => exists_candidate_near
      (R := R) (k := resolution n d (stage j)) (K i) (hK i).1 (hK i).2
    let s : State n d := ⟨L⟩
    have hzero : ∀ i, 0 ∈ L i := fun i => (Iff.mp (mem_candidates _) (hL i)).2
    let P := fun i => body (L i) (hzero i)
    have hsP : stateBodies s = P := stateBodies_eq s hzero
    have hreal := coefficientMap_realizes P
    have hstate : coefficientTest n d R a j s := by
      intro α
      have hg := hc.coefficient_sub_le_of_dist_le hreal (R : ℚ) (by positivity)
        (fun i => (hK i).2) (fun i => candidate_bounded (L i) (hL i))
        (by positivity : 0 ≤ 1 / ((resolution n d (stage j) : ℝ) + 1))
        (resolution_bounds n d (stage j)).2 hdist α
      have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
        exact_mod_cast coefficientModulus_nonneg n d R
      have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (resolution_bounds n d (stage j)).1 hC)
      have happ := approximateCoefficients_correct L hzero hreal
        (tolerance j) (tolerance_pos j) α
      have hname : |c α - (a (stage j) α : ℝ)| ≤ (tolerance j : ℝ) := ha (stage j) α
      have htri₁ := abs_sub_le ((sampledCoefficients j s α : ℚ) : ℝ)
        (coefficientMap P α) (a (stage j) α : ℝ)
      have htri₂ := abs_sub_le (coefficientMap P α) (c α) (a (stage j) α : ℝ)
      rw [abs_sub_comm (coefficientMap P α) (c α)] at htri₂
      have hbound : |(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| ≤
          (coordinateBudget n d R : ℝ) * (tolerance j : ℝ) := by
        simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
        change |(sampledCoefficients j s α : ℝ) - (a (stage j) α : ℝ)| ≤ _
        change |(sampledCoefficients j s α : ℝ) - coefficientMap P α| ≤ _ at happ
        change |c α - coefficientMap P α| ≤ (tolerance j : ℝ) * _ at hg'
        nlinarith
      exact_mod_cast hbound
    refine ⟨s, Iff.mpr (mem_states a s) ⟨Iff.mpr (mem_candidateTuples L) hL, hstate⟩, ?_⟩
    rw [hsP]
    apply (dist_pi_le_iff (by exact_mod_cast (tolerance_pos j).le)).mpr
    intro i
    exact (hdist i).trans (resolution_bounds n d (stage j)).1

/-- A realization supplies a compatible infinite sequence of finite states;
this is a proof of nonemptiness, not a choice used by the program. -/
theorem all_paths_nonempty_of_bounded_realization {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hc : c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))) :
    ∀ h, Nonempty (ComputableFinitePaths.Path (states n d R a) edge h) := by
  first
  | classical
    obtain ⟨K, hK, hreal⟩ := hc
    choose s hs hdist using fun j => exists_state_near ha K hK hreal j
    have he : ∀ j, edge j (s j) (s (j + 1)) := by
      intro j
      apply Iff.mpr (tupleHausdorffTest_correct _ _ (state_contains_zero (hs j))
        (state_contains_zero (hs (j + 1))) (edgeRadius j) (edgeRadius_nonneg j))
      rw [← stateBodies_eq (s j) (state_contains_zero (hs j)),
        ← stateBodies_eq (s (j + 1)) (state_contains_zero (hs (j + 1)))]
      have htri := dist_triangle (stateBodies (s j)) K (stateBodies (s (j + 1)))
      have hnear : dist (stateBodies (s j)) (stateBodies (s (j + 1))) ≤
          (tolerance j : ℝ) + (tolerance (j + 1) : ℝ) := by
        apply htri.trans
        exact add_le_add (by simpa only [dist_comm] using hdist j) (hdist (j + 1))
      exact hnear.trans (by exact_mod_cast tolerance_add_le_edgeRadius j)
    exact ComputableFinitePaths.paths_nonempty_of_sequence _ _ s hs he

/-- Literal finite rational output, including a finite rejection marker. -/
def output (n d R : ℕ) (a : ℕ → MultiIndex n d → ℚ) (h : ℕ) : Option (State n d) :=
  ComputableFinitePaths.output (states n d R a) edge h

theorem output_converges_of_all_paths {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hp : ∀ h, Nonempty (ComputableFinitePaths.Path (states n d R a) edge h)) :
    ∃ K : Fin n → Body d,
      Tendsto (fun h => stateBodies ((output n d R a h).getD default)) atTop (𝓝 K) ∧
      Realizes K c := by
  first
  | letI := hp
    obtain ⟨K, hK, hc⟩ := ComputableFinitePaths.output_converges
      (states n d R a) edge stateBodies coefficientMap (continuous_coefficientMap n d) c
      tailRadius (coefficientError n d R) tailRadius_nonneg tailRadius_tendsto
      (coefficientError_tendsto n d R)
      (fun _ _ hs _ ht he => edge_distance hs ht he)
      (fun _ _ hs => state_coefficient_error ha hs)
    refine ⟨K, hK, ?_⟩
    rw [← hc]
    exact coefficientMap_realizes K

/-- Every failure of realization eventually makes a finite path level empty. -/
theorem exists_rejection_of_not_realizable {n d R : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hc : c ∉ VolumeLocus n d) : ∃ h, output n d R a h = none := by
  first
  | classical
    by_contra h
    have hp : ∀ h, Nonempty (ComputableFinitePaths.Path (states n d R a) edge h) := by
      intro k
      have hne : ¬IsEmpty (ComputableFinitePaths.Path (states n d R a) edge k) := by
        intro he
        exact h ⟨k, Iff.mpr (ComputableFinitePaths.output_eq_none_iff _ _ k) he⟩
      exact not_isEmpty_iff.mp hne
    obtain ⟨K, _, hK⟩ := output_converges_of_all_paths ha hp
    exact hc ⟨K, hK⟩

/-- A rational bound read at the first input precision. -/
def inputBound {n d : ℕ} (a : ℕ → MultiIndex n d → ℚ) : ℚ :=
  ∑ α, (|a 0 α| + 1)

def inputRadius (n d : ℕ) (a : ℕ → MultiIndex n d → ℚ) : ℕ :=
  ⌈(d : ℚ) * (inputBound a + 1)⌉₊

theorem inputBound_nonneg {n d : ℕ} (a : ℕ → MultiIndex n d → ℚ) : 0 ≤ inputBound a :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem sum_le_inputBound {n d : ℕ} {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a) :
    (∑ α, c α) ≤ (inputBound a : ℝ) := by
  first
  | simp only [inputBound, Rat.cast_sum, Rat.cast_add, Rat.cast_abs, Rat.cast_one]
    apply Finset.sum_le_sum
    intro α _
    have h := (abs_le.mp (ha 0 α)).2
    have ha₀ := le_abs_self (a 0 α : ℝ)
    norm_num [RationalCertificates.precision] at h
    linarith

theorem realizable_mem_input_box {n d : ℕ} (hd : 0 < d) {c : Coefficients n d}
    {a : ℕ → MultiIndex n d → ℚ} (ha : RationalCertificates.IsName c a)
    (hc : c ∈ VolumeLocus n d) :
    c ∈ boundedVolumeLocus n d
      (Icc (fun _ => -(inputRadius n d a : ℝ)) (fun _ => (inputRadius n d a : ℝ))) := by
  first
  | apply bounded_realization_of_sum_le_of_radius_le hd hc
      (by exact_mod_cast inputBound_nonneg a) (sum_le_inputBound ha)
    exact_mod_cast Nat.le_ceil ((d : ℚ) * (inputBound a + 1))

/-- The reconstruction algorithm computes its ambient radius from the input. -/
def reconstruct (n d : ℕ) (a : ℕ → MultiIndex n d → ℚ) (h : ℕ) : Option (State n d) :=
  output n d (inputRadius n d a) a h

theorem reconstruct_ne_none_of_realizable {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} {a : ℕ → MultiIndex n d → ℚ}
    (ha : RationalCertificates.IsName c a) (hc : c ∈ VolumeLocus n d) (h : ℕ) :
    reconstruct n d a h ≠ none := by
  first
  | have hp := all_paths_nonempty_of_bounded_realization ha (realizable_mem_input_box hd ha hc) h
    intro hn
    have hi := Iff.mp (ComputableFinitePaths.output_eq_none_iff _ _ h) hn
    obtain ⟨p⟩ := hp
    exact hi.false p

theorem reconstruction_converges {n d : ℕ} (hd : 0 < d)
    {c : Coefficients n d} {a : ℕ → MultiIndex n d → ℚ}
    (ha : RationalCertificates.IsName c a) (hc : c ∈ VolumeLocus n d) :
    ∃ K : Fin n → Body d,
      Tendsto (fun h => stateBodies ((reconstruct n d a h).getD default)) atTop (𝓝 K) ∧
      Realizes K c :=
  output_converges_of_all_paths ha
    (all_paths_nonempty_of_bounded_realization ha (realizable_mem_input_box hd ha hc))

theorem reconstruct_some_is_rational_polytope {n d : ℕ}
    (a : ℕ → MultiIndex n d → ℚ) {h : ℕ} {s : State n d}
    (hs : reconstruct n d a h = some s) :
    ∀ i, 0 ∈ s.vertices i ∧ (stateBodies s i : Set (Space d)) = hull (s.vertices i) := by
  first
  | have hm : s ∈ states n d (inputRadius n d a) a h := by
      unfold reconstruct output ComputableFinitePaths.output at hs
      split_ifs at hs with hp
      · have heq : ((ComputableFinitePaths.paths (states n d (inputRadius n d a) a) edge h).min' hp).getD h default = s :=
          Option.some.inj hs
        rw [← heq]
        exact (Iff.mp (ComputableFinitePaths.mem_paths _ _ _ _) (Finset.min'_mem _ _)).2.1
          ⟨h, Nat.lt_succ_self h⟩
    intro i
    refine ⟨state_contains_zero hm i, ?_⟩
    rw [stateBodies_eq s (state_contains_zero hm)]
    rfl

end RationalReconstruction

namespace Main

/-- The entire finite rational polytope output sequence converges to an actual
realization for every realizable named input. Every nonrealizable input is
rejected at a finite height. Every output is a literal rational convex hull. -/
theorem rational_polytope_reconstruction (n d : ℕ) (hd : 0 < d)
    (c : Coefficients n d) (a : ℕ → MultiIndex n d → ℚ)
    (ha : RationalCertificates.IsName c a) :
    (c ∈ VolumeLocus n d →
      (∀ h, RationalReconstruction.reconstruct n d a h ≠ none) ∧
      ∃ K : Fin n → Body d,
        Tendsto (fun h => RationalReconstruction.stateBodies
          ((RationalReconstruction.reconstruct n d a h).getD default)) atTop (𝓝 K) ∧
        Realizes K c) ∧
    (c ∉ VolumeLocus n d ↔ ∃ h, RationalReconstruction.reconstruct n d a h = none) ∧
    (∀ h s, RationalReconstruction.reconstruct n d a h = some s →
      ∀ i, 0 ∈ s.vertices i ∧
        (RationalReconstruction.stateBodies s i : Set (Space d)) = RationalHulls.hull (s.vertices i)) := by
  first
  | constructor
    · intro hc
      exact ⟨RationalReconstruction.reconstruct_ne_none_of_realizable hd ha hc,
        RationalReconstruction.reconstruction_converges hd ha hc⟩
    constructor
    · constructor
      · exact RationalReconstruction.exists_rejection_of_not_realizable ha
      · rintro ⟨h, hh⟩ hc
        exact RationalReconstruction.reconstruct_ne_none_of_realizable hd ha hc h hh
    · intro h s hs
      exact RationalReconstruction.reconstruct_some_is_rational_polytope a hs

end Main
end VolumePolynomials
