module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Convergence of the whole least-path output sequence

This is the finite-tree selection argument in Proposition 8.4. Each `A n`
is the finite linearly ordered set of accepted paths of height `n`; `π`
is restriction to a prefix. Prefix restriction preserves lexicographic order.
The terminal metric data are required to satisfy the proved tail estimate.
No compatible branch is assumed or chosen, and no convergence rate for the
sequence of least-path terminal states is asserted.
-/

open scoped Topology
open Filter

namespace VolumePolynomials.FinitePathSelection

/-- Any decreasing sequence of finite sets eventually stops changing. -/
theorem antitone_finsets_stabilize {α : Type*} (S : ℕ → Finset α) (hS : Antitone S) :
    ∃ N, ∀ n, N ≤ n → S n = S N := by
  classical
  let P : ℕ → Prop := fun k => ∃ n, (S n).card = k
  have hex : ∃ k, P k := ⟨(S 0).card, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hex
  refine ⟨N, fun n hn => ?_⟩
  apply Finset.eq_of_subset_of_card_le (hS hn)
  rw [hN]
  exact Nat.find_min' hex ⟨n, rfl⟩

/-- Telescoping consecutive-path bounds give the exact finite tail bound. -/
theorem prefix_distance_le_sub
    {A : ℕ → Type*} {X : Type*} [PseudoMetricSpace X]
    (π : {i j : ℕ} → i ≤ j → A j → A i)
    (hrefl : ∀ n (a : A n), π (le_refl n) a = a)
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hstep : ∀ n (a : A (n + 1)),
      dist (point (n + 1) a) (point n (π (Nat.le_succ n) a)) ≤
        radius n - radius (n + 1))
    {i j : ℕ} (h : i ≤ j) :
    ∀ a : A j, dist (point j a) (point i (π h a)) ≤ radius i - radius j := by
  induction j, h using Nat.le_induction with
  | base =>
      intro a
      simp [hrefl]
  | succ j hj ih =>
      intro a
      have hs := hstep j a
      have hp := ih (π (Nat.le_succ j) a)
      have ht := dist_triangle (point (j + 1) a)
        (point j (π (Nat.le_succ j) a))
        (point i (π hj (π (Nat.le_succ j) a)))
      rw [htrans] at ht hp
      linarith

/-- A nonnegative tail radius bounds the distance from a terminal state to every prefix. -/
theorem prefix_distance_le_radius
    {A : ℕ → Type*} {X : Type*} [PseudoMetricSpace X]
    (π : {i j : ℕ} → i ≤ j → A j → A i)
    (hrefl : ∀ n (a : A n), π (le_refl n) a = a)
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ radius n)
    (hstep : ∀ n (a : A (n + 1)),
      dist (point (n + 1) a) (point n (π (Nat.le_succ n) a)) ≤
        radius n - radius (n + 1))
    {i j : ℕ} (h : i ≤ j) (a : A j) :
    dist (point j a) (point i (π h a)) ≤ radius i := by
  have hb := prefix_distance_le_sub π hrefl htrans point radius hstep h a
  linarith [hr j]

section FiniteLevels

variable {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, LinearOrder (A n)]
variable [∀ n, Nonempty (A n)]

/-- The actual least accepted path at the indicated height. -/
def leastPath (n : ℕ) : A n := Finset.univ.min' Finset.univ_nonempty

theorem leastPath_le (n : ℕ) (a : A n) : leastPath n ≤ a :=
  Finset.min'_le _ _ (Finset.mem_univ a)

variable (π : {i j : ℕ} → i ≤ j → A j → A i)

/-- Possible prefixes at depth `j` of paths of height at least `n`. -/
def extendible (j n : ℕ) : Finset (A j) :=
  Finset.univ.image (π (Nat.le_max_left j n))

/-- Prefix of the chosen least path, using `max j n` to avoid partial definitions. -/
def chosenPrefix (j n : ℕ) : A j :=
  π (Nat.le_max_left j n) (leastPath (max j n))

theorem chosenPrefix_eq {j n : ℕ} (h : j ≤ n) :
    chosenPrefix π j n = π h (leastPath n) := by
  have heq : ∀ k (hk : j ≤ k), k = n →
      π hk (leastPath k) = π h (leastPath n) := by
    intro k hk he
    subst k
    rfl
  exact heq (max j n) (Nat.le_max_left j n) (max_eq_right h)

theorem chosenPrefix_mem (j n : ℕ) : chosenPrefix π j n ∈ extendible π j n := by
  apply Finset.mem_image.mpr
  exact ⟨leastPath (max j n), Finset.mem_univ _, rfl⟩

theorem chosenPrefix_le
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h)) (j n : ℕ)
    {a : A j} (ha : a ∈ extendible π j n) : chosenPrefix π j n ≤ a := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
  exact hmono _ (leastPath_le _ b)

omit [∀ n, Nonempty (A n)] in
theorem extendible_antitone
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a) (j : ℕ) :
    Antitone (extendible π j) := by
  intro n m hnm a ha
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ha
  apply Finset.mem_image.mpr
  refine ⟨π (max_le_max_left j hnm) b, Finset.mem_univ _, ?_⟩
  exact (htrans (Nat.le_max_left j n) (max_le_max_left j hnm) b).trans hb

/-- At every fixed depth, prefixes of the least paths eventually stabilize. -/
theorem chosenPrefix_stabilizes
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h)) (j : ℕ) :
    ∃ N, ∀ n, N ≤ n → chosenPrefix π j n = chosenPrefix π j N := by
  obtain ⟨N, hN⟩ := antitone_finsets_stabilize (extendible π j)
    (extendible_antitone π htrans j)
  refine ⟨N, fun n hn => le_antisymm ?_ ?_⟩
  · apply chosenPrefix_le π hmono
    rw [hN n hn]
    exact chosenPrefix_mem π j N
  · apply chosenPrefix_le π hmono
    rw [← hN n hn]
    exact chosenPrefix_mem π j n

variable {X : Type*} [PseudoMetricSpace X]

/--
The entire output sequence of least-path terminal states is Cauchy. The proof
uses only eventual stabilization of fixed-depth prefixes, so it does not
assume that the least paths at successive heights are compatible.
-/
theorem terminal_cauchy
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i) :
    CauchySeq (fun n => point n (leastPath n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (hradius.eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨N, hN⟩ := chosenPrefix_stabilizes π htrans hmono j
  refine ⟨max j N, fun n hn m hm => ?_⟩
  have hjn : j ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  have hjm : j ≤ m := (le_max_left _ _).trans hm
  have hNm : N ≤ m := (le_max_right _ _).trans hm
  have hpn : π hjn (leastPath n) = chosenPrefix π j N := by
    exact (chosenPrefix_eq π hjn).symm.trans (hN n hNn)
  have hpm : π hjm (leastPath m) = chosenPrefix π j N := by
    exact (chosenPrefix_eq π hjm).symm.trans (hN m hNm)
  have hdn := hnear hjn (leastPath n)
  have hdm := hnear hjm (leastPath m)
  rw [hpn] at hdn
  rw [hpm] at hdm
  have htri := dist_triangle_right (point n (leastPath n)) (point m (leastPath m))
    (point j (chosenPrefix π j N))
  linarith

/-- Completeness produces a limit for the entire least-path terminal sequence. -/
theorem terminal_converges [CompleteSpace X]
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i) :
    ∃ x, Tendsto (fun n => point n (leastPath n)) atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete (terminal_cauchy π htrans hmono point radius hradius hnear)

/-- A continuous coefficient map of the limit is the exact target coefficient vector. -/
theorem terminal_limit_realizes [CompleteSpace X]
    {Y : Type*} [MetricSpace Y]
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius error : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (herror : Tendsto error atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i)
    (Φ : X → Y) (hΦ : Continuous Φ) (target : Y)
    (hcoeff : ∀ n (a : A n), dist (Φ (point n a)) target ≤ error n) :
    ∃ x, Tendsto (fun n => point n (leastPath n)) atTop (𝓝 x) ∧ Φ x = target := by
  obtain ⟨x, hx⟩ := terminal_converges π htrans hmono point radius hradius hnear
  refine ⟨x, hx, ?_⟩
  have hlim : Tendsto (fun n => Φ (point n (leastPath n))) atTop (𝓝 target) := by
    apply (tendsto_iff_dist_tendsto_zero).mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => hcoeff n (leastPath n)) herror
  exact tendsto_nhds_unique ((hΦ.tendsto x).comp hx) hlim

end FiniteLevels

/--
If no exact realization exists, some finite height has no accepted path.
Thus enumerating and testing successive finite path sets eventually rejects.
-/
theorem exists_empty_level_of_not_realizable
    {A : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, LinearOrder (A n)]
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {Y : Type*} [MetricSpace Y]
    (π : {i j : ℕ} → i ≤ j → A j → A i)
    (htrans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      π hij (π hjk a) = π (hij.trans hjk) a)
    (hmono : ∀ {i j} (h : i ≤ j), Monotone (π h))
    (point : ∀ n, A n → X) (radius error : ℕ → ℝ)
    (hradius : Tendsto radius atTop (𝓝 0))
    (herror : Tendsto error atTop (𝓝 0))
    (hnear : ∀ {i j} (h : i ≤ j) (a : A j),
      dist (point j a) (point i (π h a)) ≤ radius i)
    (Φ : X → Y) (hΦ : Continuous Φ) (target : Y)
    (hcoeff : ∀ n (a : A n), dist (Φ (point n a)) target ≤ error n)
    (hno : target ∉ Set.range Φ) :
    ∃ n, IsEmpty (A n) := by
  classical
  by_contra h
  have hne : ∀ n, Nonempty (A n) := by
    intro n
    by_contra hn
    exact h ⟨n, ⟨fun a => hn ⟨a⟩⟩⟩
  let : ∀ n, Nonempty (A n) := hne
  obtain ⟨x, _, hx⟩ := terminal_limit_realizes π htrans hmono point radius error
    hradius herror hnear Φ hΦ target hcoeff
  exact hno ⟨x, hx⟩

end VolumePolynomials.FinitePathSelection
