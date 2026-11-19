module

public import VolumePolynomials.RationalHullSampling
public import VolumePolynomials.FinitePathSelection
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.GetD
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false

/-!
# Finite executable path sets and lexicographic output

This instantiates the checked finite-prefix stabilization argument for actual
finite lists of states and decidable edges. It computes every finite path set,
its least path, and its terminal state. Prefix closure and monotonicity are
proved from the literal list operations.
-/

open Filter
open scoped Topology

namespace VolumePolynomials.ComputableFinitePaths

variable {α : Type*} [LinearOrder α] [Inhabited α]

def Valid (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    (h : ℕ) (p : List α) : Prop :=
  p.length = h + 1 ∧
    (∀ i : Fin (h + 1), p.getD i.val default ∈ states i.val) ∧
    ∀ i : Fin h, edge i.val (p.getD i.val default) (p.getD (i.val + 1) default)

instance validDecidable (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : List α) : Decidable (Valid states edge h p) := by
  first
  | unfold Valid
    infer_instance

def paths (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) : Finset (List α) :=
  ((RationalHulls.selections (fun i : Fin (h + 1) => states i.val)).map List.ofFn).toFinset.filter
    (Valid states edge h)

theorem getD_take {p : List α} {j i : ℕ} (hi : i < j) :
    (p.take j).getD i default = p.getD i default := by
  first
  | simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem ofFn_getD (p : List α) (h : ℕ) (hp : p.length = h) :
    List.ofFn (fun i : Fin h => p.getD i.val default) = p := by
  first
  | apply List.ext_getElem
    · simpa using hp.symm
    · intro i hi hi'
      simp only [List.getElem_ofFn, List.getD_eq_getElem p default hi']

theorem mem_paths (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : List α) :
    p ∈ paths states edge h ↔ Valid states edge h p := by
  first
  | constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨List.mem_toFinset.mpr (List.mem_map.mpr ?_), hp⟩
      exact ⟨fun i : Fin (h + 1) => p.getD i.val default,
        Iff.mpr (RationalHulls.mem_selections _ _) hp.2.1, ofFn_getD p (h + 1) hp.1⟩

theorem valid_take (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    {i j : ℕ} (hij : i ≤ j) {p : List α} (hp : Valid states edge j p) :
    Valid states edge i (p.take (i + 1)) := by
  first
  | refine ⟨by simp [hp.1, Nat.min_eq_left (Nat.succ_le_succ hij)], ?_, ?_⟩
    · intro k
      rw [getD_take k.isLt]
      exact hp.2.1 ⟨k.val, k.isLt.trans_le (Nat.succ_le_succ hij)⟩
    · intro k
      rw [getD_take (by omega : k.val < i + 1), getD_take (by omega : k.val + 1 < i + 1)]
      exact hp.2.2 ⟨k.val, k.isLt.trans_le hij⟩

theorem take_monotone (k : ℕ) : Monotone (List.take k : List α → List α) := by
  first
  | intro p q hpq
    rcases lt_or_eq_of_le hpq with h | rfl
    · change List.Lex (· < ·) p q at h
      clear hpq
      induction h generalizing k with
      | nil =>
          cases k with
          | zero => exact le_rfl
          | succ k =>
              apply le_of_lt
              exact List.Lex.nil
      | cons h ih =>
          cases k with
          | zero => exact le_rfl
          | succ k => exact List.cons_le_cons _ (ih k)
      | rel h =>
          cases k with
          | zero => exact le_rfl
          | succ k =>
              apply le_of_lt
              exact List.Lex.rel h
    · exact le_rfl

abbrev Path (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) :=
  {p : List α // p ∈ paths states edge h}

def pathPrefix (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j : ℕ} (hij : i ≤ j)
    (p : Path states edge j) : Path states edge i :=
  ⟨p.val.take (i + 1), Iff.mpr (mem_paths states edge i _)
    (valid_take states edge hij (Iff.mp (mem_paths states edge j _) p.property))⟩

theorem prefix_refl (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge h) :
    pathPrefix states edge (le_refl h) p = p := by
  first
  | apply Subtype.ext
    exact List.take_of_length_le (Iff.mp (mem_paths states edge h p.val) p.property).1.le

theorem prefix_trans (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (p : Path states edge k) :
    pathPrefix states edge hij (pathPrefix states edge hjk p) =
      pathPrefix states edge (hij.trans hjk) p := by
  first
  | apply Subtype.ext
    simp only [pathPrefix, List.take_take, Nat.min_eq_left (Nat.succ_le_succ hij)]

theorem prefix_monotone (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j : ℕ} (hij : i ≤ j) :
    Monotone (pathPrefix states edge hij) := fun _ _ h => take_monotone (i + 1) h

def terminal (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge h) : α :=
  p.val.getD h default

theorem terminal_mem (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge h) :
    terminal states edge h p ∈ states h :=
  (Iff.mp (mem_paths states edge h p.val) p.property).2.1 ⟨h, Nat.lt_succ_self h⟩

theorem terminal_prefix (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] {i j : ℕ} (hij : i ≤ j) (p : Path states edge j) :
    terminal states edge i (pathPrefix states edge hij p) = p.val.getD i default :=
  getD_take (Nat.lt_succ_self i)

theorem terminal_edge (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) (p : Path states edge (h + 1)) :
    edge h (terminal states edge h (pathPrefix states edge (Nat.le_succ h) p))
      (terminal states edge (h + 1) p) := by
  first
  | rw [terminal_prefix]
    exact (Iff.mp (mem_paths states edge (h + 1) p.val) p.property).2.2 ⟨h, Nat.lt_succ_self h⟩

/-- The finite algorithm returns `none` exactly at an empty height. -/
def output (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) : Option α :=
  if hp : (paths states edge h).Nonempty then
    some (((paths states edge h).min' hp).getD h default)
  else none

theorem output_eq_none_iff (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (h : ℕ) :
    output states edge h = none ↔ IsEmpty (Path states edge h) := by
  first
  | simp only [output]
    split_ifs with hp
    · simp only [Option.some_ne_none, false_iff]
      intro hi
      obtain ⟨p, hp⟩ := hp
      exact hi.false ⟨p, hp⟩
    · simp only [true_iff]
      exact ⟨fun p => hp ⟨p.val, p.property⟩⟩

theorem output_eq_least_terminal (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] [∀ h, Nonempty (Path states edge h)] (h : ℕ) :
    output states edge h = some (terminal states edge h
      (FinitePathSelection.leastPath (A := Path states edge) h)) := by
  first
  | have hp : (paths states edge h).Nonempty := by
      obtain ⟨p⟩ := (inferInstance : Nonempty (Path states edge h))
      exact ⟨p.val, p.property⟩
    have heq : (paths states edge h).min' hp =
        (FinitePathSelection.leastPath (A := Path states edge) h).val := by
      apply le_antisymm
      · exact Finset.min'_le _ _
          (FinitePathSelection.leastPath (A := Path states edge) h).property
      · exact FinitePathSelection.leastPath_le (A := Path states edge) h
          ⟨(paths states edge h).min' hp, Finset.min'_mem _ _⟩
    simp only [output, dif_pos hp, heq, terminal]

theorem paths_nonempty_of_sequence (states : ℕ → List α) (edge : ℕ → α → α → Prop)
    [∀ i, DecidableRel (edge i)] (f : ℕ → α)
    (hf : ∀ j, f j ∈ states j) (he : ∀ j, edge j (f j) (f (j + 1))) (h : ℕ) :
    Nonempty (Path states edge h) := by
  first
  | let p := List.ofFn (fun j : Fin (h + 1) => f j.val)
    have hpget (i : ℕ) (hi : i < h + 1) : p.getD i default = f i := by
      have hip : i < p.length := by simpa only [p, List.length_ofFn] using hi
      simpa only [p, List.getElem_ofFn] using List.getD_eq_getElem p default hip
    refine ⟨⟨p, Iff.mpr (mem_paths states edge h p) ⟨by simp [p], ?_, ?_⟩⟩⟩
    · intro i
      rw [hpget i.val i.isLt]
      exact hf i.val
    · intro i
      rw [hpget i.val (by omega), hpget (i.val + 1) (by omega)]
      exact he i.val

/-- The complete executable least-path sequence converges, provided the
verified edge radii and coefficient errors tend to zero. -/
theorem output_converges
    (states : ℕ → List α) (edge : ℕ → α → α → Prop) [∀ i, DecidableRel (edge i)]
    [∀ h, Nonempty (Path states edge h)]
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Y]
    (point : α → X) (Φ : X → Y) (hΦ : Continuous Φ) (target : Y)
    (radius error : ℕ → ℝ) (hr : ∀ j, 0 ≤ radius j)
    (hr0 : Tendsto radius atTop (𝓝 0)) (he0 : Tendsto error atTop (𝓝 0))
    (hedge : ∀ j, ∀ s ∈ states j, ∀ t ∈ states (j + 1), edge j s t →
      dist (point t) (point s) ≤ radius j - radius (j + 1))
    (hcoeff : ∀ j, ∀ s ∈ states j, dist (Φ (point s)) target ≤ error j) :
    ∃ x, Tendsto (fun h => point ((output states edge h).getD default)) atTop (𝓝 x) ∧ Φ x = target := by
  first
  | let π : {i j : ℕ} → i ≤ j → Path states edge j → Path states edge i :=
      @pathPrefix α _ _ states edge _
    let P : (h : ℕ) → Path states edge h → X := fun h p => point (terminal states edge h p)
    have hnear : ∀ {i j} (h : i ≤ j) (p : Path states edge j),
        dist (P j p) (P i (π h p)) ≤ radius i := by
      apply FinitePathSelection.prefix_distance_le_radius π
        (prefix_refl states edge) (prefix_trans states edge) P radius hr
      intro j p
      exact hedge j _ (terminal_mem states edge j (pathPrefix states edge (Nat.le_succ j) p))
        _ (terminal_mem states edge (j + 1) p) (terminal_edge states edge j p)
    obtain ⟨x, hx, hΦx⟩ := FinitePathSelection.terminal_limit_realizes π
      (prefix_trans states edge) (prefix_monotone states edge) P radius error hr0 he0 hnear Φ hΦ target
      (fun h p => hcoeff h _ (terminal_mem states edge h p))
    refine ⟨x, ?_, hΦx⟩
    simpa only [output_eq_least_terminal, Option.getD_some] using hx

end VolumePolynomials.ComputableFinitePaths
