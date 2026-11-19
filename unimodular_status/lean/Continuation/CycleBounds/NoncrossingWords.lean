module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Descents of noncrossing cyclic words

The combinatorial step in Proposition6.8 is expressed directly as a statement
about the cyclic word of active-component labels. No cactus structure is assumed.
-/

noncomputable section
namespace Unimodular.CycleBounds

variable {α : Type*}
attribute [local instance] Classical.propDecidable

/-- Two distinct parts never alternate in the cyclic order. The linear subword
criterion is unchanged by choosing another starting point on the circle. -/
def Noncrossing (w : List α) : Prop :=
  ∀ a b : α, a ≠ b → ¬[a, b, a, b].Sublist w

theorem Noncrossing.sublist {u w : List α} (hw : Noncrossing w) (hu : u.Sublist w) :
    Noncrossing u := fun a b hab h => hw a b hab (h.trans hu)

/-- A single directed step contributes one exactly at a strict potential decrease. -/
def step (h : α → ℝ) (a b : α) : ℕ := if h b < h a then 1 else 0

def pathCost (h : α → ℝ) (a : α) : List α → ℕ
  | [] => 0
  | b :: w => step h a b + pathCost h b w

def cyclicCost (h : α → ℝ) : List α → ℕ
  | [] => 0
  | a :: w => pathCost h a (w ++ [a])

@[simp] theorem step_self (h : α → ℝ) (a : α) : step h a a = 0 := by simp [step]

theorem step_triangle (h : α → ℝ) (a b c : α) :
    step h a b + step h b c ≤ step h a c + 1 := by
  by_cases hab : h b < h a
  · by_cases hbc : h c < h b
    · simp [step, hab, hbc, lt_trans hbc hab]
    · by_cases hac : h c < h a <;> simp [step, hab, hbc, hac]
  · by_cases hbc : h c < h b <;> by_cases hac : h c < h a <;>
      simp [step, hab, hbc, hac]

/-- Last vertex reached by a path, including the empty path. -/
def lastVertex (a : α) : List α → α
  | [] => a
  | b :: w => lastVertex b w

theorem lastVertex_append (a : α) (u v : List α) :
    lastVertex a (u ++ v) = lastVertex (lastVertex a u) v := by
  induction u generalizing a with
  | nil => rfl
  | cons b u ih => exact ih b

theorem pathCost_append (h : α → ℝ) (a : α) (u v : List α) :
    pathCost h a (u ++ v) = pathCost h a u + pathCost h (lastVertex a u) v := by
  induction u generalizing a with
  | nil => simp [pathCost, lastVertex]
  | cons b u ih =>
      simpa [pathCost, lastVertex, Nat.add_assoc] using
        (congrArg (fun z ↦ step h a b + z) (ih b))

theorem cyclicCost_append_comm (h : α → ℝ) (u v : List α) :
    cyclicCost h (u ++ v) = cyclicCost h (v ++ u) := by
  cases u with
  | nil => simp
  | cons a u =>
    cases v with
    | nil => simp
    | cons b v =>
      simp [cyclicCost, pathCost_append, pathCost, lastVertex_append, lastVertex,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem cyclicCost_cons_le (h : α → ℝ) (a : α) (w : List α) (hw : w ≠ []) :
    cyclicCost h (a :: w) ≤ cyclicCost h w + 1 := by
  cases w with
  | nil => contradiction
  | cons b w =>
    have ht := step_triangle h (lastVertex b w) a b
    simp only [cyclicCost, List.cons_append, pathCost, pathCost_append,
      List.nil_append, Nat.add_zero] at *
    omega

@[simp] theorem cyclicCost_duplicate_head (h : α → ℝ) (a : α) (w : List α) :
    cyclicCost h (a :: a :: w) = cyclicCost h (a :: w) := by
  simp [cyclicCost, pathCost]

@[simp] theorem cyclicCost_replicate (h : α → ℝ) (a : α) (k : ℕ) :
    cyclicCost h (List.replicate k a) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => simp [cyclicCost, pathCost]
    | succ k => simpa only [List.replicate_succ, cyclicCost_duplicate_head] using ih

theorem cyclicCost_replicate_append (h : α → ℝ) (a : α) (k : ℕ) (w : List α)
    (hk : 0 < k) :
    cyclicCost h (List.replicate k a ++ w) = cyclicCost h (a :: w) := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simp
    | succ k ih => simpa only [List.replicate_succ, List.cons_append,
        cyclicCost_duplicate_head] using (ih (by omega))

/-- Removing one contiguous nonempty part can reduce the number of descents
by at most one, with no restriction on the relative potentials of its neighbors. -/
theorem cyclicCost_interval_le (h : α → ℝ) (a : α) (k : ℕ) (u v : List α)
    (hk : 0 < k) (huv : u ++ v ≠ []) :
    cyclicCost h (u ++ List.replicate k a ++ v) ≤ cyclicCost h (u ++ v) + 1 := by
  rw [List.append_assoc, cyclicCost_append_comm h u,
    List.append_assoc, cyclicCost_replicate_append h a k (v ++ u) hk,
    cyclicCost_append_comm h u v]
  exact cyclicCost_cons_le h a (v ++ u) (by
    intro hh
    obtain ⟨hv, hu⟩ := List.append_eq_nil_iff.mp hh
    exact huv (List.append_eq_nil_iff.mpr ⟨hu, hv⟩))

/-- An explicit alternating four-index pattern violates noncrossing. -/
theorem Noncrossing.no_alternating {w : List α} (hw : Noncrossing w)
    (i j k l : Fin w.length) (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hik : w.get i = w.get k) (hjl : w.get j = w.get l)
    (hne : w.get i ≠ w.get j) : False := by
  let f : Fin 4 → Fin w.length := ![i, j, k, l]
  have hf : StrictMono f := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> norm_num [f] at * <;> omega
  apply hw (w.get i) (w.get j) hne
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro x
  fin_cases x
  · rfl
  · rfl
  · exact hik
  · exact hjl

/-- Every noncrossing partition of a nonempty linearly listed circle has a
part which is one contiguous interval. The proof minimizes the span of a part,
rather than assuming a combinatorial cactus decomposition. -/
theorem exists_interval_fiber {n : ℕ} (c : Fin n → α) (hn : 0 < n)
    (hcross : ∀ i j k l : Fin n, i < j → j < k → k < l →
      c i = c k → c j = c l → c i = c j) :
    ∃ a : α, ∃ lo hi : Fin n, lo ≤ hi ∧
      ∀ i : Fin n, c i = a ↔ lo ≤ i ∧ i ≤ hi := by
  classical
  let A := {a : α // a ∈ Finset.univ.image c}
  letI : Fintype A := Finset.fintypeCoeSort (Finset.univ.image c)
  let fiber (a : A) : Finset (Fin n) := Finset.univ.filter (fun i ↦ c i = a.val)
  have hne (a : A) : (fiber a).Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
    exact ⟨i, by simp [fiber, hi]⟩
  let lo (a : A) := (fiber a).min' (hne a)
  let hi (a : A) := (fiber a).max' (hne a)
  have hlo (a : A) : c (lo a) = a.val :=
    (Finset.mem_filter.mp (Finset.min'_mem (fiber a) (hne a))).2
  have hhi (a : A) : c (hi a) = a.val :=
    (Finset.mem_filter.mp (Finset.max'_mem (fiber a) (hne a))).2
  have hbounds (a : A) (i : Fin n) (h : c i = a.val) : lo a ≤ i ∧ i ≤ hi a := by
    have hm : i ∈ fiber a := by simp [fiber, h]
    exact ⟨Finset.min'_le _ _ hm, Finset.le_max' _ _ hm⟩
  letI : Nonempty A := ⟨⟨c ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, by simp, rfl⟩⟩⟩
  obtain ⟨a, ha⟩ := Finite.exists_min (fun a : A ↦ (hi a).val - (lo a).val)
  have hinside : ∀ i : Fin n, lo a ≤ i → i ≤ hi a → c i = a.val := by
    intro i hli hih
    by_contra hia
    let b : A := ⟨c i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
    have hneLo : i ≠ lo a := by intro h; exact hia ((congrArg c h).trans (hlo a))
    have hneHi : i ≠ hi a := by intro h; exact hia ((congrArg c h).trans (hhi a))
    have hloi : lo a < i := lt_of_le_of_ne hli hneLo.symm
    have hihi : i < hi a := lt_of_le_of_ne hih hneHi
    have hbbetween (j : Fin n) (hj : c j = b.val) : lo a < j ∧ j < hi a := by
      change c j = c i at hj
      constructor
      · by_contra hjlow
        have hjle : j ≤ lo a := le_of_not_gt hjlow
        have hjne : j ≠ lo a := by
          intro he
          exact hia (hj.symm.trans ((congrArg c he).trans (hlo a)))
        have hjlt : j < lo a := lt_of_le_of_ne hjle hjne
        have hbad := hcross j (lo a) i (hi a) hjlt hloi hihi hj
          ((hlo a).trans (hhi a).symm)
        exact hia (hj.symm.trans (hbad.trans (hlo a)))
      · by_contra hjhigh
        have hjge : hi a ≤ j := le_of_not_gt hjhigh
        have hjne : hi a ≠ j := by
          intro he
          exact hia (hj.symm.trans ((congrArg c he.symm).trans (hhi a)))
        have hjgt : hi a < j := lt_of_le_of_ne hjge hjne
        have hbad := hcross (lo a) i (hi a) j hloi hihi hjgt
          ((hlo a).trans (hhi a).symm) hj.symm
        exact hia (hbad.symm.trans (hlo a))
    have hleft := (hbbetween (lo b) (hlo b)).1
    have hright := (hbbetween (hi b) (hhi b)).2
    have hb := (hbounds b (hi b) (hhi b)).1
    have hmin := ha b
    have hleft' : (lo a).val < (lo b).val := hleft
    have hright' : (hi b).val < (hi a).val := hright
    have hb' : (lo b).val ≤ (hi b).val := hb
    omega
  refine ⟨a.val, lo a, hi a, (hbounds a (hi a) (hhi a)).1, ?_⟩
  intro i
  exact ⟨hbounds a i, fun h ↦ hinside i h.1 h.2⟩


/-- The interval part as a literal list decomposition, with no occurrence of
its label on either side. -/
theorem Noncrossing.exists_interval {w : List α} (hw : Noncrossing w) (hne : w ≠ []) :
    ∃ a : α, ∃ k : ℕ, ∃ u v : List α,
      0 < k ∧ a ∉ u ∧ a ∉ v ∧ w = u ++ List.replicate k a ++ v := by
  obtain ⟨a, lo, hi, hlohi, hfiber⟩ := exists_interval_fiber w.get
    (List.length_pos_iff.mpr hne) (by
      intro i j k l hij hjk hkl hik hjl
      by_contra hneq
      exact hw.no_alternating i j k l hij hjk hkl hik hjl hneq)
  let k := hi.val + 1 - lo.val
  let u := w.take lo.val
  let mid := (w.drop lo.val).take k
  let v := w.drop (hi.val + 1)
  have hk : 0 < k := by dsimp [k]; have := hi.isLt; omega
  have hlen : mid.length = k := by
    simp only [mid, List.length_take, List.length_drop]
    dsimp [k]
    have := hi.isLt
    omega
  have hmid : mid = List.replicate k a := by
    apply List.eq_replicate_iff.mpr
    refine ⟨hlen, ?_⟩
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    have hjk : j < k := by rwa [hlen] at hj
    have hjw : lo.val + j < w.length := by dsimp [k] at hjk; have := hi.isLt; omega
    have ha : w.get ⟨lo.val + j, hjw⟩ = a := (hfiber _).mpr
      ⟨by change lo.val ≤ lo.val + j; omega,
       by change lo.val + j ≤ hi.val; dsimp [k] at hjk; omega⟩
    have hjx' : w.get ⟨lo.val + j, hjw⟩ = x := by
      simpa [mid] using hjx
    exact hjx'.symm.trans ha
  have hau : a ∉ u := by
    intro hau
    obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp hau
    have hjlo : j < lo.val := by simpa [u, Nat.min_eq_left lo.isLt.le] using hj
    have hjw : j < w.length := hjlo.trans lo.isLt
    have ha : w.get ⟨j, hjw⟩ = a := by simpa [u] using hja
    have hh : lo.val ≤ j := ((hfiber _).mp ha).1
    omega
  have hav : a ∉ v := by
    intro hav
    obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp hav
    have hjw : hi.val + 1 + j < w.length := by
      simp only [v, List.length_drop] at hj
      omega
    have ha : w.get ⟨hi.val + 1 + j, hjw⟩ = a := by simpa [v] using hja
    have hh : hi.val + 1 + j ≤ hi.val := ((hfiber _).mp ha).2
    omega
  have heq : w = u ++ mid ++ v := by
    dsimp only [u, mid, v]
    rw [List.append_assoc]
    have hcut : lo.val + k = hi.val + 1 := by dsimp [k]; omega
    rw [← hcut, List.drop_take_append_drop, List.take_append_drop]
  exact ⟨a, k, u, v, hk, hau, hav, by rwa [hmid] at heq⟩

/-- The exact cycle bound: a nonempty noncrossing cyclic word with q distinct
labels has at most q−1 strict potential decreases. All lengths and all real
potentials are quantified, with repetitions and equal potentials allowed. -/
theorem cyclicCost_add_one_le_card (h : α → ℝ) (w : List α)
    (hw : Noncrossing w) (hne : w ≠ []) :
    cyclicCost h w + 1 ≤ w.toFinset.card := by
  classical
  have main : ∀ n : ℕ, ∀ w : List α, w.length = n → Noncrossing w → w ≠ [] →
      cyclicCost h w + 1 ≤ w.toFinset.card := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    intro w hwn hw hne
    obtain ⟨a, k, u, v, hk, hau, hav, heq⟩ := hw.exists_interval hne
    let r := u ++ v
    by_cases hr : r = []
    · have huv : u = [] ∧ v = [] := by simpa [r] using List.append_eq_nil_iff.mp hr
      obtain ⟨rfl, rfl⟩ := huv
      simp only [List.nil_append, List.append_nil] at heq
      rw [heq, cyclicCost_replicate, List.toFinset_replicate_of_ne_zero hk.ne']
      simp
    · have hsub : r.Sublist w := by
        rw [heq, List.append_assoc]
        exact (List.Sublist.refl u).append (List.sublist_append_right _ _)
      have hshort : r.length < n := by
        rw [← hwn, heq]
        simp only [r, List.length_append, List.length_replicate]
        omega
      have hrec := ih r.length hshort r rfl (hw.sublist hsub) hr
      have hcost : cyclicCost h w ≤ cyclicCost h r + 1 := by
        rw [heq]
        exact cyclicCost_interval_le h a k u v hk hr
      have hset : w.toFinset = insert a r.toFinset := by
        rw [heq]
        ext x
        simp [r, hk.ne', or_assoc, or_left_comm, or_comm]
      have hcard : w.toFinset.card = r.toFinset.card + 1 := by
        rw [hset, Finset.card_insert_of_notMem]
        simpa [r] using And.intro hau hav
      omega
  exact main w.length w rfl hw hne

theorem cyclicCost_le_card_sub_one (h : α → ℝ) (w : List α)
    (hw : Noncrossing w) (hne : w ≠ []) :
    cyclicCost h w ≤ w.toFinset.card - 1 := by
  have := cyclicCost_add_one_le_card h w hw hne
  omega

#print axioms cyclicCost_le_card_sub_one


end Unimodular.CycleBounds
