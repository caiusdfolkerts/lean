module

public import sunlet.coarse_selection
public import sunlet.negation_coarsening

/-! The odd part of the actual fine exponent kernel supplies generating
supports. The definitions below are the literal selected-row equations. -/

@[expose] public section
noncomputable section

namespace Sunlet.FineOddKernel

variable {G C D : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [DecidableEq C] [Fintype D] [LinearOrder D]

def mapParam {A B : Type*} (f : A → B) : ParamVar A A → ParamVar B B
  | .s i => .s (f i)
  | .t i => .t (f i)
  | .h i => .h (f i)
  | .u i => .u (f i)
  | .v i => .v (f i)

def Equation (q : G → C) (r : G → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) (b c : G) : Prop :=
  w (.s (q b)) + w (.t (q c)) +
    (if ClassSelection.selectsU r σ b c then
      w (.u (q (c-b))) + w (.h (q c))
    else w (.v (q (c-b))) + w (.h (q b))) = 0

def IsRelation (q : G → C) (r : G → D) (σ : Set D) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) : Prop := ∀ b c, Equation q r σ w b c

structure OddColumns (q : G → C) (w : ParamVar C C → ℚ) : Prop where
  s : ∀ a, w (.s (q (-a))) = -w (.s (q a))
  t : ∀ a, w (.t (q (-a))) = -w (.t (q a))
  h : ∀ a, w (.h (q (-a))) = -w (.h (q a))
  u : ∀ a, w (.u (q (-a))) = -w (.u (q a))
  v : ∀ a, w (.v (q (-a))) = -w (.v (q a))

def negColumns (e : C ≃ C) (w : ParamVar C C → ℚ) : ParamVar C C → ℚ :=
  fun j => w (mapParam e j)

theorem relation_neg (q : G → C) (r : G → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (e : C ≃ C)
    (he : ∀ a, e (q a) = q (-a)) (hr : ∀ a, r (-a) = r a)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) :
    IsRelation q r σ (negColumns e w) := by
  intro b c
  have hd : (-c)-(-b) = -(c-b) := by abel
  have hs : ClassSelection.selectsU r σ (-b) (-c) ↔
      ClassSelection.selectsU r σ b c := by
    simp only [ClassSelection.selectsU, hd, hr]
  have h := hw (-b) (-c)
  simpa only [Equation, negColumns, mapParam, he, hd, hs] using h

theorem relation_sub (q : G → C) (r : G → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (w v : ParamVar C C → ℚ)
    (hw : IsRelation q r σ w) (hv : IsRelation q r σ v) :
    IsRelation q r σ (w-v) := by
  intro b c
  have h := hw b c
  have h' := hv b c
  unfold Equation at h h' ⊢
  simp only [Pi.sub_apply]
  split_ifs at h h' ⊢ <;> linarith

theorem difference_odd (q : G → C) (e : C ≃ C)
    (he : ∀ a, e (q a) = q (-a)) (w : ParamVar C C → ℚ) :
    OddColumns q (w-negColumns e w) := by
  constructor <;> intro a <;>
    simp only [Pi.sub_apply, negColumns, mapParam, he, neg_neg] <;> ring

theorem odd_zero (q : G → C) (w : ParamVar C C → ℚ) (ho : OddColumns q w) :
    w (.s (q 0)) = 0 ∧ w (.t (q 0)) = 0 ∧ w (.h (q 0)) = 0 ∧
      w (.u (q 0)) = 0 ∧ w (.v (q 0)) = 0 := by
  have hs := ho.s 0; have ht := ho.t 0; have hh := ho.h 0
  have hu := ho.u 0; have hv := ho.v 0
  simp only [neg_zero] at hs ht hh hu hv
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem t_value (q : G → C) (r : G → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (hσ : r 0 ∉ σ)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) (ho : OddColumns q w)
    (a : G) : w (.t (q a)) = -w (.s (q a))-w (.h (q a)) := by
  have h := hw a a
  have hz := (odd_zero q w ho).2.2.2.2
  simp [Equation, ClassSelection.selectsU, hσ] at h
  linarith

theorem u_value (q : G → C) (r : G → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (hσ : r 0 ∉ σ)
    (hmin : ∀ a, r 0 ≤ r a) (hr0 : ∀ a, r a = r 0 ↔ a = 0)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) (ho : OddColumns q w)
    (a : G) : w (.u (q a)) = w (.s (q a)) := by
  by_cases ha : a = 0
  · subst a
    rw [(odd_zero q w ho).1, (odd_zero q w ho).2.2.2.1]
  · have hlt : r 0 < r a := lt_of_le_of_ne (hmin a)
      (fun h => ha ((hr0 a).mp h.symm))
    have h := hw 0 a
    have hs : ClassSelection.selectsU r σ 0 a := Or.inl hlt
    simp only [Equation, if_pos hs, sub_zero] at h
    have ht := t_value q r σ hσ w hw ho a
    have hz := (odd_zero q w ho).1
    linarith

theorem v_value (q : G → C) (r : G → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (hσ : r 0 ∉ σ)
    (hmin : ∀ a, r 0 ≤ r a) (hr0 : ∀ a, r a = r 0 ↔ a = 0)
    (hr : ∀ a, r (-a) = r a)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) (ho : OddColumns q w)
    (a : G) : w (.v (q a)) = w (.s (q a))+w (.h (q a)) := by
  by_cases ha : a = 0
  · subst a
    rw [(odd_zero q w ho).1, (odd_zero q w ho).2.2.1,
      (odd_zero q w ho).2.2.2.2, add_zero]
  · have hlt : r 0 < r a := lt_of_le_of_ne (hmin a)
      (fun h => ha ((hr0 a).mp h.symm))
    have hs : ¬ ClassSelection.selectsU r σ (-a) 0 := by
      simp only [ClassSelection.selectsU,hr]
      exact not_or.mpr ⟨not_lt.mpr hlt.le, fun h => hlt.ne h.1.symm⟩
    have h := hw (-a) 0
    simp only [Equation, if_neg hs, zero_sub, neg_neg, ho.s, ho.h] at h
    have hz := (odd_zero q w ho).2.1
    linarith

theorem cross_heights (q : G → C) (r : G → D) (σ : Set D)
    [DecidablePred (· ∈ σ)] (hσ : r 0 ∉ σ)
    (hmin : ∀ a, r 0 ≤ r a) (hr0 : ∀ a, r a = r 0 ↔ a = 0)
    (hr : ∀ a, r (-a) = r a)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) (ho : OddColumns q w)
    (b c : G) (hbc : r b ≠ r c) :
    w (.s (q (c-b))) = w (.s (q c))-w (.s (q b)) ∧
    w (.s (q (c-b)))+w (.h (q (c-b))) =
      (w (.s (q c))+w (.h (q c)))-(w (.s (q b))+w (.h (q b))) := by
  have inc (b c : G) (hbc : r b < r c) :
      w (.s (q (c-b))) = w (.s (q c))-w (.s (q b)) ∧
      w (.s (q (c-b)))+w (.h (q (c-b))) =
        (w (.s (q c))+w (.h (q c)))-(w (.s (q b))+w (.h (q b))) := by
    have hs : ClassSelection.selectsU r σ b c := Or.inl hbc
    have hs' : ¬ ClassSelection.selectsU r σ c b := by
      exact not_or.mpr ⟨not_lt.mpr hbc.le, fun h => hbc.ne h.1.symm⟩
    have h := hw b c
    have h' := hw c b
    simp only [Equation, if_pos hs] at h
    simp only [Equation, if_neg hs'] at h'
    have ht := t_value q r σ hσ w hw ho c
    have ht' := t_value q r σ hσ w hw ho b
    have hu := u_value q r σ hσ hmin hr0 w hw ho (c-b)
    have hv := v_value q r σ hσ hmin hr0 hr w hw ho (b-c)
    have hsd : w (.s (q (b-c))) = -w (.s (q (c-b))) := by
      rw [← neg_sub c b, ho.s]
    have hhd : w (.h (q (b-c))) = -w (.h (q (c-b))) := by
      rw [← neg_sub c b, ho.h]
    exact ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne hbc with h | h
  · exact inc b c h
  · have hx := inc c b h
    have hsd : w (.s (q (b-c))) = -w (.s (q (c-b))) := by
      rw [← neg_sub c b, ho.s]
    have hhd : w (.h (q (b-c))) = -w (.h (q (c-b))) := by
      rw [← neg_sub c b, ho.h]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem nonzero_height (q : G → C) (hq : Function.Surjective q)
    (r : G → D) (σ : Set D) [DecidablePred (· ∈ σ)] (hσ : r 0 ∉ σ)
    (hmin : ∀ a, r 0 ≤ r a) (hr0 : ∀ a, r a = r 0 ↔ a = 0)
    (hr : ∀ a, r (-a) = r a)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) (ho : OddColumns q w)
    (hne : w ≠ 0) :
    (∃ a, w (.s (q a)) ≠ 0) ∨
      (∃ a, w (.s (q a))+w (.h (q a)) ≠ 0) := by
  by_contra h
  push_neg at h
  apply hne
  funext j
  cases j with
  | s i => obtain ⟨a,rfl⟩ := hq i; exact h.1 a
  | t i =>
      obtain ⟨a,rfl⟩ := hq i
      have ht := t_value q r σ hσ w hw ho a
      change w (.t (q a)) = 0
      linarith [h.2 a]
  | h i => obtain ⟨a,rfl⟩ := hq i; change w (.h (q a))=0; linarith [h.1 a,h.2 a]
  | u i =>
      obtain ⟨a,rfl⟩ := hq i
      exact (u_value q r σ hσ hmin hr0 w hw ho a).trans (h.1 a)
  | v i =>
      obtain ⟨a,rfl⟩ := hq i
      exact (v_value q r σ hσ hmin hr0 hr w hw ho a).trans (h.2 a)

/-- A nonzero odd relation forces the full expected dimension through the
already proved stable-support theorem. No differential-rank hypothesis occurs. -/
theorem dimension_of_nonzero_odd {K : Type*} [Field K] [Infinite K]
    (q : G → C) (hq : Function.Surjective q) (z : C)
    (hq0 : ∀ a, q a = z ↔ a = 0)
    (r : G → D) (σ : Set D) [DecidablePred (· ∈ σ)] (hσ : r 0 ∉ σ)
    (hmin : ∀ a, r 0 ≤ r a) (hr0 : ∀ a, r a = r 0 ↔ a = 0)
    (hr : ∀ a, r (-a) = r a)
    (hfib : ∀ a b, r a = r b → q a = q b ∨ q (-a) = q b)
    (w : ParamVar C C → ℚ) (hw : IsRelation q r σ w) (ho : OddColumns q w)
    (hne : w ≠ 0) (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) q))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  have hex := nonzero_height q hq r σ hσ hmin hr0 hr w hw ho hne
  obtain ⟨f, hfodd, hf0, hfcross⟩ : ∃ f : C → ℚ,
      (∀ a, f (q (-a)) = -f (q a)) ∧ (∃ a, f (q a) ≠ 0) ∧
      (∀ b c, r b ≠ r c → f (q (c-b)) = f (q c)-f (q b)) := by
    rcases hex with hs | hl
    · exact ⟨fun i => w (.s i),ho.s,hs,
        fun b c h => (cross_heights q r σ hσ hmin hr0 hr w hw ho b c h).1⟩
    · refine ⟨fun i => w (.s i)+w (.h i), ?_, hl,
        fun b c h => (cross_heights q r σ hσ hmin hr0 hr w hw ho b c h).2⟩
      intro a
      change w (.s (q (-a))) + w (.h (q (-a))) = -(w (.s (q a)) + w (.h (q a)))
      rw [ho.s,ho.h]
      ring
  have hp : ∀ a b, r a = r b → f (q a) = f (q b) ∨ f (q a) = -f (q b) := by
    intro a b hab
    rcases hfib a b hab with h | h
    · exact Or.inl (congrArg f h)
    · right
      have hh := hfodd a
      rw [h] at hh
      linarith
  obtain ⟨hpos,hneg,htwoP,htwoN⟩ :=
    OddSupport.supports r (fun a => f (q a)) hfodd hp hfcross hf0 hm
  have hzero : f z = 0 := by
    have h := hfodd 0
    have hqz : q 0 = z := (hq0 0).mpr rfl
    simp only [neg_zero,hqz] at h
    linarith
  apply StableSupport.dimension_of_generating_supports q hq z hq0
    {i | 0 < f i} {i | f i < 0}
  · simpa only [Set.mem_setOf_eq,hzero] using (lt_irrefl (0 : ℚ))
  · simpa only [Set.mem_setOf_eq,hzero] using (lt_irrefl (0 : ℚ))
  · apply Set.disjoint_left.mpr
    intro i hi hj
    change 0 < f i at hi
    change f i < 0 at hj
    exact (not_lt_of_ge hi.le) hj
  · exact hpos
  · exact hneg
  · obtain ⟨a,ha,b,hb,hab⟩ := htwoP
    exact ⟨a,ha,b,hb,hab⟩
  · obtain ⟨a,ha,b,hb,hab⟩ := htwoN
    exact ⟨a,ha,b,hb,hab⟩

end Sunlet.FineOddKernel
