module

public import PaperVerification.AlternatingFormsEvenWalkPartition
public import PaperVerification.AlternatingFormsEvenDeterminantMultiaffine
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Lean.Elab.Tactic.Omega

/-!
# The determinant product belonging to an actual strip walk

The ordered column sets are the actual crossing times of the edges of the
strip.  Their union is disjoint.  The alternating positions in each ordered
fiber are exactly the downward steps of the walk.  Thus the leading exponent
vector of the determinant product is the indicator of its down-step set.

All statements include strip width zero; no positivity of the width is
introduced.  In that case the walk hypotheses themselves force length zero.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace PaperVerification.AlternatingForms.EvenWalkDeterminants

open scoped BigOperators
open EvenWalkPartition EvenDeterminants

def fiberDegree (h : ℕ → ℕ) (m a : ℕ) : ℕ :=
  (crossingTimes h a m).card / 2

theorem fiber_card (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) (a : Fin L) :
    (crossingTimes h a m).card = 2 * fiberDegree h m a + 1 := by
  have ho := Nat.odd_iff.mp (crossingTimes_odd h m L a hzero hfinal hstep a.isLt)
  unfold fiberDegree
  omega

/-- The increasing column labels attached to an edge of the strip. -/
def fiberColumns (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) (a : Fin L) :
    Fin (2 * fiberDegree h m a + 1) → Fin m := fun i =>
  let j := Fin.cast (fiber_card h m L hzero hfinal hstep a).symm i
  ⟨crossingEnumeration h a m j,
    ((mem_crossingTimes h a m _).mp (crossingEnumeration_mem h a m j)).1⟩

theorem fiberColumns_strictMono (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) (a : Fin L) :
    StrictMono (fiberColumns h m L hzero hfinal hstep a) := by
  intro i j hij
  change crossingEnumeration h a m (Fin.cast _ i) <
    crossingEnumeration h a m (Fin.cast _ j)
  exact (crossingEnumeration h a m).strictMono hij

theorem fiberColumns_crosses (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) (a : Fin L)
    (i : Fin (2 * fiberDegree h m a + 1)) :
    Crosses h a (fiberColumns h m L hzero hfinal hstep a i).val :=
  ((mem_crossingTimes h a m _).mp (crossingEnumeration_mem h a m _)).2

/-- All column positions in all fibers are distinct. -/
theorem fiberColumns_disjoint (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) :
    Function.Injective (fun p : (a : Fin L) × Fin (2 * fiberDegree h m a + 1) =>
      fiberColumns h m L hzero hfinal hstep p.1 p.2) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ he
  have ha := fiberColumns_crosses h m L hzero hfinal hstep a i
  have hb := fiberColumns_crosses h m L hzero hfinal hstep b j
  change Crosses h a (fiberColumns h m L hzero hfinal hstep a i).val at ha
  change Crosses h b (fiberColumns h m L hzero hfinal hstep b j).val at hb
  change fiberColumns h m L hzero hfinal hstep a i =
    fiberColumns h m L hzero hfinal hstep b j at he
  rw [he] at ha
  unfold Crosses at ha hb
  have hab : a = b := Fin.ext (ha.symm.trans hb)
  subst b
  have hij := (fiberColumns_strictMono h m L hzero hfinal hstep a).injective he
  subst j
  rfl

theorem fiber_odd_position_downward (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) (a : Fin L)
    (i : Fin (fiberDegree h m a)) :
    let t := fiberColumns h m L hzero hfinal hstep a
      (rowPosition (fiberDegree h m a) (Sum.inr i))
    h (t.val + 1) + 1 = h t.val := by
  let j := Fin.cast (fiber_card h m L hzero hfinal hstep a).symm
    (rowPosition (fiberDegree h m a) (Sum.inr i))
  have hj : Odd j.val := by
    apply Nat.odd_iff.mpr
    change (2 * i.val + 1) % 2 = 1
    omega
  exact (enumeration_downward_iff_odd h a m hzero hstep j).mpr hj

/-- Every actual downward step is an odd ordinal position in its unique edge
fiber. -/
theorem exists_fiber_odd_position (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hbound : ∀ i ≤ m, h i ≤ L)
    (hstep : ∀ i < m, UnitStep h i) (t : Fin m)
    (ht : h (t.val + 1) + 1 = h t.val) :
    ∃ a : Fin L, ∃ i : Fin (fiberDegree h m a),
      fiberColumns h m L hzero hfinal hstep a
        (rowPosition (fiberDegree h m a) (Sum.inr i)) = t := by
  let a : Fin L := ⟨min (h t.val) (h (t.val + 1)),
    crossed_edge_lt h m L t.val hbound hstep t.isLt⟩
  have hmem : t.val ∈ crossingTimes h a m :=
    (mem_crossingTimes h a m t.val).mpr ⟨t.isLt, rfl⟩
  obtain ⟨j, hj⟩ := ((crossingTimes h a m).orderIsoOfFin rfl).surjective ⟨t.val, hmem⟩
  have he : crossingEnumeration h a m j = t.val := congrArg Subtype.val hj
  have hodd : Odd j.val := (enumeration_downward_iff_odd h a m hzero hstep j).mp
    (by simpa only [he] using ht)
  have hmod := Nat.odd_iff.mp hodd
  have hcard := fiber_card h m L hzero hfinal hstep a
  have hjlt : j.val < 2 * fiberDegree h m a + 1 :=
    lt_of_lt_of_eq j.isLt hcard
  let i : Fin (fiberDegree h m a) := ⟨j.val / 2, by omega⟩
  have hij : Fin.cast hcard.symm
      (rowPosition (fiberDegree h m a) (Sum.inr i)) = j := by
    apply Fin.ext
    change 2 * (j.val / 2) + 1 = j.val
    omega
  refine ⟨a, i, ?_⟩
  apply Fin.ext
  change crossingEnumeration h a m (Fin.cast _
    (rowPosition (fiberDegree h m a) (Sum.inr i))) = t.val
  rw [hij, he]

theorem fiber_odd_positions_injective (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hstep : ∀ i < m, UnitStep h i) :
    Function.Injective (fun p : (a : Fin L) × Fin (fiberDegree h m a) =>
      fiberColumns h m L hzero hfinal hstep p.1
        (rowPosition (fiberDegree h m p.1) (Sum.inr p.2))) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ he
  have hp : (⟨a, rowPosition (fiberDegree h m a) (Sum.inr i)⟩ :
      (a : Fin L) × Fin (2 * fiberDegree h m a + 1)) =
      ⟨b, rowPosition (fiberDegree h m b) (Sum.inr j)⟩ :=
    fiberColumns_disjoint h m L hzero hfinal hstep he
  have hab : a = b := congrArg Sigma.fst hp
  subst b
  have hij : i = j := Sum.inr.inj
    (rowPosition_injective (fiberDegree h m a)
      (sigma_mk_injective (β := fun a : Fin L => Fin (2 * fiberDegree h m a + 1))
        (i := a) hp))
  subst j
  rfl

/-- Each exponent is exactly zero or one according to whether the position is
a downward step of the original walk. -/
theorem productLeadingExponent_apply (h : ℕ → ℕ) (m L : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hbound : ∀ i ≤ m, h i ≤ L)
    (hstep : ∀ i < m, UnitStep h i) (t : Fin m) :
    productLeadingExponent m (fun a : Fin L => fiberDegree h m a)
      (fiberColumns h m L hzero hfinal hstep) t =
      if h (t.val + 1) + 1 = h t.val then 1 else 0 := by
  classical
  let T := (a : Fin L) × Fin (fiberDegree h m a)
  let f : T → Fin m := fun p => fiberColumns h m L hzero hfinal hstep p.1
    (rowPosition (fiberDegree h m p.1) (Sum.inr p.2))
  have hf : Function.Injective f := fiber_odd_positions_injective h m L hzero hfinal hstep
  have hs : productLeadingExponent m (fun a : Fin L => fiberDegree h m a)
      (fiberColumns h m L hzero hfinal hstep) t =
      ∑ p : T, if f p = t then 1 else 0 := by
    rw [Fintype.sum_sigma]
    simp only [productLeadingExponent, Finset.sum_apply', Finsupp.single_apply]
    rfl
  rw [hs]
  by_cases ht : h (t.val + 1) + 1 = h t.val
  · obtain ⟨a, i, hi⟩ := exists_fiber_odd_position h m L hzero hfinal hbound hstep t ht
    let p₀ : T := ⟨a, i⟩
    have hp₀ : f p₀ = t := hi
    rw [if_pos ht, Finset.sum_eq_single p₀]
    · simp only [hp₀, if_true]
    · intro p hp hne
      have hpt : f p ≠ t := fun he => hne (hf (he.trans hp₀.symm))
      simp only [hpt, if_false]
    · simp
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro p hp
    have hpt : f p ≠ t := by
      intro he
      apply ht
      rw [← he]
      exact fiber_odd_position_downward h m L hzero hfinal hstep p.1 p.2
    simp only [hpt, if_false]

theorem sum_fiberDegree (h : ℕ → ℕ) (m L q : ℕ) (hzero : h 0 = 0)
    (hfinal : h m = L) (hbound : ∀ i ≤ m, h i ≤ L)
    (hstep : ∀ i < m, UnitStep h i) (hsize : m = 2 * q + L) :
    (∑ a : Fin L, fiberDegree h m a) = q := by
  change (∑ a : Fin L, (crossingTimes h a m).card / 2) = q
  exact (Fin.sum_univ_eq_sum_range (fun a => (crossingTimes h a m).card / 2) L).trans
    (sum_fiber_half_card h m L q hzero hfinal hbound hstep hsize)

end PaperVerification.AlternatingForms.EvenWalkDeterminants
