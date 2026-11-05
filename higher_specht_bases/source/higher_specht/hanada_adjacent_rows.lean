module

public import higher_specht.hanada_row_insertion
public import higher_specht.hanada_pop_saturation

@[expose] public section

/-!
# Comparison of insertions in adjacent rows without gaps

The proof uses the exact capacity equality at a popped entry.  A first
insertion increases every sublevel count between its input and its pop by one.
An upper-row insertion with a strictly larger input cannot exhaust the new
capacity before the first pop.  This also gives absorption above an absorbed
first input.

The strict inequality between inputs matches distinct visit pairs.  Equal
inputs are not silently allowed under a strict column convention.  No claim
about a row with an internal deleted-column gap is made here.
-/

namespace HigherSpecht

variable {α : Type*} [LinearOrder α]

/-- Conservation of the literal routine gives a gain of one below every
threshold above its input and no larger than its popped entry. -/
theorem scheduleCountLT_insert_gain (lower upper : List α) (x t : α)
    (hxt : x < t)
    (hpop : ∀ p, (scheduleRowInsert lower upper x).2 = some p → t ≤ p) :
    scheduleCountLT (scheduleRowInsert lower upper x).1 t =
      scheduleCountLT upper t + 1 := by
  have hc := (scheduleRowInsert_conservation lower upper x).countP_eq
    (fun z => decide (z < t))
  dsimp only [scheduleCountLT]
  cases hp : (scheduleRowInsert lower upper x).2 with
  | none =>
      simp [List.countP_cons, List.countP_append, hp, hxt] at hc
      omega
  | some p =>
      have hpt : ¬ p < t := not_lt_of_ge (hpop p hp)
      simp [List.countP_cons, List.countP_append, hp, hxt, hpt] at hc
      omega

/-- A strictly larger input in the row immediately above cannot pop an entry
smaller than the pop from the lower insertion. -/
theorem scheduleRowInsert_adjacent_pop_le
    (bottom middle upper : List α) (x y p q : α)
    (hmiddle : middle.Pairwise (· ≤ ·))
    (hupper : upper.Pairwise (· ≤ ·))
    (hcolumns : RowsFit middle upper) (hxy : x < y)
    (hp : (scheduleRowInsert bottom middle x).2 = some p)
    (hq : (scheduleRowInsert (scheduleRowInsert bottom middle x).1 upper y).2 = some q) :
    p ≤ q := by
  by_contra hpq
  have hqp : q < p := lt_of_not_ge hpq
  have hyq := scheduleRowInsert_pop_ge
    (scheduleRowInsert bottom middle x).1 upper y q hq
  have hxq : x < q := hxy.trans_le hyq
  have hgain := scheduleCountLT_insert_gain bottom middle x q hxq (by
    intro z hz
    have hzp : z = p := Option.some.inj (hz.symm.trans hp)
    simpa only [hzp] using hqp.le)
  have hnewColumns : RowsFit (scheduleRowInsert bottom middle x).1 upper :=
    hcolumns.of_lower_take_le (scheduleRowInsert_take_le bottom middle x)
  have hsaturated := scheduleRowInsert_pop_saturated
    (scheduleRowInsert bottom middle x).1 upper y q
    (scheduleRowInsert_pairwise_le bottom middle x hmiddle) hupper hnewColumns hq
  have hcapacity := hcolumns.countLE_le_countLT q
  omega

/-- If the first insertion is absorbed, the larger adjacent upper input is
also absorbed. This is the endpoint case of the route comparison. -/
theorem scheduleRowInsert_adjacent_none
    (bottom middle upper : List α) (x y : α)
    (hmiddle : middle.Pairwise (· ≤ ·))
    (hupper : upper.Pairwise (· ≤ ·))
    (hcolumns : RowsFit middle upper) (hxy : x < y)
    (hp : (scheduleRowInsert bottom middle x).2 = none) :
    (scheduleRowInsert (scheduleRowInsert bottom middle x).1 upper y).2 = none := by
  cases hq : (scheduleRowInsert (scheduleRowInsert bottom middle x).1 upper y).2 with
  | none => rfl
  | some q =>
      have hyq := scheduleRowInsert_pop_ge
        (scheduleRowInsert bottom middle x).1 upper y q hq
      have hgain := scheduleCountLT_insert_gain bottom middle x q (hxy.trans_le hyq) (by
        intro z hz
        rw [hp] at hz
        contradiction)
      have hnewColumns : RowsFit (scheduleRowInsert bottom middle x).1 upper :=
        hcolumns.of_lower_take_le (scheduleRowInsert_take_le bottom middle x)
      have hsaturated := scheduleRowInsert_pop_saturated
        (scheduleRowInsert bottom middle x).1 upper y q
        (scheduleRowInsert_pairwise_le bottom middle x hmiddle) hupper hnewColumns hq
      have hcapacity := hcolumns.countLE_le_countLT q
      omega

end HigherSpecht
