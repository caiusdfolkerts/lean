import Characterizations.TermOrders.MatroidMatching
import Characterizations.BoundedFamilies
import Mathlib.Data.Finsupp.MonomialOrder

/-! # Linear quotients in every genuine monomial term order

The matching is on actual clone-matroid bases. Common clones are fixed; every
other matched pair gives an exchange feasible at the original base. Additivity
of the given Mathlib monomial order forces one matched exchange to move earlier.
-/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Characterizations.TermOrders
open Classical Finset CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Decreasing order under the actual well-founded multiplicative monomial order. -/
def termBefore (m : MonomialOrder V) (a b : Exponent V) : Prop := m.toSyn b < m.toSyn a

lemma termBefore_irrefl (m : MonomialOrder V) (a : Exponent V) : ¬ termBefore m a a := lt_irrefl _
lemma termBefore_trans (m : MonomialOrder V) {a b c : Exponent V}
    (hab : termBefore m a b) (hbc : termBefore m b c) : termBefore m a c := hbc.trans hab
lemma termBefore_total (m : MonomialOrder V) (a b : Exponent V) (hab : a ≠ b) :
    termBefore m a b ∨ termBefore m b a := by
  exact lt_or_gt_of_ne (fun h => hab (m.toSyn.injective h)) |>.symm

private lemma clone_sum (m : MonomialOrder V) (d : ℕ) (A : Finset (Clone V d)) :
    (∑ x : A, m.toSyn (Finsupp.single x.val.1 1)) = m.toSyn (cloneCount A) := by
  simp only [cloneCount, map_sum]
  exact Finset.sum_attach A (fun x => m.toSyn (Finsupp.single x.1 1))

lemma termOrder_exchange {B : Family V} (hB : IsPolymatroidal B)
    (m : MonomialOrder V) {a b : Exponent V} (ha : a ∈ B) (hb : b ∈ B)
    (hab : termBefore m a b) :
    ∃ i j, b i < a i ∧ a j < b j ∧ exchange b j i ∈ B ∧ termBefore m (exchange b j i) b := by
  obtain ⟨d, hdeg⟩ := hB.1
  let A := canonicalClones d a
  let D := canonicalClones d b
  let M := cloneMatroid B ⟨a, ha⟩ d hdeg hB
  have hAc : cloneCount A = a := cloneCount_canonical d a (fun i =>
    (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))
  have hDc : cloneCount D = b := cloneCount_canonical d b (fun i =>
    (coordinate_le_degree b i).trans (by rw [hdeg b hb]; omega))
  have hA : M.IsBase (A : Set (Clone V d)) := by
    change cloneCount (clonesOfSet (A : Set (Clone V d))) ∈ B
    rwa [clonesOfSet_coe, hAc]
  have hD : M.IsBase (D : Set (Clone V d)) := by
    change cloneCount (clonesOfSet (D : Set (Clone V d))) ∈ B
    rwa [clonesOfSet_coe, hDc]
  obtain ⟨f, hf⟩ := matroid_basis_matching M A D hA hD
  have hsumA : (∑ x : A, m.toSyn (Finsupp.single x.val.1 1)) = m.toSyn a := by
    rw [clone_sum, hAc]
  have hsumD : (∑ x : A, m.toSyn (Finsupp.single (f x).val.1 1)) = m.toSyn b := by
    rw [f.sum_comp (fun y : D => m.toSyn (Finsupp.single y.val.1 1)), clone_sum, hDc]
  have hsome : ∃ x : A, m.toSyn (Finsupp.single (f x).val.1 1) < m.toSyn (Finsupp.single x.val.1 1) := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset A)) => hn x)
    rw [hsumA, hsumD] at hh
    exact (not_le_of_gt hab) hh
  obtain ⟨x, hx⟩ := hsome
  have hxD : x.val ∉ D := by
    intro h
    have he := matroid_matching_fixes_common M A D f hf x h
    rw [he] at hx
    exact (lt_irrefl _ hx)
  obtain ⟨hfA, hbase⟩ := matroid_matching_exchange M A D hA hD f hf x hxD
  have hi : b x.val.1 < a x.val.1 := by
    have h₁ : x.val.2.val < a x.val.1 := by exact (mem_filter.mp x.property).2
    have h₂ : ¬ x.val.2.val < b x.val.1 := by simpa [D, canonicalClones] using hxD
    omega
  have hj : a (f x).val.1 < b (f x).val.1 := by
    have h₁ : (f x).val.2.val < b (f x).val.1 := by exact (mem_filter.mp (f x).property).2
    have h₂ : ¬ (f x).val.2.val < a (f x).val.1 := by simpa [A, canonicalClones] using hfA
    omega
  have hw : exchange b (f x).val.1 x.val.1 ∈ B := by
    change cloneCount (clonesOfSet (insert x.val ((D : Set (Clone V d)) \ {(f x).val}))) ∈ B at hbase
    have he : clonesOfSet (insert x.val ((D : Set (Clone V d)) \ {(f x).val})) =
        insert x.val (D.erase (f x).val) := by
      ext z
      simp [and_comm]
    rw [he, cloneCount_exchange (f x).property hxD, hDc] at hbase
    exact hbase
  have hpos : 0 < b (f x).val.1 := Nat.zero_lt_of_lt hj
  have hle : Finsupp.single (f x).val.1 1 ≤ b := by
    intro v
    by_cases he : v = (f x).val.1
    · subst v; simpa only [Finsupp.single_eq_same] using Nat.succ_le_of_lt hpos
    · simp [Finsupp.single_apply, he, Ne.symm he]
  refine ⟨x.val.1, (f x).val.1, hi, hj, hw, ?_⟩
  change m.toSyn b < m.toSyn (exchange b (f x).val.1 x.val.1)
  calc
    m.toSyn b = m.toSyn (b - Finsupp.single (f x).val.1 1) +
        m.toSyn (Finsupp.single (f x).val.1 1) := by rw [← map_add, tsub_add_cancel_of_le hle]
    _ < m.toSyn (b - Finsupp.single (f x).val.1 1) + m.toSyn (Finsupp.single x.val.1 1) :=
      add_lt_add_of_le_of_lt le_rfl hx
    _ = m.toSyn (exchange b (f x).val.1 x.val.1) := by rw [← map_add]; rfl

/-- Theorem 3.12, for every actual admissible monomial term order, with literal
polynomial colon ideals and no replacement by a variable-permutation order. -/
theorem polymatroidal_termOrder_linearQuotients {k : Type*} [CommSemiring k]
    {B : Family V} (hB : IsPolymatroidal B) (m : MonomialOrder V) :
    HasLinearQuotients k B (termBefore m) := by
  apply linearQuotients_of_witness
  intro a ha b hb hab
  obtain ⟨i, j, hi, hj, hw, hwb⟩ := termOrder_exchange hB m ha hb hab
  have hji : j ≠ i := by intro he; subst j; omega
  exact ⟨exchange b j i, hw, hwb, i, Characterizations.exchange_sub_self b hji, hi⟩

end Characterizations.TermOrders
