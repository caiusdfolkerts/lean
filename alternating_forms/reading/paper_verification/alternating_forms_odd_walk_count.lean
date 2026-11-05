module

public import PaperVerification.AlternatingFormsOddExteriorBasis
public import PaperVerification.AlternatingFormsGoodPathBounds
public import PaperVerification.AlternatingFormsBooleanGraphWalks

/-!
# The good odd exterior words count the paper's actual strip walks

An original exterior position `i` becomes downward step `i+1`.  Both
endpoints of a strip walk are upward steps, so every good downward set
of length `2*k+3` comes from exactly one increasing exterior word.
The proof constructs this equivalence using sorted finite sets.  It
therefore identifies the full good-word basis with the actual graph
walk count, including the degrees above the vanishing cutoff.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms

open BooleanWalks

/-- The initial fixed up-step shifts every original exterior position by one. -/
def oddDownstepShift (k : ℕ) : Fin (2*k+1) ↪ Fin (2*k+3) where
  toFun i := ⟨i.val+1, by have := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have := congrArg Fin.val h
    change i.val+1=j.val+1 at this
    omega

def oddIndexDownset {k s : ℕ} (I : Fin s → Fin (2*k+1)) : Finset (Fin (2*k+3)) :=
  (GoodPaths.selectedSet I).map (oddDownstepShift k)

theorem oddIndexDownset_card {k s : ℕ} {I : Fin s → Fin (2*k+1)}
    (hI : StrictMono I) : (oddIndexDownset I).card=s := by
  rw [oddIndexDownset, Finset.card_map, GoodPaths.selectedSet_card hI]

theorem oddIndexDownset_prefix {k s : ℕ} {I : Fin s → Fin (2*k+1)}
    (hI : StrictMono I) (q : ℕ) :
    prefixCount (oddIndexDownset I) q = GoodPaths.selectedBefore I q := by
  rw [prefixCount, oddIndexDownset, Finset.filter_map, Finset.card_map]
  change ((GoodPaths.selectedSet I).filter (fun x => x.val+1<q)).card =
    GoodPaths.selectedBefore I q
  exact (GoodPaths.selectedBefore_eq_filter_card hI q).symm

def goodOddIndexToGoodSubset {k s : ℕ} (I : GoodOddIndex k s) :
    GoodSubset (2*k+3) s :=
  ⟨⟨oddIndexDownset I.val.val, oddIndexDownset_card I.val.property⟩, by
    intro q hq
    change 2*prefixCount (oddIndexDownset I.val.val) q≤q ∧
      q+2*s≤2*k+3+2*prefixCount (oddIndexDownset I.val.val) q
    rw [oddIndexDownset_prefix I.val.property]
    exact (GoodPaths.good_bounds_iff_prefix_strip k s I.val.val I.val.property).mp
      I.property q hq⟩

theorem goodOddIndexToGoodSubset_injective (k s : ℕ) :
    Function.Injective (goodOddIndexToGoodSubset (k := k) (s := s)) := by
  intro I J h
  have hs : oddIndexDownset I.val.val = oddIndexDownset J.val.val :=
    congrArg (fun S : GoodSubset (2*k+3) s => S.val.val) h
  have hi : GoodPaths.selectedSet I.val.val = GoodPaths.selectedSet J.val.val :=
    Finset.map_injective (oddDownstepShift k) hs
  apply Subtype.ext
  exact (GoodPaths.increasingSelectionEquiv s (2*k+1)).injective (Subtype.ext hi)

/-- A good downward set contains neither of the two endpoint steps. -/
theorem goodSubset_odd_interior {k s : ℕ} (S : GoodSubset (2*k+3) s)
    (j : Fin (2*k+3)) (hj : j∈S.val.val) :
    0<j.val ∧ j.val<2*k+2 := by
  have hfirst : (0 : Fin (2*k+3)) ∉ S.val.val := by
    intro hzero
    have hc := prefixCount_succ S.val.val 0
    have hd : selectedAt S.val.val 0 = 1 := by
      simpa only [Fin.val_zero, if_pos hzero] using
        selectedAt_position S.val.val (0 : Fin (2*k+3))
    have hc' : prefixCount S.val.val 1 = 1 := by
      simpa only [prefixCount_zero, hd, Nat.zero_add] using hc
    have hb : 2 * prefixCount S.val.val 1 ≤ 1 := (S.property 1 (by omega)).1
    rw [hc'] at hb
    norm_num at hb
  have hlast : (⟨2*k+2, by omega⟩ : Fin (2*k+3)) ∉ S.val.val := by
    intro hlast
    have hc := prefixCount_succ S.val.val (2*k+2)
    have hd := selectedAt_position S.val.val (⟨2*k+2, by omega⟩ : Fin (2*k+3))
    simp only [Fin.val_mk, if_pos hlast] at hd
    have ha := prefixCount_all S.val.val (2*k+3) le_rfl
    rw [S.val.property] at ha
    change prefixCount S.val.val (2*k+3) =
      prefixCount S.val.val (2*k+2) + selectedAt S.val.val (2*k+2) at hc
    rw [hd, ha] at hc
    have hb := (S.property (2*k+2) (by omega)).2
    omega
  have hj0 : j.val≠0 := by
    intro hz
    have he : j = (0 : Fin (2*k+3)) := Fin.ext hz
    exact hfirst (he ▸ hj)
  have hjlast : j.val≠2*k+2 := by
    intro hz
    have he : j = (⟨2*k+2, by omega⟩ : Fin (2*k+3)) := Fin.ext hz
    exact hlast (he ▸ hj)
  have hjlt := j.isLt
  omega

/-- Sort the downward steps and remove the initial fixed up-step. -/
def goodSubsetToOddIndex {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    Fin s → Fin (2*k+1) := fun i =>
  ⟨(S.val.val.orderEmbOfFin S.val.property i).val-1, by
    have h := goodSubset_odd_interior S _
      (S.val.val.orderEmbOfFin_mem S.val.property i)
    omega⟩

theorem goodSubsetToOddIndex_strictMono {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    StrictMono (goodSubsetToOddIndex S) := by
  intro i j hij
  have hord := (S.val.val.orderEmbOfFin S.val.property).strictMono hij
  have hi := goodSubset_odd_interior S _
    (S.val.val.orderEmbOfFin_mem S.val.property i)
  have hj := goodSubset_odd_interior S _
    (S.val.val.orderEmbOfFin_mem S.val.property j)
  change (S.val.val.orderEmbOfFin S.val.property i).val <
    (S.val.val.orderEmbOfFin S.val.property j).val at hord
  change (S.val.val.orderEmbOfFin S.val.property i).val-1 <
    (S.val.val.orderEmbOfFin S.val.property j).val-1
  omega

theorem oddIndexDownset_goodSubsetToOddIndex {k s : ℕ}
    (S : GoodSubset (2*k+3) s) : oddIndexDownset (goodSubsetToOddIndex S)=S.val.val := by
  unfold oddIndexDownset GoodPaths.selectedSet
  rw [Finset.map_eq_image, Finset.image_image]
  have hf : (fun i => oddDownstepShift k (goodSubsetToOddIndex S i)) =
      S.val.val.orderEmbOfFin S.val.property := by
    funext i
    apply Fin.ext
    have hi := goodSubset_odd_interior S _
      (S.val.val.orderEmbOfFin_mem S.val.property i)
    change (S.val.val.orderEmbOfFin S.val.property i).val-1+1 =
      (S.val.val.orderEmbOfFin S.val.property i).val
    omega
  simp only [Function.comp_def]
  rw [hf]
  exact Finset.image_orderEmbOfFin_univ S.val.val S.val.property

theorem goodSubsetToOddIndex_good {k s : ℕ} (S : GoodSubset (2*k+3) s) :
    ∀ i, 2*i.val≤(goodSubsetToOddIndex S i).val ∧
      (goodSubsetToOddIndex S i).val+2*s≤2*k+2+2*i.val := by
  apply (GoodPaths.good_bounds_iff_prefix_strip k s (goodSubsetToOddIndex S)
    (goodSubsetToOddIndex_strictMono S)).mpr
  intro q hq
  rw [← oddIndexDownset_prefix (goodSubsetToOddIndex_strictMono S),
    oddIndexDownset_goodSubsetToOddIndex]
  exact S.property q hq

theorem goodOddIndexToGoodSubset_surjective (k s : ℕ) :
    Function.Surjective (goodOddIndexToGoodSubset (k := k) (s := s)) := by
  intro S
  refine ⟨⟨⟨goodSubsetToOddIndex S, goodSubsetToOddIndex_strictMono S⟩,
    goodSubsetToOddIndex_good S⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact oddIndexDownset_goodSubsetToOddIndex S

/-- Every good exterior word is precisely one bounded binary strip walk. -/
def goodOddIndexGoodSubsetEquiv (k s : ℕ) : GoodOddIndex k s ≃ GoodSubset (2*k+3) s :=
  Equiv.ofBijective goodOddIndexToGoodSubset
    ⟨goodOddIndexToGoodSubset_injective k s, goodOddIndexToGoodSubset_surjective k s⟩

theorem card_goodOddIndex_eq_paperWalkCount_of_le (k s : ℕ) (hs : s≤k+1) :
    Fintype.card (GoodOddIndex k s) = StripWalks.paperWalkCount (2*k+1) s := by
  calc
    Fintype.card (GoodOddIndex k s) = Fintype.card (GoodSubset (2*k+3) s) :=
      Fintype.card_congr (goodOddIndexGoodSubsetEquiv k s)
    _ = StripWalks.walkCount (2*k+3-2*s) (2*k+3) :=
      card_goodSubset_eq_walkCount (2*k+3) s (by omega)
    _ = StripWalks.paperWalkCount (2*k+1) s := by
      unfold StripWalks.paperWalkCount
      congr 1 <;> omega

/-- A width-zero strip has no positive-length walk. -/
theorem stripWalkCount_zero_width (N : ℕ) (hN : 0<N) :
    StripWalks.walkCount 0 N=0 := by
  letI : Subsingleton (Fin (0+1)) := Fin.subsingleton_iff_le_one.mpr (by decide)
  letI : IsEmpty {p : (SimpleGraph.pathGraph (0+1)).Walk 0 (Fin.last 0) // p.length=N} :=
    ⟨fun p => by
      have hz := p.val.nil_of_subsingleton.length_eq_zero
      have hn := p.property
      omega⟩
  exact Fintype.card_of_isEmpty

theorem paperWalkCount_odd_above_cutoff (k s : ℕ) (hs : k+1<s) :
    StripWalks.paperWalkCount (2*k+1) s=0 := by
  unfold StripWalks.paperWalkCount
  rw [show 2*k+1+2-2*s=0 by omega]
  exact stripWalkCount_zero_width _ (by omega)

/-- The count equality is valid in every natural exterior degree. -/
theorem card_goodOddIndex_eq_paperWalkCount (k s : ℕ) :
    Fintype.card (GoodOddIndex k s) = StripWalks.paperWalkCount (2*k+1) s := by
  by_cases hs : s≤k+1
  · exact card_goodOddIndex_eq_paperWalkCount_of_le k s hs
  · have hs' : k+1<s := by omega
    letI := goodOddIndex_isEmpty k s hs'
    rw [Fintype.card_of_isEmpty, paperWalkCount_odd_above_cutoff k s hs']

/-- The odd path pencil has exactly the paper's Hilbert function in all degrees. -/
theorem oddExteriorQuotientDegree_finrank_eq_paperWalkCount
    {K : Type*} [Field K] [CharZero K] (k s : ℕ) :
    Module.finrank K (OddExteriorQuotientDegree (K := K) k s) =
      StripWalks.paperWalkCount (2*k+1) s := by
  rw [Module.finrank_eq_card_basis (oddExteriorBasis (K := K) k s),
    card_goodOddIndex_eq_paperWalkCount]

end PaperVerification.AlternatingForms
