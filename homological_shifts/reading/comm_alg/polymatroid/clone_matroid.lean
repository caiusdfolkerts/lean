import CommAlg.Polymatroid.SocleReconstruction
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! # The genuine clone matroid of an exchange family

Replacing each coordinate by sufficiently many interchangeable elements turns
the integer exchange axiom into the ordinary matroid basis exchange axiom.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Clone (V : Type*) (d : ℕ) := V × Fin (d + 1)

def clonesOfSet {d : ℕ} (S : Set (Clone V d)) : Finset (Clone V d) :=
  Finset.univ.filter (· ∈ S)

@[simp] theorem mem_clonesOfSet {d : ℕ} (S : Set (Clone V d)) (x : Clone V d) :
    x ∈ clonesOfSet S ↔ x ∈ S := by simp [clonesOfSet]

@[simp] theorem clonesOfSet_coe {d : ℕ} (S : Finset (Clone V d)) :
    clonesOfSet (S : Set (Clone V d)) = S := by ext x; simp

def cloneCount {d : ℕ} (S : Finset (Clone V d)) : Exponent V :=
  ∑ x ∈ S, Finsupp.single x.1 1

@[simp] theorem cloneCount_apply {d : ℕ} (S : Finset (Clone V d)) (i : V) :
    cloneCount S i = (S.filter (fun x => x.1 = i)).card := by
  simp only [cloneCount, Finsupp.finsetSum_apply, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun x _ => by simp [Finsupp.single_apply, eq_comm])

@[simp] theorem cloneCount_degree {d : ℕ} (S : Finset (Clone V d)) :
    (cloneCount S).degree = S.card := by
  simp [cloneCount, map_sum]

theorem cloneCount_mono {d : ℕ} {S T : Finset (Clone V d)} (hST : S ⊆ T) :
    cloneCount S ≤ cloneCount T := by
  intro i
  rw [cloneCount_apply, cloneCount_apply]
  exact Finset.card_le_card (Finset.filter_subset_filter _ hST)

theorem cloneCount_exchange {d : ℕ} {S : Finset (Clone V d)} {e f : Clone V d}
    (he : e ∈ S) (hf : f ∉ S) :
    cloneCount (insert f (S.erase e)) = exchange (cloneCount S) e.1 f.1 := by
  have hfe : f ∉ S.erase e := fun h => hf (Finset.mem_of_mem_erase h)
  have hc : cloneCount (S.erase e) + Finsupp.single e.1 1 = cloneCount S :=
    Finset.sum_erase_add _ _ he
  rw [cloneCount, Finset.sum_insert hfe]
  change Finsupp.single f.1 1 + cloneCount (S.erase e) = _
  rw [exchange, ← hc, add_tsub_cancel_right, add_comm]

def canonicalClones (d : ℕ) (a : Exponent V) : Finset (Clone V d) :=
  Finset.univ.filter (fun x => x.2.val < a x.1)

theorem coordinate_le_degree (a : Exponent V) (i : V) : a i ≤ a.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

theorem cloneCount_canonical (d : ℕ) (a : Exponent V) (ha : ∀ i, a i ≤ d + 1) :
    cloneCount (canonicalClones d a) = a := by
  ext i
  rw [cloneCount_apply]
  simp only [canonicalClones, Finset.filter_filter]
  have he : (Finset.univ.filter (fun x : Clone V d => x.2.val < a x.1 ∧ x.1 = i)) =
      (Finset.univ.filter (fun k : Fin (d + 1) => k.val < a i)).map
        ⟨fun k => (i, k), fun k l h => congrArg Prod.snd h⟩ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hi⟩ := (Finset.mem_filter.mp hx).2
      apply Finset.mem_map.mpr
      refine ⟨x.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [hi] using hx
      · exact Prod.ext hi.symm rfl
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2, rfl⟩
  rw [he, Finset.card_map, Fin.card_filter_val_lt, Nat.min_eq_right (ha i)]

theorem cloneCount_subsetSum {d : ℕ} (S : Finset (Clone V d)) (U : Finset V) :
    subsetSum (cloneCount S) U = (S.filter (fun x => x.1 ∈ U)).card := by
  simp only [subsetSum, cloneCount, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Finsupp.single_apply]

theorem exists_clone_of_count_lt {d : ℕ} {S T : Finset (Clone V d)} {i : V}
    (h : cloneCount S i < cloneCount T i) :
    ∃ f ∈ T, f ∉ S ∧ f.1 = i := by
  by_contra hn
  push_neg at hn
  have hsub : T.filter (fun x => x.1 = i) ⊆ S.filter (fun x => x.1 = i) := by
    intro f hf
    obtain ⟨hfT, hfi⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨?_, hfi⟩
    by_contra hfS
    exact hn f hfT hfS hfi
  have hcard := Finset.card_le_card hsub
  rw [← cloneCount_apply, ← cloneCount_apply] at hcard
  omega

theorem exists_clone_same_of_count_le {d : ℕ} {S T : Finset (Clone V d)}
    {e : Clone V d} (heS : e ∈ S) (heT : e ∉ T)
    (h : cloneCount S e.1 ≤ cloneCount T e.1) :
    ∃ f ∈ T, f ∉ S ∧ f.1 = e.1 := by
  by_contra hn
  push_neg at hn
  have hsub : T.filter (fun x => x.1 = e.1) ⊆ S.filter (fun x => x.1 = e.1) := by
    intro f hf
    obtain ⟨hfT, hfi⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨?_, hfi⟩
    by_contra hfS
    exact hn f hfT hfS hfi
  have hne : T.filter (fun x => x.1 = e.1) ≠ S.filter (fun x => x.1 = e.1) := by
    intro heq
    have hm : e ∈ T.filter (fun x => x.1 = e.1) := by rw [heq]; simp [heS]
    exact heT (Finset.mem_filter.mp hm).1
  have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  rw [← cloneCount_apply, ← cloneCount_apply] at hcard
  omega

set_option maxHeartbeats 800000 in
theorem clone_basis_exchange {B : Family V} {d : ℕ} (hB : IsPolymatroidal B) :
    Matroid.ExchangeProperty
      (fun S : Set (Clone V d) => cloneCount (clonesOfSet S) ∈ B) := by
  intro S T hS hT e he
  let SF := (clonesOfSet S)
  let TF := (clonesOfSet T)
  have heS : e ∈ SF := by simpa [SF] using he.1
  have heT : e ∉ TF := by simpa [TF] using he.2
  by_cases hcount : cloneCount TF e.1 < cloneCount SF e.1
  · obtain ⟨j, hj, hex⟩ := hB.2 (cloneCount SF) hS (cloneCount TF) hT e.1 hcount
    obtain ⟨f, hfT, hfS, hfj⟩ := exists_clone_of_count_lt hj
    refine ⟨f, ⟨by simpa [TF] using hfT, by simpa [SF] using hfS⟩, ?_⟩
    have heq : (clonesOfSet (insert f (S \ {e}))) = insert f (SF.erase e) := by
      ext x
      simp [SF, and_comm]
    change cloneCount (clonesOfSet (insert f (S \ {e}))) ∈ B
    rw [heq, cloneCount_exchange heS hfS, hfj]
    exact hex
  · obtain ⟨f, hfT, hfS, hfe⟩ := exists_clone_same_of_count_le heS heT (Nat.le_of_not_gt hcount)
    refine ⟨f, ⟨by simpa [TF] using hfT, by simpa [SF] using hfS⟩, ?_⟩
    have heq : (clonesOfSet (insert f (S \ {e}))) = insert f (SF.erase e) := by
      ext x
      simp [SF, and_comm]
    change cloneCount (clonesOfSet (insert f (S \ {e}))) ∈ B
    rw [heq, cloneCount_exchange heS hfS, hfe]
    have hpos : 0 < cloneCount SF e.1 := by
      rw [cloneCount_apply]
      exact Finset.card_pos.mpr ⟨e, by simp [heS]⟩
    have hsame : exchange (cloneCount SF) e.1 e.1 = cloneCount SF := by
      ext i
      by_cases hi : i = e.1
      · subst i
        simpa only [exchange_apply, ↓reduceIte] using
          Nat.sub_add_cancel (show 1 ≤ cloneCount SF e.1 by omega)
      · simp [hi]
    rwa [hsame]

/-- No rank condition is assumed: this matroid is constructed solely from the
given finite equigenerated exchange family. -/
def cloneMatroid (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) : Matroid (Clone V d) :=
  Matroid.ofIsBaseOfFinite (Set.toFinite Set.univ)
    (fun S => cloneCount (clonesOfSet S) ∈ B)
    (by
      obtain ⟨a, ha⟩ := hBne
      refine ⟨(canonicalClones d a : Set (Clone V d)), ?_⟩
      have he : (clonesOfSet (canonicalClones d a : Set (Clone V d))) = canonicalClones d a := by
        ext x
        simp
      rw [he]
      rw [cloneCount_canonical d a (fun i => (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))]
      exact ha)
    (clone_basis_exchange hB) (fun _ _ => Set.subset_univ _)

@[simp] theorem cloneMatroid_ground (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) :
    (cloneMatroid B hBne d hdeg hB).E = Set.univ := rfl

@[simp] theorem cloneMatroid_isBase (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (S : Set (Clone V d)) :
    (cloneMatroid B hBne d hdeg hB).IsBase S ↔ cloneCount (clonesOfSet S) ∈ B := Iff.rfl

end CommAlg.Polymatroid
