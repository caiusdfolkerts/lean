import CommAlg.Polymatroid.Exponents
import Mathlib.Data.Finset.Lattice.Fold

/-! # Minimal projected generators and local subset minima -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def minimalFamily (B : Family V) : Family V :=
  B.filter (fun a => ∀ b ∈ B, b ≤ a → b = a)

@[simp] theorem mem_minimalFamily {B : Family V} {a : Exponent V} :
    a ∈ minimalFamily B ↔ a ∈ B ∧ ∀ b ∈ B, b ≤ a → b = a := by
  simp [minimalFamily]

theorem minimalFamily_subset (B : Family V) : minimalFamily B ⊆ B := by
  intro a ha
  exact (mem_minimalFamily.mp ha).1

theorem minimal_below {B : Family V} {a : Exponent V} (ha : a ∈ B) :
    ∃ b ∈ minimalFamily B, b ≤ a := by
  obtain ⟨b, hba, hb, hmin⟩ := B.exists_le_minimal ha
  exact ⟨b, mem_minimalFamily.mpr ⟨hb, fun c hc hcb => le_antisymm hcb (hmin hc hcb)⟩, hba⟩

theorem minimalFamily_nonempty {B : Family V} (hB : B.Nonempty) :
    (minimalFamily B).Nonempty := by
  obtain ⟨a, ha⟩ := hB
  obtain ⟨b, hb, _⟩ := minimal_below ha
  exact ⟨b, hb⟩

theorem minimalFamily_antichain (B : Family V) : Antichain (minimalFamily B) := by
  intro a ha b hb hab
  exact (mem_minimalFamily.mp hb).2 a ((mem_minimalFamily.mp ha).1) hab

theorem contains_minimalFamily (B : Family V) (a : Exponent V) :
    Contains (minimalFamily B) a ↔ Contains B a := by
  constructor
  · rintro ⟨b, hb, hba⟩
    exact ⟨b, minimalFamily_subset B hb, hba⟩
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc, hcb⟩ := minimal_below hb
    exact ⟨c, hc, hcb.trans hba⟩

theorem minimalFamily_eq {B : Family V} (hB : Antichain B) : minimalFamily B = B := by
  ext a
  simp only [mem_minimalFamily]
  exact ⟨And.left, fun ha => ⟨ha, fun b hb hba => hB b hb a ha hba⟩⟩

theorem monomialIdeal_minimalFamily (k : Type*) [CommSemiring k] (B : Family V) :
    monomialIdeal k (minimalFamily B) = monomialIdeal k B := by
  ext f
  simp only [mem_monomialIdeal_iff, contains_minimalFamily]

def project (U : Finset V) (a : Exponent V) : Exponent V := a.filter (· ∈ U)

@[simp] theorem project_apply (U : Finset V) (a : Exponent V) (i : V) :
    project U a i = if i ∈ U then a i else 0 := rfl

theorem project_le (U : Finset V) (a : Exponent V) : project U a ≤ a := by
  intro i
  simp only [project_apply]
  split <;> omega

theorem project_mono (U : Finset V) {a b : Exponent V} (hab : a ≤ b) :
    project U a ≤ project U b := by
  intro i
  simp only [project_apply]
  split
  · exact hab i
  · exact le_rfl

theorem project_project {U W : Finset V} (hWU : W ⊆ U) (a : Exponent V) :
    project W (project U a) = project W a := by
  ext i
  by_cases hiW : i ∈ W
  · simp [hiW, hWU hiW]
  · simp [hiW]

@[simp] theorem project_univ (a : Exponent V) : project Finset.univ a = a := by
  ext i
  simp

@[simp] theorem project_empty (a : Exponent V) : project ∅ a = 0 := by
  ext i
  simp

theorem subsetSum_project {U W : Finset V} (hWU : W ⊆ U) (a : Exponent V) :
    subsetSum (project U a) W = subsetSum a W := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [hWU hi]

theorem degree_project (U : Finset V) (a : Exponent V) :
    (project U a).degree = subsetSum a U := by
  rw [Finsupp.degree_eq_sum]
  simp only [project_apply, ← Finset.sum_filter]
  simp [subsetSum]

def localize (B : Family V) (U : Finset V) : Family V :=
  minimalFamily (B.image (project U))

theorem localize_nonempty {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    (localize B U).Nonempty := minimalFamily_nonempty (hB.image _)

theorem localize_antichain (B : Family V) (U : Finset V) : Antichain (localize B U) :=
  minimalFamily_antichain _

theorem localize_member {B : Family V} {U : Finset V} {b : Exponent V}
    (hb : b ∈ localize B U) : ∃ a ∈ B, project U a = b :=
  Finset.mem_image.mp (minimalFamily_subset _ hb)

theorem localize_supported {B : Family V} {U : Finset V} {b : Exponent V}
    (hb : b ∈ localize B U) : project U b = b := by
  obtain ⟨a, ha, rfl⟩ := localize_member hb
  exact project_project le_rfl a

theorem localize_below {B : Family V} {U : Finset V} {a : Exponent V}
    (ha : a ∈ B) : ∃ b ∈ localize B U, b ≤ project U a :=
  minimal_below (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem contains_localize (B : Family V) (U : Finset V) (a : Exponent V) :
    Contains (localize B U) a ↔ ∃ b ∈ B, project U b ≤ a := by
  rw [localize, contains_minimalFamily]
  simp [Contains]

def lowerRank (B : Family V) (U : Finset V) : ℕ :=
  if h : B.Nonempty then B.inf' h (fun a => subsetSum a U) else 0

theorem lowerRank_le {B : Family V} {a : Exponent V} (ha : a ∈ B) (U : Finset V) :
    lowerRank B U ≤ subsetSum a U := by
  rw [lowerRank, dif_pos ⟨a, ha⟩]
  exact Finset.inf'_le _ ha

theorem lowerRank_attained {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    ∃ a ∈ B, subsetSum a U = lowerRank B U := by
  obtain ⟨a, ha, hle⟩ := (Finset.inf'_le_iff hB).mp
    (le_rfl : B.inf' hB (fun a => subsetSum a U) ≤ B.inf' hB (fun a => subsetSum a U))
  exact ⟨a, ha, le_antisymm (by simpa [lowerRank, hB] using hle) (lowerRank_le ha U)⟩

theorem le_lowerRank {B : Family V} (hB : B.Nonempty) {U : Finset V} {r : ℕ}
    (h : ∀ a ∈ B, r ≤ subsetSum a U) : r ≤ lowerRank B U := by
  rw [lowerRank, dif_pos hB]
  exact Finset.le_inf' hB _ h

@[simp] theorem lowerRank_empty (B : Family V) : lowerRank B ∅ = 0 := by
  unfold lowerRank
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    exact Nat.eq_zero_of_le_zero (by simpa using Finset.inf'_le (fun a => subsetSum a ∅) ha)
  · rfl

theorem lowerRank_mono {B : Family V} (hB : B.Nonempty) {U W : Finset V} (hUW : U ⊆ W) :
    lowerRank B U ≤ lowerRank B W := by
  apply le_lowerRank hB
  intro a ha
  exact (lowerRank_le ha U).trans (subsetSum_mono a hUW)

theorem localize_sum_ge {B : Family V} {U W : Finset V} (hWU : W ⊆ U)
    {b : Exponent V} (hb : b ∈ localize B U) : lowerRank B W ≤ subsetSum b W := by
  obtain ⟨a, ha, rfl⟩ := localize_member hb
  rw [subsetSum_project hWU]
  exact lowerRank_le ha W

/-- Projection and removal of redundant monomials preserve every subset minimum. -/
theorem lowerRank_localize {B : Family V} (hB : B.Nonempty)
    {U W : Finset V} (hWU : W ⊆ U) : lowerRank (localize B U) W = lowerRank B W := by
  apply le_antisymm
  · obtain ⟨a, ha, hmin⟩ := lowerRank_attained hB W
    obtain ⟨b, hb, hba⟩ := localize_below (U := U) ha
    calc
      lowerRank (localize B U) W ≤ subsetSum b W := lowerRank_le hb W
      _ ≤ subsetSum (project U a) W := Finset.sum_le_sum (fun i _ => hba i)
      _ = lowerRank B W := (subsetSum_project hWU a).trans hmin
  · exact le_lowerRank (localize_nonempty hB U) (fun b hb => localize_sum_ge hWU hb)

def LocallyEquigenerated (B : Family V) : Prop :=
  ∀ U : Finset V, ∃ d, Equigenerated (localize B U) d

theorem localize_degree {B : Family V} (hB : B.Nonempty) (hl : LocallyEquigenerated B)
    {U : Finset V} {b : Exponent V} (hb : b ∈ localize B U) : b.degree = lowerRank B U := by
  obtain ⟨d, hd⟩ := hl U
  obtain ⟨a, ha, hmin⟩ := lowerRank_attained (localize_nonempty hB U) U
  rw [lowerRank_localize hB le_rfl] at hmin
  have haD : a.degree = subsetSum a U := by
    rw [← degree_project, localize_supported ha]
  exact (hd b hb).trans ((hd a ha).symm.trans (haD.trans hmin))

def Supermodular (r : Finset V → ℕ) : Prop :=
  ∀ A B, r A + r B ≤ r (A ∪ B) + r (A ∩ B)

/-- Lemma 2.4: local equigeneration forces supermodularity. -/
theorem lowerRank_supermodular {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) : Supermodular (lowerRank B) := by
  intro A C
  obtain ⟨b, hb, hmin⟩ := lowerRank_attained (localize_nonempty hB (A ∪ C)) (A ∩ C)
  rw [lowerRank_localize hB (Finset.inter_subset_left.trans Finset.subset_union_left)] at hmin
  have hdeg := localize_degree hB hl hb
  have hsum : subsetSum b (A ∪ C) = lowerRank B (A ∪ C) := by
    rw [← degree_project, localize_supported hb]
    exact hdeg
  calc
    lowerRank B A + lowerRank B C ≤ subsetSum b A + subsetSum b C :=
      Nat.add_le_add (localize_sum_ge Finset.subset_union_left hb)
        (localize_sum_ge Finset.subset_union_right hb)
    _ = subsetSum b (A ∪ C) + subsetSum b (A ∩ C) := subsetSum_union_inter b A C
    _ = _ := by rw [hsum, hmin]

end CommAlg.Polymatroid
