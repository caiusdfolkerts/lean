import Characterizations.RealHull
import CommAlg.Polymatroid.RankBases
import CommAlg.Polymatroid.IdealProducts

/-! # The full integer base family of a locally equigenerated monomial ideal -/
noncomputable section
namespace Characterizations
open Classical CommAlg.Polymatroid Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def lowerBaseFamily (r : Finset V → ℕ) (d : ℕ) : Family V :=
  (Finset.Iic (constExponent d)).filter (fun a => a.degree = d ∧ LowerFeasible r a)

@[simp] theorem mem_lowerBaseFamily (r : Finset V → ℕ) (d : ℕ) (a : Exponent V) :
    a ∈ lowerBaseFamily r d ↔ a.degree = d ∧ LowerFeasible r a := by
  classical
  simp only [lowerBaseFamily, Finset.mem_filter, Finset.mem_Iic]
  exact ⟨And.right, fun h => ⟨fun i => (coordinate_le_degree a i).trans h.1.le, h⟩⟩

theorem lowerBaseFamily_equigenerated (r : Finset V → ℕ) (d : ℕ) :
    Equigenerated (lowerBaseFamily r d) d := fun a ha => ((mem_lowerBaseFamily r d a).mp ha).1

theorem contains_lowerBaseFamily_iff {r : Finset V → ℕ} (hr : Supermodular r)
    (hr0 : r ∅ = 0) {d : ℕ} (hrd : r Finset.univ = d) (hrle : ∀ U, r U ≤ d)
    (a : Exponent V) : Contains (lowerBaseFamily r d) a ↔ LowerFeasible r a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    exact (((mem_lowerBaseFamily r d b).mp hb).2 U).trans
      (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    obtain ⟨b, hba, hd, hb⟩ := exists_lower_base_below hr hr0 hrd hrle ha
    exact ⟨b, (mem_lowerBaseFamily r d b).mpr ⟨hd, hb⟩, hba⟩

theorem lowerBaseFamily_polymatroidal {r : Finset V → ℕ} (hr : Supermodular r)
    (hr0 : r ∅ = 0) {d : ℕ} (hrd : r Finset.univ = d) (hrle : ∀ U, r U ≤ d) :
    IsPolymatroidal (lowerBaseFamily r d) :=
  polymatroidal_of_lower_inequalities (lowerBaseFamily_equigenerated r d) hr
    (contains_lowerBaseFamily_iff hr hr0 hrd hrle)

theorem lowerRank_univ_of_equigenerated {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) : lowerRank B Finset.univ = d := by
  obtain ⟨a, ha, he⟩ := lowerRank_attained hB Finset.univ
  simpa only [subsetSum_univ, hd a ha] using he.symm

theorem lowerRank_le_degree {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V) : lowerRank B U ≤ d := by
  rw [← lowerRank_univ_of_equigenerated hB hd]
  exact lowerRank_mono hB (Finset.subset_univ U)

theorem subset_lowerBaseFamily {B : Family V} {d : ℕ} (hd : Equigenerated B d) :
    B ⊆ lowerBaseFamily (lowerRank B) d := by
  intro a ha
  exact (mem_lowerBaseFamily _ _ _).mpr ⟨hd a ha, fun U => lowerRank_le ha U⟩

theorem canonicalLowerBases_polymatroidal {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    IsPolymatroidal (lowerBaseFamily (lowerRank B) d) :=
  lowerBaseFamily_polymatroidal (lowerRank_supermodular hB hl) (lowerRank_empty B)
    (lowerRank_univ_of_equigenerated hB hd) (lowerRank_le_degree hB hd)

theorem contains_canonicalLowerBases_iff {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) (a : Exponent V) :
    Contains (lowerBaseFamily (lowerRank B) d) a ↔ LowerFeasible (lowerRank B) a :=
  contains_lowerBaseFamily_iff (lowerRank_supermodular hB hl) (lowerRank_empty B)
    (lowerRank_univ_of_equigenerated hB hd) (lowerRank_le_degree hB hd) a

end Characterizations
