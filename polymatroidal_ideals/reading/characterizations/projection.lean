import Characterizations.Localization
import CommAlg.Polymatroid.RankIdeal

/-! # Monomial localization preserves the full exchange axiom

The minimal projected generators are precisely the projections of the bases
minimizing the total exponent on the retained coordinates. This proves the
localization theorem simultaneously for every retained subset.
-/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem minimum_layer_dominates {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) {a : Exponent V} (ha : a ∈ B) :
    ∃ b ∈ B, subsetSum b U = lowerRank B U ∧ restrictExponent U b ≤ restrictExponent U a := by
  classical
  let L := B.filter (fun b => subsetSum b U = lowerRank B U)
  have hL : L.Nonempty := by
    obtain ⟨b, hb, he⟩ := lowerRank_attained ⟨a, ha⟩ U
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, he⟩⟩
  obtain ⟨b, hbL, hmin⟩ := L.exists_min_image (fun b => ∑ i ∈ U, (b i - a i)) hL
  obtain ⟨hb, hbmin⟩ := Finset.mem_filter.mp hbL
  refine ⟨b, hb, hbmin, ?_⟩
  intro i
  by_contra hn
  have hi : a i < b i := Nat.lt_of_not_ge hn
  obtain ⟨j, hj, hc⟩ := hB.2 b hb a ha i hi
  have hij : i.val ≠ j := by intro h; subst j; omega
  have hsum := subsetSum_exchange b i j (by omega) U
  have hlo := lowerRank_le hc U
  have hjU : j ∈ U := by
    by_contra hjU
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  have hcmin : subsetSum (exchange b i j) U = lowerRank B U := by
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  have hbetter : (∑ q ∈ U, (exchange b i j q - a q)) < ∑ q ∈ U, (b q - a q) := by
    apply Finset.sum_lt_sum
    · intro q hq
      by_cases hqi : q = i.val
      · subst q
        simp only [exchange_apply, ↓reduceIte, hij]
        omega
      · by_cases hqj : q = j
        · subst q
          simp only [exchange_apply, hqi, ↓reduceIte]
          omega
        · simp [hqi, hqj]
    · refine ⟨i.val, i.property, ?_⟩
      simp only [exchange_apply, ↓reduceIte, hij]
      omega
  have hbad := hmin (exchange b i j) (Finset.mem_filter.mpr ⟨hc, hcmin⟩)
  omega

theorem localFamily_eq_minimum_layer {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) :
    localFamily B U = (B.filter (fun a => subsetSum a U = lowerRank B U)).image
      (restrictExponent U) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨ha, hminimal⟩ :=
      (mem_minimalFamily.mp ha : a ∈ B.image (restrictExponent U) ∧ _)
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c, hc, hcmin, hcb⟩ := minimum_layer_dominates hB U hb
    have he := hminimal (restrictExponent U c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩) hcb
    exact Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hcmin⟩, he⟩
  · rintro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hbmin⟩ := Finset.mem_filter.mp hb
    apply mem_minimalFamily.mpr
    refine ⟨Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    intro c hc hcb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    apply eq_of_le_of_degree_eq hcb
    apply Nat.le_antisymm (degree_mono hcb)
    rw [restrictExponent_degree, restrictExponent_degree, hbmin]
    exact lowerRank_le hz U

theorem localFamily_equigenerated {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) : Equigenerated (localFamily B U) (lowerRank B U) := by
  intro a ha
  rw [localFamily_eq_minimum_layer hB] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [restrictExponent_degree]
  exact (Finset.mem_filter.mp hb).2

theorem restrict_exchange (U : Finset V) (a : Exponent V) (i j : U) :
    restrictExponent U (exchange a i j) = exchange (restrictExponent U a) i j := by
  ext q
  simp only [restrictExponent_apply, exchange_apply]
  have hqi : q.val = i.val ↔ q = i := Subtype.ext_iff.symm
  have hqj : q.val = j.val ↔ q = j := Subtype.ext_iff.symm
  simp only [hqi, hqj]

/-- Proposition 2.8, with actual minimal generators in the retained-variable ring. -/
theorem localFamily_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (U : Finset V) : IsPolymatroidal (localFamily B U) := by
  classical
  refine ⟨⟨lowerRank B U, localFamily_equigenerated hB U⟩, ?_⟩
  intro a ha b hb i hi
  rw [localFamily_eq_minimum_layer hB] at ha hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hx, hxmin⟩ := Finset.mem_filter.mp hx
  obtain ⟨hy, hymin⟩ := Finset.mem_filter.mp hy
  obtain ⟨j, hj, hz⟩ := hB.2 x hx y hy i hi
  have hsum := subsetSum_exchange x i j (by exact Nat.zero_lt_of_lt hi) U
  have hlo := lowerRank_le hz U
  have hjU : j ∈ U := by
    by_contra hjU
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  have hzmin : subsetSum (exchange x i j) U = lowerRank B U := by
    simp only [i.property, hjU, ↓reduceIte] at hsum
    omega
  refine ⟨⟨j, hjU⟩, hj, ?_⟩
  rw [← restrict_exchange, localFamily_eq_minimum_layer hB]
  exact Finset.mem_image.mpr ⟨exchange x i j, Finset.mem_filter.mpr ⟨hz, hzmin⟩, rfl⟩

theorem polymatroidal_locallyEquigenerated {B : Family V} (hB : IsPolymatroidal B) :
    LocallyEquigenerated B :=
  (locallyEquigenerated_iff B).mpr (fun U => ⟨lowerRank B U, localFamily_equigenerated hB U⟩)

end Characterizations
