import Characterizations.ThickeningClosure
import Characterizations.Strands.FiniteHoles
import Characterizations.Strands.SocleTor
import Characterizations.Strands.DeletedBetti

/-! # Genuine Tor regularity of a minimal local obstruction -/
noncomputable section
namespace Characterizations
open Classical CommAlg CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The maximum defining Castelnuovo–Mumford regularity: all actual derived-Tor
degrees are bounded by r+i, and that bound occurs. -/
def IsTorRegularity (B : Family V) (r : ℕ) : Prop :=
  (∀ i a, bettiNumber (k := k) B a i ≠ 0 → a.degree ≤ r+i) ∧
    ∃ i a, bettiNumber (k := k) B a i ≠ 0 ∧ a.degree = r+i

theorem torRegularity_unique {B : Family V} {r s : ℕ}
    (hr : IsTorRegularity (k := k) B r) (hs : IsTorRegularity (k := k) B s) : r = s := by
  obtain ⟨i,a,ha,hda⟩ := hr.2
  obtain ⟨j,b,hb,hdb⟩ := hs.2
  have h₁ := hs.1 i a ha
  have h₂ := hr.1 j b hb
  omega

theorem totalBettiNumber_pos_iff (B : Family V) (i j : ℕ) :
    0 < Strands.totalBettiNumber (k := k) B i j ↔
      ∃ a, a.degree = j ∧ 0 < bettiNumber (k := k) B a i := by
  rw [Strands.totalBettiNumber, Finset.sum_pos_iff]
  simp

/-- The multigraded maximum agrees exactly with the usual total-degree formula. -/
theorem torRegularity_iff_total (B : Family V) (r : ℕ) :
    IsTorRegularity (k := k) B r ↔
      (∀ i j, 0 < Strands.totalBettiNumber (k := k) B i j → j ≤ r+i) ∧
        ∃ i j, 0 < Strands.totalBettiNumber (k := k) B i j ∧ j = r+i := by
  constructor
  · rintro ⟨hu,⟨i,a,ha,hda⟩⟩
    refine ⟨?_,i,a.degree,(totalBettiNumber_pos_iff B i _).mpr
      ⟨a,rfl,Nat.pos_of_ne_zero ha⟩,hda⟩
    intro i j hij
    obtain ⟨a,had,ha⟩ := (totalBettiNumber_pos_iff B i j).mp hij
    exact had ▸ hu i a (Nat.ne_of_gt ha)
  · rintro ⟨hu,⟨i,j,hij,hj⟩⟩
    refine ⟨?_,?_⟩
    · intro i a ha
      exact hu i a.degree ((totalBettiNumber_pos_iff B i _).mpr ⟨a,rfl,Nat.pos_of_ne_zero ha⟩)
    · obtain ⟨a,had,ha⟩ := (totalBettiNumber_pos_iff B i j).mp hij
      exact ⟨i,a,Nat.ne_of_gt ha,had.trans hj⟩

theorem generator_bettiNumber_pos {B : Family V} {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ B) : 0 < bettiNumber (k := k) B a 0 := by
  rw [bettiNumber_pos_iff_faces]
  apply nonzeroHomology_zero_of_only_empty
  · exact ⟨by simp,by simpa using (show Contains B a from ⟨a,ha,le_rfl⟩)⟩
  · intro s hs
    obtain ⟨b,hb,hba⟩ := hs.2
    have hdeg := degree_mono hba
    have he := Strands.degree_sub_faceExponent hs.1
    rw [hd b hb] at hdeg
    rw [hd a ha] at he
    exact Finset.card_eq_zero.mp (by omega)

theorem polymatroidal_torRegularity {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hp : IsPolymatroidal B) :
    IsTorRegularity (k := k) B d := by
  constructor
  · intro i a ha
    have he : a.degree = d+i := by
      by_contra hn
      have hex := Strands.polymatroidal_faces_exact_off_linear (k := k) B hB d hd hp a i hn
      have hh := (bettiNumber_pos_iff_faces B a i).mp (Nat.pos_of_ne_zero ha)
      exact ((nonzeroHomology_iff_not_exactIn _ _).mp hh) hex
    exact he.le
  · obtain ⟨a,ha⟩ := hB
    exact ⟨0,a,Nat.ne_of_gt (generator_bettiNumber_pos hd ha),by simpa using hd a ha⟩

theorem torRegularity_of_top_hole [Nonempty V] {B : Family V} (hB : B.Nonempty)
    (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    {a : Exponent V} (ha : a ∈ holeSet B) (hmax : ∀ b ∈ holeSet B, b.degree ≤ a.degree)
    (hmul : ∀ j, Contains B (a+Finsupp.single j 1)) :
    IsTorRegularity (k := k) B (a.degree+1) := by
  have hda : d ≤ a.degree := by
    have h := ha.1 Finset.univ
    simpa only [lowerRank_univ_of_equigenerated hB hd, subsetSum_univ] using h
  constructor
  · intro i b hb
    have h := Strands.finite_holes_betti_degree_bound (k := k) B
      (lowerBaseFamily (lowerRank B) d) (fun c hc =>
        (contains_canonicalLowerBases_iff hB hl hd c).mpr
          (fun U => by
            obtain ⟨z,hz,hzc⟩ := hc
            exact (lowerRank_le hz U).trans (Finset.sum_le_sum (fun j _ => hzc j))))
      a.degree (fun c hc hout => hmax c
        ⟨(contains_canonicalLowerBases_iff hB hl hd c).mp hc,hout⟩)
      (hB.mono (subset_lowerBaseFamily hd)) d (lowerBaseFamily_equigenerated _ _)
      (canonicalLowerBases_polymatroidal hB hl hd) (by omega) b i hb
    omega
  · have hc : Fintype.card V = (Fintype.card V-1)+1 := by
      have hpos := Fintype.card_pos (α := V)
      omega
    refine ⟨Fintype.card V-1,a+faceExponent Finset.univ,?_,?_⟩
    · rw [Strands.socle_bettiNumber_eq_one B a ha.2 hmul _ hc]
      exact one_ne_zero
    · rw [map_add, Strands.degree_faceExponent, Finset.card_univ]
      omega

theorem locallyEquigenerated_of_proper_polymatroidal {B : Family V} {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U)) :
    LocallyEquigenerated B := by
  intro U
  by_cases hU : U = Finset.univ
  · subst U
    rw [localize_univ_of_antichain hd.antichain]
    exact ⟨d,hd⟩
  · exact (hloc U ((Finset.subset_univ U).ssubset_of_ne hU)).1

theorem holeSet_nonempty_of_nonclosed {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) (hne : B ≠ lowerBaseFamily (lowerRank B) d) :
    (holeSet B).Nonempty := by
  have hnot : ¬ lowerBaseFamily (lowerRank B) d ⊆ B := fun h =>
    hne (Finset.Subset.antisymm (subset_lowerBaseFamily hd) h)
  obtain ⟨a,haJ,haB⟩ := Finset.not_subset.mp hnot
  obtain ⟨had,hlo⟩ := (mem_lowerBaseFamily _ _ _).mp haJ
  exact ⟨a,hlo,fun h => haB ((hd.mem_iff_contains had).mpr h)⟩

/-- Proposition 4.1: the exact maximum hole degree, actual Tor regularity, and
the least maximal-ideal power that becomes polymatroidal. -/
theorem minimal_local_obstruction {B : Family V} (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d)
    (hloc : ∀ U : Finset V, U ⊂ Finset.univ → IsPolymatroidal (localize B U))
    (hne : B ≠ lowerBaseFamily (lowerRank B) d) :
    ∃ t : ℕ, (∃ a ∈ holeSet B, a.degree = t) ∧
      (∀ b ∈ holeSet B, b.degree ≤ t) ∧ d ≤ t ∧
      IsTorRegularity (k := k) B (t+1) ∧
      IsLeast {q : ℕ | IsPolymatroidal (thickening B q)} (t+1-d) := by
  have hl := locallyEquigenerated_of_proper_polymatroidal hd hloc
  obtain ⟨a,ha,hmax,hda,hmul⟩ := exists_top_hole hB hd hloc (holeSet_nonempty_of_nonclosed hd hne)
  haveI : Nonempty V := by
    by_contra hn
    haveI : IsEmpty V := not_nonempty_iff.mp hn
    obtain ⟨b,hb⟩ := hB
    exact ha.2 ⟨b,hb,(Subsingleton.elim b a).le⟩
  exact ⟨a.degree,⟨a,ha,rfl⟩,hmax,hda,torRegularity_of_top_hole hB hl hd ha hmax hmul,
    least_polymatroidal_thickening hB hd.antichain hl hd ha hmax hda⟩

end Characterizations
