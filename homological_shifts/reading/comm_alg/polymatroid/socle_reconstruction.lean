import CommAlg.Polymatroid.TightSets
import Mathlib.Data.Finsupp.Interval

/-! # Actual monomial socles recover the exponent ideal

A monomial socle element is an exponent outside the ideal which enters the
ideal after multiplication by each retained variable. This is the literal
monomial condition, not a surrogate exchange or rigidity property.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Contains.mono {B : Family V} {a b : Exponent V}
    (ha : Contains B a) (hab : a ≤ b) : Contains B b := by
  obtain ⟨c, hc, hca⟩ := ha
  exact ⟨c, hc, hca.trans hab⟩

theorem project_add (U : Finset V) (a b : Exponent V) :
    project U (a + b) = project U a + project U b := by
  ext i
  by_cases hi : i ∈ U <;> simp [hi]

theorem project_single {U : Finset V} {i : V} (hi : i ∈ U) (k : ℕ) :
    project U (Finsupp.single i k) = Finsupp.single i k := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · simp [Finsupp.single_apply, hji, Ne.symm hji]

/-- A bounded corner outside a monomial ideal lies below an actual socle monomial. -/
theorem exists_socle_above (B : Family V) (U : Finset V) (a : Exponent V)
    (hsupp : project U a = a) (hout : ¬ Contains B a)
    (hkill : ∀ i ∈ U, ∃ k : ℕ, Contains B (a + Finsupp.single i k)) :
    ∃ b, a ≤ b ∧ project U b = b ∧ ¬ Contains B b ∧
      ∀ i ∈ U, Contains B (b + Finsupp.single i 1) := by
  choose k hk using hkill
  let bound : Exponent V := Finsupp.equivFunOnFinite.symm
    (fun i => if hi : i ∈ U then a i + k i hi else 0)
  let T : Set (Exponent V) := {b | a ≤ b ∧ project U b = b ∧ ¬ Contains B b}
  have hbounded : T ⊆ Set.Iic bound := by
    intro b hb i
    change b i ≤ (if hi : i ∈ U then a i + k i hi else 0)
    by_cases hi : i ∈ U
    · rw [dif_pos hi]
      by_contra h
      apply hb.2.2
      apply (hk i hi).mono
      intro j
      by_cases hji : j = i
      · subst j
        simpa using (show a i + k i hi ≤ b i by omega)
      · simpa [Finsupp.single_apply, hji, Ne.symm hji] using hb.1 j
    · rw [dif_neg hi]
      have he := congrArg (fun c : Exponent V => c i) hb.2.1
      simpa [hi] using he.symm.le
  have hfinite : T.Finite := (Set.finite_Iic bound).subset hbounded
  obtain ⟨b, hb, hmax⟩ := hfinite.exists_maximal ⟨a, le_rfl, hsupp, hout⟩
  refine ⟨b, hb.1, hb.2.1, hb.2.2, ?_⟩
  intro i hi
  by_contra hout'
  have hb' : b + Finsupp.single i 1 ∈ T := by
    refine ⟨hb.1.trans (le_add_right le_rfl), ?_, hout'⟩
    rw [project_add, hb.2.1, project_single hi]
  have hle := hmax hb' (le_add_right le_rfl)
  have h := hle i
  simp at h

def LocalSocleDegrees (B : Family V) : Prop :=
  ∀ (U : Finset V) (a : Exponent V), project U a = a →
    ¬ Contains (localize B U) a →
    (∀ i ∈ U, Contains (localize B U) (a + Finsupp.single i 1)) →
    a.degree + 1 = lowerRank B U

theorem contains_project_empty {B : Family V} (hB : B.Nonempty) (a : Exponent V) :
    Contains (localize B ∅) (project ∅ a) := by
  rw [contains_localize]
  obtain ⟨b, hb⟩ := hB
  exact ⟨b, hb, by simp⟩

theorem contains_localize_univ (B : Family V) (a : Exponent V) :
    Contains (localize B Finset.univ) (project Finset.univ a) ↔ Contains B a := by
  rw [contains_localize]
  simp only [project_univ, Contains]

/-- Every missing monomial has a localization where it lies below a socle monomial. -/
theorem missing_local_socle {B : Family V} (hB : B.Nonempty) {a : Exponent V}
    (ha : ¬ Contains B a) :
    ∃ U : Finset V, U.Nonempty ∧ ∃ b : Exponent V,
      project U a ≤ b ∧ project U b = b ∧ ¬ Contains (localize B U) b ∧
        ∀ i ∈ U, Contains (localize B U) (b + Finsupp.single i 1) := by
  let bad : Finset (Finset V) := Finset.univ.filter
    (fun U => ¬ Contains (localize B U) (project U a))
  have hbad : bad.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rwa [contains_localize_univ]
  obtain ⟨U, hU, hmin⟩ := bad.exists_minimal hbad
  have hout : ¬ Contains (localize B U) (project U a) := (Finset.mem_filter.mp hU).2
  have hUne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst U
    exact hout (contains_project_empty hB a)
  have hgood : ∀ i ∈ U, Contains (localize B (U.erase i)) (project (U.erase i) a) := by
    intro i hi
    by_contra h
    have hmem : U.erase i ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hsub := hmin hmem (Finset.erase_subset i U)
    exact Finset.notMem_erase i U (hsub hi)
  have hkill : ∀ i ∈ U, ∃ k : ℕ,
      Contains (localize B U) (project U a + Finsupp.single i k) := by
    intro i hi
    obtain ⟨b, hb, hba⟩ := (contains_localize B (U.erase i) _).mp (hgood i hi)
    refine ⟨b i, (contains_localize B U _).mpr ⟨b, hb, ?_⟩⟩
    intro j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · by_cases hjU : j ∈ U
      · have h := hba j
        have hjerase : j ∈ U.erase i := Finset.mem_erase.mpr ⟨hji, hjU⟩
        simpa [hjerase, hjU, Finsupp.single_apply, hji, Ne.symm hji] using h
      · simp [hjU, Finsupp.single_apply, hji, Ne.symm hji]
  obtain ⟨b, hab, hbsupp, hbout, hbsoc⟩ := exists_socle_above (localize B U) U
    (project U a) (project_project le_rfl a) hout hkill
  exact ⟨U, hUne, b, hab, hbsupp, hbout, hbsoc⟩

/-- Lemma 2.5: all local monomial socle degrees recover every monomial of the ideal. -/
theorem contains_iff_lowerFeasible {B : Family V} (hB : B.Nonempty)
    (hsoc : LocalSocleDegrees B) (a : Exponent V) :
    Contains B a ↔ LowerFeasible (lowerRank B) a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    exact (lowerRank_le hb U).trans (Finset.sum_le_sum (fun i _ => hba i))
  · intro hfeas
    by_contra hout
    obtain ⟨U, _, b, hab, hbsupp, hbout, hbsoc⟩ := missing_local_socle hB hout
    have hdegree := hsoc U b hbsupp hbout hbsoc
    have hle := degree_mono hab
    rw [degree_project] at hle
    have hr := hfeas U
    omega

/-- The complete converse in the local-socle characterization, before invoking
any homological source for its literal monomial socle hypothesis. -/
theorem polymatroidal_of_local_socles {B : Family V} (hB : B.Nonempty)
    (ha : Antichain B) (hl : LocallyEquigenerated B) (hsoc : LocalSocleDegrees B) :
    IsPolymatroidal B := by
  obtain ⟨d, hd⟩ := hl Finset.univ
  have he : localize B Finset.univ = B := by
    have hp : project (Finset.univ : Finset V) = id := funext project_univ
    simpa [localize, hp] using minimalFamily_eq ha
  rw [he] at hd
  exact polymatroidal_of_lower_inequalities hd (lowerRank_supermodular hB hl)
    (contains_iff_lowerFeasible hB hsoc)

end CommAlg.Polymatroid
