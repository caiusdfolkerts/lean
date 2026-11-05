module
public import PaperVerification.ToricStarDualBasis
public import PaperVerification.ToricStarConeCovering
@[expose] public section
/-!
# Actual intersections of the cones in a smooth star chart

The intersection of two newly subdivided cones is proved to be their
common-ray cone. The key equality is that both chosen pivot coordinates
must be minima, hence equal; the corresponding new coefficient vanishes.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section RaySets

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

/-- The actual inserted-sum ray set is exactly the indicated subset of the
unimodular replacement basis. -/
theorem starRaySet_basis (b : Module.Basis ι R E)
    (I J : Finset ι) (hJI : J ⊆ I) (j : ι) (hj : j ∈ J) :
    starRaySet (I.image b) (J.image b) (b j) = I.image (starRayBasis b J j) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    letI : Subsingleton E := Module.subsingleton R E
    ext x
    constructor
    · intro _
      exact Finset.mem_image.mpr ⟨j, hJI hj, Subsingleton.elim _ _⟩
    · intro _
      exact (mem_starRaySet _ _ _ _).mpr (Or.inl (Subsingleton.elim _ _))
  · letI := hR
    have hjI : j ∈ I := hJI hj
    have hsum : (∑ v ∈ J.image b, v) = ∑ i ∈ J, b i := by
      rw [Finset.sum_image]
      exact fun i _ k _ hik => b.injective hik
    have hrest : (I.erase j).image (starRayBasis b J j) = (I.erase j).image b := by
      apply Finset.image_congr
      intro i hi
      exact starRayBasis_other b J j i (Finset.mem_erase.mp hi).1
    calc
      starRaySet (I.image b) (J.image b) (b j) =
          insert (∑ i ∈ J, b i) ((I.erase j).image b) := by
        rw [starRaySet, hsum, ← Finset.image_erase b.injective]
      _ = insert (starRayBasis b J j j) ((I.erase j).image (starRayBasis b J j)) := by
        rw [starRayBasis_pivot b J j hj, hrest]
      _ = I.image (starRayBasis b J j) := by
        rw [← Finset.image_insert, Finset.insert_erase hjI]

end RaySets

section OneBasis

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] [DecidableEq ι]

/-- Two charts of a subdivision of one smooth cone meet in exactly the cone
on their common rays. This uses the actual sheared bases, not an asserted
fan-intersection property. -/
theorem starRayBasis_cone_inter (b : Module.Basis ι ℝ E)
    (I J : Finset ι) (hJI : J ⊆ I) (p q : ι) (hp : p ∈ J) (hq : q ∈ J) :
    finiteRayCone (I.image (starRayBasis b J p)) ⊓
        finiteRayCone (I.image (starRayBasis b J q)) =
      finiteRayCone ((I.image (starRayBasis b J p)) ∩
        (I.image (starRayBasis b J q))) := by
  by_cases hpq : p = q
  · subst q
    simp
  let bp := starRayBasis b J p
  let bq := starRayBasis b J q
  have hpI : p ∈ I := hJI hp
  have hqI : q ∈ I := hJI hq
  have hF : (I.erase q).image bp ⊆ (I.image bp) ∩ (I.image bq) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiI := Finset.mem_of_mem_erase hi
    have hiq := (Finset.mem_erase.mp hi).1
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, hiI, rfl⟩, ?_⟩
    by_cases hip : i = p
    · subst i
      refine Finset.mem_image.mpr ⟨q, hqI, ?_⟩
      exact (starRayBasis_pivot b J q hq).trans (starRayBasis_pivot b J p hp).symm
    · refine Finset.mem_image.mpr ⟨i, hiI, ?_⟩
      rw [starRayBasis_other b J q i hiq, starRayBasis_other b J p i hip]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxpos, hxzero⟩ :=
      (mem_finiteRayCone_basis_iff bp I x).mp hx.1
    obtain ⟨hypos, hyzero⟩ :=
      (mem_finiteRayCone_basis_iff bq I x).mp hx.2
    have hqp : q ∈ J.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
    have hpq' : p ∈ J.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
    have hxq : 0 ≤ b.coord q x - b.coord p x := by
      have h := hxpos q
      change 0 ≤ bp.coord q x at h
      simpa only [bp, starRayBasis_coord, if_pos hqp] using h
    have hyp : 0 ≤ b.coord p x - b.coord q x := by
      have h := hypos p
      change 0 ≤ bq.coord p x at h
      simpa only [bq, starRayBasis_coord, if_pos hpq'] using h
    have hzeroq : bp.repr x q = 0 := by
      change bp.coord q x = 0
      rw [starRayBasis_coord, if_pos hqp]
      linarith
    apply finiteRayCone_mono hF
    apply (mem_finiteRayCone_basis_iff bp (I.erase q) x).mpr
    refine ⟨hxpos, ?_⟩
    intro i hi
    by_cases hiq : i = q
    · simpa only [hiq] using hzeroq
    · exact hxzero i (fun hiI => hi (Finset.mem_erase.mpr ⟨hiq, hiI⟩))
  · exact le_inf
      (finiteRayCone_mono Finset.inter_subset_left)
      (finiteRayCone_mono Finset.inter_subset_right)

/-- If an old coordinate face omits a focus direction, its intersection
with a new cone has no exceptional-ray coefficient. -/
theorem starRayBasis_cone_inter_old_face (b : Module.Basis ι ℝ E)
    (I J K : Finset ι) (hJI : J ⊆ I) (hKI : K ⊆ I)
    (p : ι) (hp : p ∈ J) (hJK : ¬ J ⊆ K) :
    finiteRayCone (I.image (starRayBasis b J p)) ⊓ finiteRayCone (K.image b) =
      finiteRayCone (((I.image (starRayBasis b J p))) ∩ (K.image b)) := by
  let bp := starRayBasis b J p
  have hF : (K.erase p).image b ⊆ (I.image bp) ∩ (K.image b) := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiK := Finset.mem_of_mem_erase hi
    have hip := (Finset.mem_erase.mp hi).1
    refine Finset.mem_inter.mpr ⟨?_, Finset.mem_image.mpr ⟨i, hiK, rfl⟩⟩
    exact Finset.mem_image.mpr ⟨i, hKI hiK, starRayBasis_other b J p i hip⟩
  obtain ⟨q, hqJ, hqK⟩ := Finset.not_subset.mp hJK
  apply le_antisymm
  · intro x hx
    obtain ⟨hxpos, hxzero⟩ := (mem_finiteRayCone_basis_iff bp I x).mp hx.1
    obtain ⟨hypos, hyzero⟩ := (mem_finiteRayCone_basis_iff b K x).mp hx.2
    have hqzero : b.coord q x = 0 := hyzero q hqK
    have hpzero : b.coord p x = 0 := by
      by_cases hqp : q = p
      · simpa only [hqp] using hqzero
      · have hqerase : q ∈ J.erase p := Finset.mem_erase.mpr ⟨hqp, hqJ⟩
        have hqnonneg := hxpos q
        change 0 ≤ bp.coord q x at hqnonneg
        rw [starRayBasis_coord, if_pos hqerase, hqzero, zero_sub] at hqnonneg
        have hpnonneg := hypos p
        change 0 ≤ b.coord p x at hpnonneg
        linarith
    apply finiteRayCone_mono hF
    apply (mem_finiteRayCone_basis_iff b (K.erase p) x).mpr
    refine ⟨hypos, ?_⟩
    intro i hi
    by_cases hip : i = p
    · subst i
      change b.coord p x = 0
      exact hpzero
    · exact hyzero i (fun hiK => hi (Finset.mem_erase.mpr ⟨hip, hiK⟩))
  · exact le_inf
      (finiteRayCone_mono Finset.inter_subset_left)
      (finiteRayCone_mono Finset.inter_subset_right)

end OneBasis

end PaperVerification.ToricGeometry
