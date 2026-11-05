module
public import PaperVerification.ToricStarConeIntersections
public import PaperVerification.ToricFanConstruction
@[expose] public section
/-!
# Restriction of star cones to old fan faces

All ray sets are finite subsets of the actual integer lattice. The exceptional
ray is their sum, and its incidence with an old face is proved from the fan's
actual geometric intersection property.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem image_embed_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) :
    (I.image b).image (embed n) = I.image (integralBasisReal b) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i hi
  exact (integralBasisReal_apply b i).symm

/-- The generic basis identity with finite images in the literal lattice. -/
theorem lattice_starRaySet_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hJI : J ⊆ I) (j : Fin n) (hj : j ∈ J) :
    starRaySet (I.image b) (J.image b) (b j) = I.image (starRayBasis b J j) := by
  have hImage (f : Fin n → Lattice n) (K : Finset (Fin n)) :
      @Finset.image (Fin n) (Lattice n)
        (fun a b => Classical.propDecidable (a = b)) f K = K.image f := by
    ext x
    simp only [Finset.mem_image]
  have h := starRaySet_basis b I J hJI j hj
  rw [hImage b I, hImage b J, hImage (starRayBasis b J j) I] at h
  exact h

theorem embed_starRaySet {n : ℕ} (s t : Finset (Lattice n)) (v : Lattice n) :
    (starRaySet s t v).image (embed n) =
      starRaySet (s.image (embed n)) (t.image (embed n)) (embed n v) := by
  have hsum : embed n (∑ w ∈ t, w) = ∑ w ∈ t.image (embed n), w := by
    rw [map_sum, Finset.sum_image]
    exact fun a _ b _ hab => embed_injective n hab
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_starRaySet _ _ _ _).mpr
    rcases (mem_starRaySet _ _ _ _).mp hz with hsumz | ⟨hzv, hzs⟩
    · exact Or.inl (congrArg (embed n) hsumz |>.trans hsum)
    · exact Or.inr ⟨fun h => hzv (embed_injective n h),
        Finset.mem_image.mpr ⟨z, hzs, rfl⟩⟩
  · intro hx
    rcases (mem_starRaySet _ _ _ _).mp hx with hxsum | ⟨hxv, hxs⟩
    · refine Finset.mem_image.mpr ⟨∑ w ∈ t, w,
        (mem_starRaySet _ _ _ _).mpr (Or.inl rfl), ?_⟩
      exact hsum.trans hxsum.symm
    · obtain ⟨z, hzs, rfl⟩ := Finset.mem_image.mp hxs
      exact Finset.mem_image.mpr ⟨z,
        (mem_starRaySet _ _ _ _).mpr (Or.inr
          ⟨fun h => hxv (congrArg (embed n) h), hzs⟩), rfl⟩

theorem latticeRayCone_starRaySet_le {n : ℕ} {s t : Finset (Lattice n)}
    (hts : t ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ≤ latticeRayCone s := by
  unfold latticeRayCone
  rw [embed_starRaySet]
  exact finiteRayCone_starRaySet_le (Finset.image_subset_image hts) (embed n v)

theorem latticeRayCone_star_cover {n : ℕ} {s t : Finset (Lattice n)}
    (hts : t ⊆ s) (ht : t.Nonempty) {x : Ambient n} (hx : x ∈ latticeRayCone s) :
    ∃ v ∈ t, x ∈ latticeRayCone (starRaySet s t v) := by
  obtain ⟨v, hv, hxv⟩ := finiteRayCone_star_cover
    (Finset.image_subset_image hts) (ht.image (embed n)) hx
  obtain ⟨vZ, hvZ, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨vZ, hvZ, ?_⟩
  unfold latticeRayCone
  rw [embed_starRaySet]
  exact hxv

theorem latticeRayCone_inf_face {n : ℕ} (C F : PointedCone ℝ (Ambient n))
    (hF : F.IsFaceOf C) (s : Finset (Lattice n))
    (hs : ∀ v ∈ s, embed n v ∈ C) :
    latticeRayCone s ⊓ F = latticeRayCone (s.filter (fun v => embed n v ∈ F)) := by
  unfold latticeRayCone
  rw [finiteRayCone_inf_face C F hF _ (by
    rintro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact hs v hv)]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hxF⟩ := Finset.mem_filter.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hxF⟩, rfl⟩
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hv, hvF⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, hvF⟩

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- An actual subcone is a subset of the same integral basis as its parent. -/
theorem adapted_basis_for_subcone {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I J : Finset (Fin n)),
      s = I.image b ∧ t = J.image b ∧ J ⊆ I := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  let J := I.filter (fun i => b i ∈ t)
  refine ⟨b, I, J, rfl, ?_, Finset.filter_subset _ _⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2

/-- Every new ray set is literally part of a genuine integral basis. -/
theorem starRaySet_smooth {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (hts : t ⊆ s) {v : Lattice n} (hv : v ∈ t) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      starRaySet s t v = I.image b := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  rw [htJ] at hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨starRayBasis b J j, I, ?_⟩
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI j hj]

/-- The local star-chart intersection theorem transferred to actual integer
ray sets, with an integral basis adapted to the original cone. -/
theorem star_cones_same_parent_inter {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) {v w : Lattice n}
    (hv : v ∈ t) (hw : w ∈ t) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet s t w) =
      latticeRayCone (starRaySet s t v ∩ starRaySet s t w) := by
  obtain ⟨b, I, J, hsI, htJ, hJI⟩ := «Σ».adapted_basis_for_subcone hs hts
  rw [htJ] at hv hw
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hw
  rw [hsI, htJ, lattice_starRaySet_basis b I J hJI p hp,
    lattice_starRaySet_basis b I J hJI q hq]
  unfold latticeRayCone
  rw [Finset.image_inter _ _ (embed_injective n)]
  simp only [image_embed_basis, integralBasisReal_starRayBasis]
  have hImage (f : Fin n → Ambient n) (K : Finset (Fin n)) :
      @Finset.image (Fin n) (Ambient n)
        (fun a b => Classical.propDecidable (a = b)) f K = K.image f := by
    ext x
    simp only [Finset.mem_image]
  have hInter (S T : Finset (Ambient n)) :
      @Inter.inter (Finset (Ambient n))
        (@Finset.instInter (Ambient n) (fun a b => Classical.propDecidable (a = b))) S T =
          S ∩ T := by
    ext x
    simp only [Finset.mem_inter]
  have h := starRayBasis_cone_inter (integralBasisReal b) I J hJI p q hp hq
  rw [hImage (starRayBasis (integralBasisReal b) J p) I,
    hImage (starRayBasis (integralBasisReal b) J q) I, hInter] at h
  exact h

/-- The sum of all focus rays lies in an old cone exactly when that cone
contains every focus ray. -/
theorem sum_rays_mem_cone_iff {t u : Finset (Lattice n)}
    (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones) :
    embed n (∑ v ∈ t, v) ∈ latticeRayCone u ↔ t ⊆ u := by
  rw [map_sum]
  constructor
  · exact «Σ».sum_mem_cone_implies_subset ht hu
  · intro htu
    exact Submodule.sum_mem _ (fun v hv => latticeRayCone_generator u (htu hv))

/-- A focus of dimension at least two produces a new ray, distinct from
every original ray of the complete smooth fan. -/
theorem sum_rays_not_mem_rays {t : Finset (Lattice n)}
    (ht : t ∈ «Σ».cones) (hcard : 2 ≤ t.card) : (∑ v ∈ t, v) ∉ «Σ».rays := by
  intro hmem
  have hsingle := «Σ».singleton_mem_of_mem_rays hmem
  have hsub : t ⊆ {∑ v ∈ t, v} := («Σ».sum_rays_mem_cone_iff ht hsingle).mp
    (latticeRayCone_generator _ (Finset.mem_singleton_self _))
  have h := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at h
  omega

/-- Filtering one new ray set by incidence with an old face is explicit:
the exceptional ray survives precisely when the entire focus does. -/
theorem filter_starRaySet_by_face {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hus : u ⊆ s) (v : Lattice n) :
    (starRaySet s t v).filter (fun w => embed n w ∈ latticeRayCone u) =
      if t ⊆ u then starRaySet u t v else u.erase v := by
  ext w
  have hcone (hws : w ∈ s) : embed n w ∈ latticeRayCone u ↔ w ∈ u := by
    exact «Σ».ray_mem_cone_iff hu ((«Σ».mem_rays_iff w).mpr ⟨s, hs, hws⟩)
  by_cases htu : t ⊆ u
  · simp only [Finset.mem_filter, mem_starRaySet, if_pos htu]
    constructor
    · rintro ⟨hstar, hwcone⟩
      rcases hstar with hsum | ⟨hwv, hws⟩
      · exact Or.inl hsum
      · exact Or.inr ⟨hwv, (hcone hws).mp hwcone⟩
    · intro hstar
      rcases hstar with hsum | ⟨hwv, hwu⟩
      · refine ⟨Or.inl hsum, ?_⟩
        rw [hsum]
        exact («Σ».sum_rays_mem_cone_iff ht hu).mpr htu
      · exact ⟨Or.inr ⟨hwv, hus hwu⟩, latticeRayCone_generator u hwu⟩
  · simp only [Finset.mem_filter, mem_starRaySet, if_neg htu, Finset.mem_erase]
    constructor
    · rintro ⟨hstar, hwcone⟩
      rcases hstar with hsum | ⟨hwv, hws⟩
      · rw [hsum] at hwcone
        exact False.elim (htu ((«Σ».sum_rays_mem_cone_iff ht hu).mp hwcone))
      · exact ⟨hwv, (hcone hws).mp hwcone⟩
    · rintro ⟨hwv, hwu⟩
      exact ⟨Or.inr ⟨hwv, hus hwu⟩, latticeRayCone_generator u hwu⟩

/-- Restriction of a new cone to an actual old face is either the
corresponding star cone in that face or its unchanged old rays. -/
theorem star_cone_inter_face {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (hus : u ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      if t ⊆ u then latticeRayCone (starRaySet u t v) else latticeRayCone (u.erase v) := by
  rw [latticeRayCone_inf_face (latticeRayCone s) (latticeRayCone u)
    («Σ».cone_subset_isFaceOf hs hus) _ (by
      intro w hw
      exact latticeRayCone_starRaySet_le hts v (latticeRayCone_generator _ hw)),
    «Σ».filter_starRaySet_by_face hs ht hu hus v]
  split_ifs <;> rfl

/-- The same restriction formula against any old fan cone, using the
actual common face of its old parent. -/
theorem star_cone_inter_old_cone {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      if t ⊆ s ∩ u then latticeRayCone (starRaySet (s ∩ u) t v)
      else latticeRayCone ((s ∩ u).erase v) := by
  have hle := latticeRayCone_starRaySet_le hts v
  have heq : latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (s ∩ u) := by
    rw [← «Σ».intersection s hs u hu]
    ext x
    exact ⟨fun h => ⟨h.1, hle h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [heq]
  exact «Σ».star_cone_inter_face hs ht
    («Σ».downward s hs _ Finset.inter_subset_left) hts Finset.inter_subset_left v

/-- A new cone and an unchanged old cone have precisely their common-ray
intersection. The focus is not contained in an unchanged old cone. -/
theorem star_cone_inter_unchanged {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (htu : ¬ t ⊆ u) (v : Lattice n) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone u =
      latticeRayCone (starRaySet s t v ∩ u) := by
  have hnot : ¬ t ⊆ s ∩ u := fun h => htu (h.trans Finset.inter_subset_right)
  rw [«Σ».star_cone_inter_old_cone hs ht hu hts v, if_neg hnot]
  have he : (∑ w ∈ t, w) ∉ u := by
    intro heu
    exact htu ((«Σ».sum_rays_mem_cone_iff ht hu).mp (latticeRayCone_generator u heu))
  congr 1
  ext z
  by_cases hze : z = ∑ w ∈ t, w
  · subst z
    simp [starRaySet, he]
  · simp [starRaySet, hze, Finset.mem_inter, Finset.mem_erase,
      and_assoc, and_left_comm, and_comm]

/-- New cones over any two old cones meet in their exact common-ray cone.
Restriction to the old common face reduces this to the same-parent theorem. -/
theorem star_cones_inter {s t u : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (hu : u ∈ «Σ».cones)
    (hts : t ⊆ s) (htu : t ⊆ u) {v w : Lattice n}
    (hv : v ∈ t) (hw : w ∈ t) :
    latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet u t w) =
      latticeRayCone (starRaySet s t v ∩ starRaySet u t w) := by
  let F := s ∩ u
  have hF : F ∈ «Σ».cones := «Σ».downward s hs F Finset.inter_subset_left
  have htF : t ⊆ F := Finset.subset_inter hts htu
  have hleft := «Σ».star_cone_inter_face hs ht hF hts Finset.inter_subset_left v
  have hright := «Σ».star_cone_inter_face hu ht hF htu Finset.inter_subset_right w
  rw [if_pos htF] at hleft hright
  have hmeet : latticeRayCone (starRaySet s t v) ⊓ latticeRayCone (starRaySet u t w) =
      (latticeRayCone (starRaySet s t v) ⊓ latticeRayCone F) ⊓
      (latticeRayCone (starRaySet u t w) ⊓ latticeRayCone F) := by
    ext x
    constructor
    · intro hx
      have hxF : x ∈ latticeRayCone F := by
        rw [← «Σ».intersection s hs u hu]
        exact ⟨latticeRayCone_starRaySet_le hts v hx.1,
          latticeRayCone_starRaySet_le htu w hx.2⟩
      exact ⟨⟨hx.1, hxF⟩, ⟨hx.2, hxF⟩⟩
    · exact fun hx => ⟨hx.1.1, hx.2.1⟩
  rw [hmeet, hleft, hright, «Σ».star_cones_same_parent_inter hF htF hv hw]
  congr 1
  ext z
  by_cases hze : z = ∑ y ∈ t, y
  · subst z
    simp [starRaySet]
  · simp [starRaySet, hze, F, Finset.mem_inter, Finset.mem_erase,
      and_assoc, and_left_comm, and_comm]

end SmoothCompleteFan

end PaperVerification.ToricGeometry
