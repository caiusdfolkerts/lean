module

public import PaperVerification.ToricBundleFanQuotient


@[expose] public section
/-!
# The fan of projected cones over a smooth cone

The only input to completeness in this construction is the literal covering
of quotient vectors by projected cones.  Smoothness, finiteness, intersections,
faces, purity, and uniqueness of ray lifts are proved from the original fan.
The empty-focus bundle case proves this covering in `ToricBundleFan`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem coneQuotient_injective_star_rays
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hIs : I.image b ⊆ s) (hIt : I.image b ⊆ t)
    {v w : Lattice n} (hv : v ∈ s \ I.image b) (hw : w ∈ t \ I.image b)
    (he : coneQuotientLattice b I v = coneQuotientLattice b I w) : v = w := by
  by_contra hvw
  let F := I.image b
  let S := insert v F
  let T := insert w F
  have hS : S ∈ «Σ».cones := «Σ».downward s hs S (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (Finset.mem_sdiff.mp hv).1
    · exact hIs ha)
  have hT : T ∈ «Σ».cones := «Σ».downward t ht T (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (Finset.mem_sdiff.mp hw).1
    · exact hIt ha)
  have hST : S ∩ T = F := by
    ext a
    constructor
    · intro ha
      obtain ⟨haS, haT⟩ := Finset.mem_inter.mp ha
      rcases Finset.mem_insert.mp haS with rfl | haF
      · rcases Finset.mem_insert.mp haT with heq | haF
        · exact (hvw heq).elim
        · exact haF
      · exact haF
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem ha⟩
  have hm : embed (n - I.card) (coneQuotientLattice b I v) ∈
      (latticeRayCone S).map (coneQuotientReal b I) ⊓
        (latticeRayCone T).map (coneQuotientReal b I) := by
    refine ⟨⟨embed n v, latticeRayCone_generator S (Finset.mem_insert_self v F),
      coneQuotient_compatible b I v⟩, ?_⟩
    refine ⟨embed n w, latticeRayCone_generator T (Finset.mem_insert_self w F), ?_⟩
    change coneQuotientReal b I (embed n w) =
      embed (n - I.card) (coneQuotientLattice b I v)
    rw [coneQuotient_compatible, he]
  rw [«Σ».coneQuotient_intersection b I hS hT
    (Finset.subset_insert v F) (Finset.subset_insert w F), hST] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  change coneQuotientReal b I x =
    embed (n - I.card) (coneQuotientLattice b I v) at hxe
  have hz : coneQuotientLattice b I v = 0 := by
    apply embed_injective (n - I.card)
    rw [← hxe, coneQuotient_zero_on_cone b I hx, map_zero]
  exact «Σ».coneQuotient_nonzero_ray b I hs hIs hv hz

/-- Literal finite family of all quotient cones over the deleted cone. -/
def quotientStarCones (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Finset (Finset (Lattice (n - I.card))) :=
  («Σ».cones.filter (fun s => I.image b ⊆ s)).image
    (fun s => (s \ I.image b).image (coneQuotientLattice b I))

theorem mem_quotientStarCones (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (t : Finset (Lattice (n - I.card))) :
    t ∈ «Σ».quotientStarCones b I ↔
      ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
        t = (s \ I.image b).image (coneQuotientLattice b I) := by
  simp only [quotientStarCones, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨s, ⟨hs, hIs⟩, he⟩
    exact ⟨s, hs, hIs, he.symm⟩
  · rintro ⟨s, hs, hIs, he⟩
    exact ⟨s, ⟨hs, hIs⟩, he.symm⟩

theorem quotientStarCones_downward (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {s t : Finset (Lattice (n - I.card))}
    (hs : s ∈ «Σ».quotientStarCones b I) (hts : t ⊆ s) :
    t ∈ «Σ».quotientStarCones b I := by
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  let D := S.filter (fun v => v ∉ I.image b ∧ coneQuotientLattice b I v ∈ t)
  have hD : I.image b ∪ D ⊆ S := Finset.union_subset hIS (Finset.filter_subset _ _)
  refine («Σ».mem_quotientStarCones b I t).mpr
    ⟨I.image b ∪ D, «Σ».downward S hS _ hD, Finset.subset_union_left, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hts hv)
    obtain ⟨hwS, hwI⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_image.mpr ⟨w,
      Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hwS, hwI, hv⟩), hwI⟩, rfl⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwU, hwI⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp hwU with hwF | hwD
    · exact (hwI hwF).elim
    · exact (Finset.mem_filter.mp hwD).2.2

theorem quotientStarCones_intersection (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {s t : Finset (Lattice (n - I.card))}
    (hs : s ∈ «Σ».quotientStarCones b I) (ht : t ∈ «Σ».quotientStarCones b I) :
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t) := by
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  obtain ⟨T, hT, hIT, rfl⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  apply le_antisymm
  · rw [latticeRayCone_quotient_sdiff, latticeRayCone_quotient_sdiff,
      «Σ».coneQuotient_intersection b I hS hT hIS hIT,
      ← latticeRayCone_quotient_sdiff]
    apply latticeRayCone_mono
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwST, hwI⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hwS, hwT⟩ := Finset.mem_inter.mp hwST
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwS, hwI⟩, rfl⟩,
        Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwT, hwI⟩, rfl⟩⟩
  · exact le_inf (latticeRayCone_mono Finset.inter_subset_left)
      (latticeRayCone_mono Finset.inter_subset_right)

/-- The actual smooth complete fan in the saturated quotient.  Its covering
input is an ordinary statement about real images of actual cones. -/
def quotientStarFan (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n))
    (hcover : ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I)) :
    SmoothCompleteFan (n - I.card) where
  cones := «Σ».quotientStarCones b I
  smooth := by
    intro s hs
    obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
    exact «Σ».coneQuotient_smooth b I hS hIS
  downward := by
    intro s hs t hts
    exact «Σ».quotientStarCones_downward b I hs hts
  intersection := by
    intro s hs t ht
    exact «Σ».quotientStarCones_intersection b I hs ht
  complete := by
    intro y
    obtain ⟨S, hS, hIS, hy⟩ := hcover y
    refine ⟨(S \ I.image b).image (coneQuotientLattice b I),
      («Σ».mem_quotientStarCones b I _).mpr ⟨S, hS, hIS, rfl⟩, ?_⟩
    rw [latticeRayCone_quotient_sdiff]
    exact hy

theorem quotientStarFan_isPure (hpure : «Σ».IsPure)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hcover : ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I)) :
    («Σ».quotientStarFan b I hcover).IsPure := by
  intro s hs
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  obtain ⟨T, hT, hST, hcard⟩ := hpure S hS
  have hIT : I.image b ⊆ T := hIS.trans hST
  refine ⟨(T \ I.image b).image (coneQuotientLattice b I),
    («Σ».mem_quotientStarCones b I _).mpr ⟨T, hT, hIT, rfl⟩, ?_, ?_⟩
  · exact Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) hST)
  · rw [Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hIT,
      Finset.card_image_of_injective I b.injective, hcard]
    intro v hv w hw he
    exact «Σ».coneQuotient_injective_star_rays b I hT hT hIT hIT hv hw he

end SmoothCompleteFan

end PaperVerification.ToricGeometry
