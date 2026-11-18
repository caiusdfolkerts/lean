module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part08
public import Unimodular.FanBridge

/-!
# Identifying the two fan interfaces

The finite ray-set fan used by the scheme construction gives an ordinary
TauCeti fan with exactly the same geometric cones and primitive lattice
rays.  Completeness and regularity are proved from its defining axioms.
Thus the paper's coordinate and matroid results can be applied to the
same fans as the global-section and sheaf constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace Unimodular.FanInterfaces

open Set TauCeti.Toric
open PaperVerification.ToricGeometry

variable {n : ℕ}

lemma dictionaryEmbedding_eq :
    PaperVerification.ToricGeometry.embed n = Unimodular.FanBridge.standardEmbedding n := rfl

lemma latticeRayCone_eq_hull_image (s : Finset (Lattice n)) :
    latticeRayCone s = PointedCone.hull ℝ (PaperVerification.ToricGeometry.embed n '' (s : Set (Lattice n))) := by
  rw [latticeRayCone, finiteRayCone_eq_hull]
  simp only [Finset.coe_image]

lemma latticeRayCone_full_basis (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    latticeRayCone (Finset.univ.image b) =
      Unimodular.ConeBases.cone (ι := Unimodular.FanBridge.standardEmbedding n) b := by
  rw [latticeRayCone_eq_hull_image]
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
    ← Set.range_comp, Unimodular.ConeBases.cone, dictionaryEmbedding_eq]
  rfl

variable (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)

lemma dictionaryCone_isRegular {s : Finset (Lattice n)} (hs : s ∈ F.cones) :
    IsRegularCone (Unimodular.FanBridge.standardEmbedding n) (latticeRayCone s) := by
  obtain ⟨b, I, rfl⟩ := F.smooth s hs
  rw [latticeRayCone_eq_hull_image]
  simp only [Finset.coe_image, Set.image_image, dictionaryEmbedding_eq]
  simpa only [Set.image_image] using isRegularCone_hull_image_basis
    (Unimodular.FanBridge.standardEmbedding_isIntegralLattice n) b (I : Set (Fin n))

lemma face_eq_filtered_rays {s : Finset (Lattice n)}
    {C : PointedCone ℝ (Ambient n)} (hC : C.IsFaceOf (latticeRayCone s)) :
    C = latticeRayCone (s.filter (fun u => PaperVerification.ToricGeometry.embed n u ∈ C)) := by
  classical
  have h := PointedCone.Face.eq_hull_inter_of_eq_hull ⟨C, hC⟩
    (PaperVerification.ToricGeometry.embed n '' (s : Set (Lattice n))) (latticeRayCone_eq_hull_image s)
  change C = PointedCone.hull ℝ
    ((PaperVerification.ToricGeometry.embed n '' (s : Set (Lattice n))) ∩ (C : Set (Ambient n))) at h
  calc
    C = PointedCone.hull ℝ
        ((PaperVerification.ToricGeometry.embed n '' (s : Set (Lattice n))) ∩
          (C : Set (Ambient n))) := h
    _ = latticeRayCone (s.filter (fun u => PaperVerification.ToricGeometry.embed n u ∈ C)) := by
      rw [latticeRayCone_eq_hull_image]
      congr 1
      ext x
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hx⟩
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, hx⟩, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, (Finset.mem_filter.mp hu).1, rfl⟩, (Finset.mem_filter.mp hu).2⟩

/-- The ordinary fan with exactly the original geometric cones. -/
def dictionaryToricFan : Fan (Unimodular.FanBridge.standardEmbedding n) where
  lattice := Unimodular.FanBridge.standardEmbedding_isIntegralLattice n
  cones := latticeRayCone '' (F.cones : Set (Finset (Lattice n)))
  finite_cones := F.cones.finite_toSet.image _
  isToricCone := by
    rintro C ⟨s, hs, rfl⟩
    exact (dictionaryCone_isRegular F hs).toIsToricCone
  mem_of_isFaceOf := by
    rintro C D ⟨s, hs, rfl⟩ hD
    classical
    exact ⟨s.filter (fun u => PaperVerification.ToricGeometry.embed n u ∈ D),
      F.downward s hs _ (Finset.filter_subset _ _), (face_eq_filtered_rays hD).symm⟩
  inf_isFaceOf_left := by
    rintro C D ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rw [F.intersection s hs t ht]
    exact F.cone_subset_isFaceOf hs Finset.inter_subset_left

@[simp] theorem dictionaryToricFan_cones :
    (dictionaryToricFan F).cones = latticeRayCone '' (F.cones : Set (Finset (Lattice n))) := rfl

theorem dictionaryToricFan_complete : (dictionaryToricFan F).IsComplete := by
  apply (Fan.isComplete_iff _).mpr
  intro x
  obtain ⟨s, hs, hx⟩ := F.complete x
  exact ⟨latticeRayCone s, ⟨s, hs, rfl⟩, hx⟩

theorem dictionaryToricFan_regular : (dictionaryToricFan F).IsRegular := by
  apply Fan.isRegular_iff.mpr
  rintro C ⟨s, hs, rfl⟩
  exact dictionaryCone_isRegular F hs

/-- No ray is added, lost, rescaled, or identified with its negative. -/
theorem dictionaryToricFan_ray_iff (u : Lattice n) :
    Unimodular.ConeBases.IsRay (dictionaryToricFan F) u ↔ u ∈ F.rays := by
  constructor
  · rintro ⟨C, ⟨s, hs, rfl⟩, ρ, hu⟩
    obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
    obtain ⟨b, hb⟩ := F.full_cone_basis ht hcard
    have hcone : latticeRayCone t =
        Unimodular.ConeBases.cone (ι := Unimodular.FanBridge.standardEmbedding n) b := by
      rw [hb, latticeRayCone_full_basis]
    have hu' := (isPrimitiveGenerator_faceEmbedding (F.cone_subset_isFaceOf ht hst) ρ).mpr hu
    obtain ⟨i, rfl⟩ := Unimodular.ConeBases.primitive_generator_eq_basis_of_eq
      (dictionaryToricFan F).lattice b hcone _ hu'
    apply F.ray_mem_of_mem_cone ht
    rw [hb]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro hu
    obtain ⟨s, hs, hus⟩ := (F.mem_rays_iff u).mp hu
    obtain ⟨t, ht, hst, hcard⟩ := F.isPure s hs
    obtain ⟨b, hb⟩ := F.full_cone_basis ht hcard
    have hut : u ∈ Finset.univ.image b := hb ▸ hst hus
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hut
    apply Unimodular.ConeBases.isRay_basis (dictionaryToricFan F) b
    exact ⟨t, ht, by rw [hb, latticeRayCone_full_basis]⟩

/-- The older coordinate presentation exists for exactly these cones and
primitive rays; its basis criterion is the ordinary fan basis criterion. -/
theorem exists_coordinatePresentation :
    ∃ G : Unimodular.SmoothCompleteFan n,
      (∀ u, u ∈ G.rays ↔ u ∈ F.rays) ∧
      (Unimodular.ConeBases.PositiveCriterion (dictionaryToricFan F) ↔
        G.PositiveCoordinateCriterion) := by
  obtain ⟨G, hG, hcrit⟩ := Unimodular.FanBridge.exists_smoothCompleteFan
    (dictionaryToricFan F) (dictionaryToricFan_complete F) (dictionaryToricFan_regular F)
  exact ⟨G, fun u => (hG u).trans (dictionaryToricFan_ray_iff F u), hcrit⟩

/-- The intrinsic criterion over every cone basis is precisely the
coordinate criterion used by the divisor construction. -/
theorem dictionaryPositiveCriterion_iff :
    Unimodular.ConeBases.PositiveCriterion (dictionaryToricFan F) ↔
      ∀ s : F.fullCones, ∀ u ∈ F.rays,
        (∑ i, max ((F.fullConeBasis s).repr u i) 0) ≤ 1 := by
  constructor
  · intro h s u hu
    apply h n (F.fullConeBasis s)
    · refine ⟨s.val, F.fullCones_mem s, ?_⟩
      rw [F.fullConeBasis_ray_set, latticeRayCone_full_basis]
    · exact (dictionaryToricFan_ray_iff F u).mpr hu
  · intro h m b hb u hu
    obtain ⟨s, hs, hsb⟩ := hb
    have hsfull : s.card = n := F.card_eq_of_full_span hs (by
      rw [hsb]
      exact Unimodular.ConeBases.span_cone (dictionaryToricFan F).lattice b)
    let s' : F.fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hsfull⟩⟩
    have hb' : Unimodular.ConeBases.cone
        (ι := Unimodular.FanBridge.standardEmbedding n) b =
        Unimodular.ConeBases.cone
          (ι := Unimodular.FanBridge.standardEmbedding n) (F.fullConeBasis s') := by
      rw [← hsb, ← latticeRayCone_full_basis, ← F.fullConeBasis_ray_set]
    rw [Unimodular.ConeBases.positive_sum_eq_of_cone_eq
      (dictionaryToricFan F).lattice b (F.fullConeBasis s') hb' u]
    exact h s' u ((dictionaryToricFan_ray_iff F u).mp hu)

#print axioms dictionaryToricFan
#print axioms dictionaryToricFan_ray_iff
#print axioms dictionaryPositiveCriterion_iff

end Unimodular.FanInterfaces
