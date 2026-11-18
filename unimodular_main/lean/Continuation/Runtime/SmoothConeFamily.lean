module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part12

/-!
# A complete fan from smooth affine cones of arbitrary dimension

A finite invariant affine cover may contain charts with torus factors.
Its cones are therefore allowed to have any dimension. The construction
below closes an arbitrary smooth cone family under faces; it uses the
actual common-ray intersection and covering equalities.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PaperVerification.ToricGeometry

open scoped Classical

variable {n : ℕ} {J : Type*} [Fintype J]

/-- Every face of every cone in the given finite family. -/
def smoothConeFamilyFaces (s : J → Finset (Lattice n)) : Finset (Finset (Lattice n)) :=
  Finset.univ.biUnion (fun j => (s j).powerset)

theorem mem_smoothConeFamilyFaces (s : J → Finset (Lattice n)) (t : Finset (Lattice n)) :
    t ∈ smoothConeFamilyFaces s ↔ ∃ j, t ⊆ s j := by
  simp [smoothConeFamilyFaces]

/-- The face closure of a covering family of smooth cones is a complete
smooth fan, with no maximal-dimensionality assumption on the family. -/
def fanOfSmoothConeFamily (s : J → Finset (Lattice n))
    (hsmooth : ∀ j, ∃ (b : Module.Basis (Fin n) ℤ (Lattice n))
      (I : Finset (Fin n)), s j = I.image b)
    (hinter : ∀ i j, latticeRayCone (s i) ⊓ latticeRayCone (s j) =
      latticeRayCone (s i ∩ s j))
    (hcover : ∀ x : Ambient n, ∃ j, x ∈ latticeRayCone (s j)) :
    SmoothCompleteFan n where
  cones := smoothConeFamilyFaces s
  smooth := by
    intro t ht
    obtain ⟨j, hj⟩ := (mem_smoothConeFamilyFaces s t).mp ht
    obtain ⟨b, I, hI⟩ := hsmooth j
    have hj' : t ⊆ Finset.univ.image b := hj.trans (by
      rw [hI]
      exact Finset.image_subset_image (Finset.subset_univ I))
    exact ⟨b, basisRayIndices b t, (image_basisRayIndices b t hj').symm⟩
  downward := by
    intro t ht q hqt
    obtain ⟨j, hj⟩ := (mem_smoothConeFamilyFaces s t).mp ht
    exact (mem_smoothConeFamilyFaces s q).mpr ⟨j, hqt.trans hj⟩
  intersection := by
    intro t ht q hq
    obtain ⟨i, hti⟩ := (mem_smoothConeFamilyFaces s t).mp ht
    obtain ⟨j, hqj⟩ := (mem_smoothConeFamilyFaces s q).mp hq
    obtain ⟨bi, Ii, hi⟩ := hsmooth i
    obtain ⟨bj, Ij, hj⟩ := hsmooth j
    have hifull : s i ⊆ Finset.univ.image bi := by
      rw [hi]
      exact Finset.image_subset_image (Finset.subset_univ Ii)
    have hjfull : s j ⊆ Finset.univ.image bj := by
      rw [hj]
      exact Finset.image_subset_image (Finset.subset_univ Ij)
    have hsets : (t ∩ (s i ∩ s j)) ∩ q = t ∩ q := by
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hvt, _⟩, hvq⟩
        exact ⟨hvt, hvq⟩
      · rintro ⟨hvt, hvq⟩
        exact ⟨⟨hvt, hti hvt, hqj hvq⟩, hvq⟩
    ext x
    constructor
    · rintro ⟨hxt, hxq⟩
      have hxij : x ∈ latticeRayCone (s i ∩ s j) := by
        rw [← hinter i j]
        exact ⟨latticeRayCone_mono hti hxt, latticeRayCone_mono hqj hxq⟩
      have hxmid : x ∈ latticeRayCone (t ∩ (s i ∩ s j)) := by
        rw [← latticeRayCone_inter_of_subsets_basis bi t (s i ∩ s j)
          (hti.trans hifull) (Finset.inter_subset_left.trans hifull)]
        exact ⟨hxt, hxij⟩
      have hmid : t ∩ (s i ∩ s j) ⊆ Finset.univ.image bj :=
        (Finset.inter_subset_right.trans Finset.inter_subset_right).trans hjfull
      have hxfin : x ∈ latticeRayCone ((t ∩ (s i ∩ s j)) ∩ q) := by
        rw [← latticeRayCone_inter_of_subsets_basis bj (t ∩ (s i ∩ s j)) q
          hmid (hqj.trans hjfull)]
        exact ⟨hxmid, hxq⟩
      simpa only [hsets] using hxfin
    · intro hx
      exact ⟨latticeRayCone_mono Finset.inter_subset_left hx,
        latticeRayCone_mono Finset.inter_subset_right hx⟩
  complete := by
    intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨s j, (mem_smoothConeFamilyFaces s _).mpr ⟨j, Finset.Subset.refl _⟩, hj⟩

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.fanOfSmoothConeFamily
