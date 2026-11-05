module
public import PaperVerification.ToricFanConstruction
@[expose] public section
/-!
# A finite smooth cone cover and all its faces

The generating cones need not be full dimensional. Each is assumed only to
have a genuine integral-basis ray set; coverage and the actual intersection
identity then propagate to all their subsets.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def finiteConeFamilyClosure {n : ℕ} (C : Finset (Finset (Lattice n))) :
    Finset (Finset (Lattice n)) := C.biUnion Finset.powerset

theorem mem_finiteConeFamilyClosure {n : ℕ} (C : Finset (Finset (Lattice n)))
    (s : Finset (Lattice n)) :
    s ∈ finiteConeFamilyClosure C ↔ ∃ u ∈ C, s ⊆ u := by
  simp [finiteConeFamilyClosure]

/-- Closing a finite smooth cone cover under ray subsets produces an actual
smooth complete fan if the original cone intersections are the common-ray
cones. None of these geometric properties is discarded in the closure. -/
def fanOfFiniteSmoothCones {n : ℕ} (C : Finset (Finset (Lattice n)))
    (hsmooth : ∀ s ∈ C, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      s ⊆ Finset.univ.image b)
    (hinter : ∀ s ∈ C, ∀ t ∈ C,
      latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t))
    (hcover : ∀ x : Ambient n, ∃ s ∈ C, x ∈ latticeRayCone s) :
    SmoothCompleteFan n where
  cones := finiteConeFamilyClosure C
  smooth := by
    intro s hs
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    obtain ⟨b, hb⟩ := hsmooth u hu
    exact ⟨b, basisRayIndices b s, (image_basisRayIndices b s (hsu.trans hb)).symm⟩
  downward := by
    intro s hs t hts
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    exact (mem_finiteConeFamilyClosure C t).mpr ⟨u, hu, hts.trans hsu⟩
  intersection := by
    intro s hs t ht
    obtain ⟨u, hu, hsu⟩ := (mem_finiteConeFamilyClosure C s).mp hs
    obtain ⟨v, hv, htv⟩ := (mem_finiteConeFamilyClosure C t).mp ht
    obtain ⟨bu, hbu⟩ := hsmooth u hu
    obtain ⟨bv, hbv⟩ := hsmooth v hv
    have hsets : (s ∩ (u ∩ v)) ∩ t = s ∩ t := by
      ext w
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hws, hwu, hwv⟩, hwt⟩
        exact ⟨hws, hwt⟩
      · rintro ⟨hws, hwt⟩
        exact ⟨⟨hws, hsu hws, htv hwt⟩, hwt⟩
    ext x
    constructor
    · rintro ⟨hxs, hxt⟩
      have hxuv : x ∈ latticeRayCone (u ∩ v) := by
        rw [← hinter u hu v hv]
        exact ⟨latticeRayCone_mono hsu hxs, latticeRayCone_mono htv hxt⟩
      have hxmid : x ∈ latticeRayCone (s ∩ (u ∩ v)) := by
        rw [← latticeRayCone_inter_of_subsets_basis bu s (u ∩ v)
          (hsu.trans hbu) (Finset.inter_subset_left.trans hbu)]
        exact ⟨hxs, hxuv⟩
      have hmidv : s ∩ (u ∩ v) ⊆ v :=
        Finset.inter_subset_right.trans Finset.inter_subset_right
      have hxfin : x ∈ latticeRayCone ((s ∩ (u ∩ v)) ∩ t) := by
        rw [← latticeRayCone_inter_of_subsets_basis bv (s ∩ (u ∩ v)) t
          (hmidv.trans hbv) (htv.trans hbv)]
        exact ⟨hxmid, hxt⟩
      simpa only [hsets] using hxfin
    · intro hx
      exact ⟨latticeRayCone_mono Finset.inter_subset_left hx,
        latticeRayCone_mono Finset.inter_subset_right hx⟩
  complete := by
    intro x
    obtain ⟨s, hs, hx⟩ := hcover x
    exact ⟨s, (mem_finiteConeFamilyClosure C s).mpr ⟨s, hs, Finset.Subset.refl _⟩, hx⟩

end PaperVerification.ToricGeometry
