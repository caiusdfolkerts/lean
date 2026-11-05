module

public import PaperVerification.ToricCartierCharacterModules

@[expose] public section

/-! # Recovering integral support coefficients from compatible chart characters -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open scoped Classical BigOperators

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure)

include hpure in
theorem exists_fullCone_of_ray (u : «Σ».rays) :
    ∃ s : «Σ».fullCones,u.val∈s.val := by
  obtain ⟨t,ht,hut⟩ := («Σ».mem_rays_iff u.val).mp u.property
  obtain ⟨s,hs,hts,hcard⟩ := hpure t ht
  exact ⟨⟨s,Finset.mem_filter.mpr ⟨hs,hcard⟩⟩,hts hut⟩

def rayFullCone (u : «Σ».rays) : «Σ».fullCones :=
  («Σ».exists_fullCone_of_ray hpure u).choose

theorem mem_rayFullCone (u : «Σ».rays) : u.val∈(«Σ».rayFullCone hpure u).val :=
  («Σ».exists_fullCone_of_ray hpure u).choose_spec

/-- Only actual rays carry coefficients; the extension away from the
finite ray set is fixed to zero and has no geometric effect. -/
def coefficientsOfCharacters (m : «Σ».fullCones→Lattice n) (u : Lattice n) : ℤ :=
  if hu : u∈«Σ».rays then -integerPairing u (m («Σ».rayFullCone hpure ⟨u,hu⟩)) else 0

theorem coefficientsOfCharacters_pairing (m : «Σ».fullCones→Lattice n)
    (hcompat : ∀ s t (u : Lattice n),u∈s.val → u∈t.val →
      integerPairing u (m s)=integerPairing u (m t))
    (s : «Σ».fullCones) (u : Lattice n) (hu : u∈s.val) :
    integerPairing u (m s) = -«Σ».coefficientsOfCharacters hpure m u := by
  have hray : u∈«Σ».rays := «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hu
  rw [coefficientsOfCharacters,dif_pos hray,neg_neg]
  exact hcompat s («Σ».rayFullCone hpure ⟨u,hray⟩) u hu
    («Σ».mem_rayFullCone hpure ⟨u,hray⟩)

/-- A full smooth cone determines the lattice character uniquely from
its actual pairings with the primitive ray basis. -/
theorem eq_cartierLatticePoint_of_pairings (a : Lattice n→ℤ)
    (s : «Σ».fullCones) (m : Lattice n)
    (hm : ∀ u∈s.val,integerPairing u m = -a u) :
    m=«Σ».cartierLatticePoint a s := by
  apply (integralDualBasis («Σ».fullConeBasis s)).repr.injective
  ext i
  have hi : «Σ».fullConeBasis s i∈s.val := by
    rw [«Σ».fullConeBasis_ray_set]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have h := (hm _ hi).trans («Σ».cartierLatticePoint_pairing a s _ hi).symm
  simpa only [integerPairing,integralDualBasis_repr,mul_comm] using h

/-- Compatibility on common rays reconstructs one honest integral
coefficient function whose ordinary Cartier points are the given characters. -/
theorem characters_eq_cartierLatticePoint (m : «Σ».fullCones→Lattice n)
    (hcompat : ∀ s t (u : Lattice n),u∈s.val → u∈t.val →
      integerPairing u (m s)=integerPairing u (m t)) (s : «Σ».fullCones) :
    m s=«Σ».cartierLatticePoint («Σ».coefficientsOfCharacters hpure m) s :=
  «Σ».eq_cartierLatticePoint_of_pairings _ s (m s)
    («Σ».coefficientsOfCharacters_pairing hpure m hcompat s)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.characters_eq_cartierLatticePoint
