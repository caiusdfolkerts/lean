module

public import PaperVerification.ToricOrbitClosedImmersion
public import PaperVerification.ToricQuotientFaceSupport
public import PaperVerification.ToricFanIntegralCoefficients
public import PaperVerification.ToricPrincipalChartModules

@[expose] public section

/-!
# Cartier equations on an actual quotient-star orbit closure

A common integral character is used to normalize all local generators
along the orbit cone. The normalized characters lie in its actual
annihilator lattice. Their projections are proved to be the Cartier
characters of the quotient fan, and actual transition units are mapped
by the previously constructed surjective chart homomorphisms.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b∈«Σ».cones)

def orbitRestrictionCoefficients (a : Lattice n→ℤ) (m₀ : Lattice n) :
    Lattice (n-I.card)→ℤ := fun u =>
  if hu : u∈(«Σ».completeQuotientStarFan b I hF).rays then
    a («Σ».starRayLift b I hF ⟨u,hu⟩)+
      integerPairing («Σ».starRayLift b I hF ⟨u,hu⟩) m₀
  else 0

theorem orbitRestrictionCoefficients_projected (a : Lattice n→ℤ) (m₀ : Lattice n)
    {s : Finset (Lattice n)} (hs : s∈«Σ».cones) (hIs : I.image b⊆s)
    {u : Lattice n} (hu : u∈s\I.image b) :
    «Σ».orbitRestrictionCoefficients b I hF a m₀ (coneQuotientLattice b I u) =
      a u+integerPairing u m₀ := by
  have hp := «Σ».projected_starRay_mem b I hF hs hIs hu
  simp only [orbitRestrictionCoefficients,dif_pos hp]
  rw [«Σ».starRayLift_projected b I hF hs hIs hu]

def orbitFullConeIndex (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    («Σ».completeQuotientStarFan b I hF).fullCones :=
  ⟨orbitQuotientCone b I s.val,Finset.mem_filter.mpr ⟨
    («Σ».mem_quotientStarCones b I _).mpr ⟨s.val,«Σ».fullCones_mem s,hIs,rfl⟩,by
      have himage : (orbitQuotientCone b I s.val).card=(s.val\I.image b).card := by
        apply Finset.card_image_of_injOn
        intro v hv w hw he
        exact «Σ».coneQuotient_injective_star_rays b I
          («Σ».fullCones_mem s) («Σ».fullCones_mem s) hIs hIs hv hw he
      rw [himage,Finset.card_sdiff_of_subset hIs,
        Finset.card_image_of_injective I b.injective,«Σ».fullCones_card]⟩⟩

theorem orbit_normalized_character_annihilates (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    ∀ u∈I.image b,integerPairing u («Σ».cartierLatticePoint a s-m₀)=0 := by
  intro u hu
  rw [integerPairing_sub,«Σ».cartierLatticePoint_pairing a s u (hIs hu),hm₀ u hu,sub_self]

/-- Projected local equations are uniquely the actual Cartier equations
of the quotient fan. -/
theorem orbit_cartierLatticePoint (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s : «Σ».fullCones) (hIs : I.image b⊆s.val) :
    faceCharacterProjection b I («Σ».cartierLatticePoint a s-m₀) =
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀)
        («Σ».orbitFullConeIndex b I hF s hIs) := by
  apply («Σ».completeQuotientStarFan b I hF).eq_cartierLatticePoint_of_pairings
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [← integerPairing_faceTangentLattice,
    faceTangentLattice_projection b I _
      («Σ».orbit_normalized_character_annihilates b I a m₀ hm₀ s hIs),
    integerPairing_sub,
    «Σ».cartierLatticePoint_pairing a s u (Finset.mem_sdiff.mp hu).1,
    «Σ».orbitRestrictionCoefficients_projected b I hF a m₀ («Σ».fullCones_mem s) hIs hu]
  ring

theorem orbit_cartier_difference (a : Lattice n→ℤ) (m₀ : Lattice n)
    (hm₀ : ∀ u∈I.image b,integerPairing u m₀ = -a u)
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val) :
    faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t) =
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) («Σ».orbitFullConeIndex b I hF s hIs) -
      («Σ».completeQuotientStarFan b I hF).cartierLatticePoint
        («Σ».orbitRestrictionCoefficients b I hF a m₀) («Σ».orbitFullConeIndex b I hF t hIt) := by
  rw [← «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ s hIs,
    ← «Σ».orbit_cartierLatticePoint b I hF a m₀ hm₀ t hIt,← map_sub]
  congr 1
  abel

theorem orbitQuotientCone_inter (s t : «Σ».OrbitConeIndex b I) :
    orbitQuotientCone b I (s.val∩t.val) =
      orbitQuotientCone b I s.val∩orbitQuotientCone b I t.val := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_sdiff.mp hu with ⟨hut,huI⟩
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hut).1,huI⟩,rfl⟩,
      Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hut).2,huI⟩,rfl⟩⟩
  · intro hv
    obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).1
    obtain ⟨w,hw,hwv⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hv).2
    have huw := «Σ».coneQuotient_injective_star_rays b I s.property.1 t.property.1
      s.property.2 t.property.2 hu hw (huv.trans hwv.symm)
    subst w
    exact Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr
      ⟨Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1,(Finset.mem_sdiff.mp hw).1⟩,
        (Finset.mem_sdiff.mp hu).2⟩,huv⟩

variable (k : Type*) [CommRing k]

/-- The exact regular transition character is sent to its projected
character by the actual closed-immersion chart algebra homomorphism. -/
theorem orbit_cartierTransition_character (a : Lattice n→ℤ)
    (s t : «Σ».fullCones) (hIs : I.image b⊆s.val) (hIt : I.image b⊆t.val) :
    ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
      («Σ».cartierTransitionUnit k a s t :
        monoidChartAlgebra k (dualConeMonoid (s.val∩t.val)))) :
          AddMonoidAlgebra k (Lattice (n-I.card))) =
      AddMonoidAlgebra.single
        (faceCharacterProjection b I («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)) 1 := by
  have hz : ∀ u∈I.image b,
      integerPairing u («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)=0 := by
    intro u hu
    rw [integerPairing_sub,«Σ».cartierLatticePoint_pairing a s u (hIs hu),
      «Σ».cartierLatticePoint_pairing a t u (hIt hu),sub_self]
  change ((orbitQuotientAlgebraMap k b I (s.val∩t.val) (Finset.subset_inter hIs hIt)
    (chartCharacter k (dualConeMonoid (s.val∩t.val))
      («Σ».cartierLatticePoint a s-«Σ».cartierLatticePoint a t)
      («Σ».cartier_difference_mem_overlap a s t).1)) :
        AddMonoidAlgebra k (Lattice (n-I.card))) = _
  rw [orbitQuotientAlgebraMap_character,dif_pos hz]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_cartierLatticePoint
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbit_cartierTransition_character
