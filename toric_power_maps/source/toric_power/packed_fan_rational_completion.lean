module

public import ToricPower.DivisorialRayPacking
public import ToricPower.FanRaySelectionMap
public import ToricPower.FanExteriorBoundary
public import ToricPower.PiecewiseExteriorFan
public import ToricPower.RayCompatibleCompletion

/-!
# Actual rational completion of a packed regular fan

Every old ray has a complete star in the packing. The integral projection
fixing new rays and killing old rays is the identity on its boundary.
The checked interior/exterior gluing therefore gives a complete rational
fan retaining every original cone. Its stronger old-ray invariant survives
every subsequent relative refinement.
-/

@[expose] public noncomputable section
open TauCeti.Toric Set
open scoped Classical

namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (original : Fan i) (packing : RegularDivisorialRayPacking original)

local instance packedCompletionConeFintype : Fintype packing.fan.cones := Fintype.ofFinite _

def packedRayProjection (σ : packing.fan.cones) : N →+ N :=
  raySelectionLatticeMap packing.fan packing.regular
    (fun ρ => ρ.toCone.val ∉ original.cones) σ

theorem packedRayProjection_compatible (σ τ : packing.fan.cones) (x : V)
    (member : x ∈ σ.val ⊓ τ.val) :
    packing.fan.lattice.extend i (packedRayProjection original packing σ) x =
      packing.fan.lattice.extend i (packedRayProjection original packing τ) x :=
  raySelectionRealMap_compatible packing.fan packing.regular
    (fun ρ => ρ.toCone.val ∉ original.cones) σ τ x member

theorem packedRayProjection_fixedFace (σ : packing.fan.cones) :
    (σ.val ⊓ PointedCone.ofSubmodule
      (LinearMap.id-packing.fan.lattice.extend i (packedRayProjection original packing σ)).ker).IsFaceOf σ.val :=
  raySelectionRealMap_fixedFace packing.fan packing.regular
    (fun ρ => ρ.toCone.val ∉ original.cones) σ

theorem packedSignCone_adapted
    (sign : FanHyperplaneIndex packing.fan → Ordering) (σ : packing.fan.cones) :
    (hyperplaneSignCone (fun k => packing.fan.lattice.realCharacter
      (fanHyperplaneCharacters packing.fan packing.regular k)) sign ⊓ σ.val).IsFaceOf
      (hyperplaneSignCone (fun k => packing.fan.lattice.realCharacter
        (fanHyperplaneCharacters packing.fan packing.regular k)) sign) := by
  apply inf_isFaceOf_of_weakSigns
    (fun p => packing.fan.lattice.realCharacter (regularFanConeCharacters packing.fan packing.regular σ p))
    _ σ.val (regularFanConeCharacters_membership packing.fan packing.regular σ)
  intro p
  have constrained (x : V) (member : x ∈ hyperplaneSignCone
      (fun k => packing.fan.lattice.realCharacter (fanHyperplaneCharacters packing.fan packing.regular k)) sign) :=
    (mem_hyperplaneSignCone _ sign x).mp member (σ,p)
  cases h : sign (σ,p)
  · right
    intro x member
    simpa only [h,signConstraint,fanHyperplaneCharacters] using constrained x member
  · left
    intro x member
    have zero : packing.fan.lattice.realCharacter
        (regularFanConeCharacters packing.fan packing.regular σ p) x = 0 := by
      simpa only [h,signConstraint,fanHyperplaneCharacters] using constrained x member
    exact zero.ge
  · left
    intro x member
    simpa only [h,signConstraint,fanHyperplaneCharacters] using constrained x member

theorem packed_oldRay_covers (ρ : packing.fan.Ray) (old : ρ.toCone.val ∈ original.cones) :
    RayStarCovers packing.fan (fanRayRealVector packing.fan ρ) := by
  let oldRay : original.Ray := ⟨⟨ρ.toCone.val,old⟩,ρ.property⟩
  have same : subfanRayEmbedding original packing.fan packing.contains oldRay = ρ := rfl
  rw [← same,fanRayRealVector,subfanRayEmbedding_primitive]
  exact packing.covers oldRay

theorem packedRayProjection_fixedExterior (σ : packing.fan.cones)
    (sign : FanHyperplaneIndex packing.fan → Ordering)
    (outside : IsExteriorSign packing.fan (fanHyperplaneCharacters packing.fan packing.regular) sign)
    (x : V) (member : x ∈ σ.val ⊓ hyperplaneSignCone
      (fun k => packing.fan.lattice.realCharacter
        (fanHyperplaneCharacters packing.fan packing.regular k)) sign) :
    packing.fan.lattice.extend i (packedRayProjection original packing σ) x = x := by
  letI := packing.fan.lattice.finiteDimensional
  let coordinates := (Module.finBasis ℝ V).equivFun
  letI : NormedAddCommGroup V := NormedAddCommGroup.induced V _ coordinates coordinates.injective
  letI : NormedSpace ℝ V := NormedSpace.induced ℝ V _ coordinates
  apply raySelectionRealMap_fixed_of_coordinates packing.fan packing.regular
    (fun ρ => ρ.toCone.val ∉ original.cones) σ member.1
  intro ρ discarded
  have old : ρ.toCone.val ∈ original.cones := not_not.mp discarded
  exact exteriorCone_oldRayCoordinate_zero packing.fan packing.regular _
    (hyperplaneSignCone_rational packing.fan.lattice
      (fanHyperplaneCharacters packing.fan packing.regular) sign).fg
    (packedSignCone_adapted original packing sign) outside ρ
    (packed_oldRay_covers original packing ρ old) σ member.2 member.1

theorem packedRayProjection_old_zero (σ : original.cones) (x : V) (member : x ∈ σ.val) :
    packing.fan.lattice.extend i (packedRayProjection original packing
      (subfanConeEmbedding original packing.fan packing.contains σ)) x = 0 := by
  apply raySelectionRealMap_zero packing.fan packing.regular
    (fun ρ => ρ.toCone.val ∉ original.cones) _ ?_ member
  intro ρ below
  apply not_not.mpr
  exact original.mem_of_isFaceOf σ.property
    (packing.fan.isFaceOf_of_le (packing.contains σ.property) ρ.toCone.property below)

theorem packed_exterior_no_oldRay
    (sign : FanHyperplaneIndex packing.fan → Ordering)
    (outside : IsExteriorSign packing.fan (fanHyperplaneCharacters packing.fan packing.regular) sign)
    (ρ : original.Ray) :
    ¬ ρ.toCone.val ≤ hyperplaneSignCone
      (fun k => packing.fan.lattice.realCharacter
        (fanHyperplaneCharacters packing.fan packing.regular k)) sign := by
  letI := packing.fan.lattice.finiteDimensional
  let coordinates := (Module.finBasis ℝ V).equivFun
  letI : NormedAddCommGroup V := NormedAddCommGroup.induced V _ coordinates coordinates.injective
  letI : NormedSpace ℝ V := NormedSpace.induced ℝ V _ coordinates
  intro contained
  let oldRay := subfanRayEmbedding original packing.fan packing.contains ρ
  have interiorMember := ray_mem_interior_support_of_starCovers packing.fan packing.regular oldRay
    (packed_oldRay_covers original packing oldRay ρ.toCone.property)
  have disjoint := exteriorCone_disjoint_interior packing.fan _
    (hyperplaneSignCone_rational packing.fan.lattice
      (fanHyperplaneCharacters packing.fan packing.regular) sign).fg
    (packedSignCone_adapted original packing sign) outside
  exact Set.disjoint_left.mp disjoint (contained (fanRayRealVector_mem packing.fan oldRay)) interiorMember

variable (nonempty : original.cones.Nonempty)

include nonempty in
theorem packing_cones_nonempty : packing.fan.cones.Nonempty := nonempty.mono packing.contains

def packedRationalFan : Fan i :=
  exteriorCompletedFan packing.fan packing.regular
    (fanHyperplaneCharacters packing.fan packing.regular) (packedRayProjection original packing)
    (packedRayProjection_compatible original packing)
    (packedSignCone_adapted original packing)
    (packedRayProjection_fixedFace original packing)
    (packedRayProjection_fixedExterior original packing)
    (fanHyperplaneCharacters_separate packing.fan packing.regular (packing_cones_nonempty original packing nonempty))

theorem packedRationalFan_complete : (packedRationalFan original packing nonempty).IsComplete :=
  exteriorCompletedFan_complete packing.fan packing.regular
    (fanHyperplaneCharacters packing.fan packing.regular) (packedRayProjection original packing)
    (packedRayProjection_compatible original packing) (packedSignCone_adapted original packing)
    (packedRayProjection_fixedFace original packing) (packedRayProjection_fixedExterior original packing)
    (fanHyperplaneCharacters_separate packing.fan packing.regular (packing_cones_nonempty original packing nonempty))

theorem packedRationalFan_contains : original.cones ⊆ (packedRationalFan original packing nonempty).cones := by
  intro σ member
  exact exteriorCompletedFan_retains_zero packing.fan packing.regular
    (fanHyperplaneCharacters packing.fan packing.regular) (packedRayProjection original packing)
    (packedRayProjection_compatible original packing) (packedSignCone_adapted original packing)
    (packedRayProjection_fixedFace original packing) (packedRayProjection_fixedExterior original packing)
    (fanHyperplaneCharacters_separate packing.fan packing.regular (packing_cones_nonempty original packing nonempty))
    (subfanConeEmbedding original packing.fan packing.contains ⟨σ,member⟩)
    (packedRayProjection_old_zero original packing ⟨σ,member⟩)

theorem packedRationalFan_oldRays (σ : (packedRationalFan original packing nonempty).cones) :
    ∃ τ : original.cones, ∀ ρ : original.Ray, ρ.toCone.val ≤ σ.val → ρ.toCone.val ≤ τ.val := by
  have member := σ.property
  unfold packedRationalFan exteriorCompletedFan at member
  rw [Fan.mem_ofCones_cones] at member
  obtain ⟨_,⟨index,rfl⟩,face⟩ := member
  rcases index with ⟨current,sign⟩ | ⟨sign,outside⟩
  · refine ⟨subfanOldRayFace original packing.fan packing.regular packing.full current,?_⟩
    intro ρ below
    apply (subfanOldRayFace_rays original packing.fan packing.regular packing.full current
      (subfanRayEmbedding original packing.fan packing.contains ρ)).mpr
    exact ⟨ρ.toCone.property,(below.trans face.le).trans inf_le_left⟩
  · obtain ⟨τ,old⟩ := nonempty
    refine ⟨⟨τ,old⟩,?_⟩
    intro ρ below
    exact False.elim (packed_exterior_no_oldRay original packing sign outside ρ (below.trans face.le))

/-- The genuine complete rational extension with its preserved old-ray invariant. -/
def packedRayCompatibleCompletion : RayCompatibleCompletion original where
  fan := packedRationalFan original packing nonempty
  contains := packedRationalFan_contains original packing nonempty
  complete := packedRationalFan_complete original packing nonempty
  oldRays := packedRationalFan_oldRays original packing nonempty

end ToricPower.FanSubdivision
end
