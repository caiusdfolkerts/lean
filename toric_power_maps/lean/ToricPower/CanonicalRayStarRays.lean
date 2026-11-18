module

public import ToricPower.RegularQuotientPrimitive
public import ToricPower.SubfanRayRetraction

/-!
# The old rays of a quotient star and their canonical integral lifts

The rays of the quotient star correspond exactly to the original rays
which share a cone with the selected ray, excluding that ray itself.
The corresponding original primitive vector is an integral lift of the
quotient primitive vector. This exact identification is needed to keep
old cones unchanged during relative completion.
-/

@[expose] public noncomputable section
open TauCeti TauCeti.Toric
namespace ToricPower.FanSubdivision

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i) (regular : fan.IsRegular) (ray : fan.Ray)

local notation "a" => fanRayPrimitiveGenerator fan ray
local notation "q" => Submodule.mkQ (Submodule.span ℝ {i a})
local notation "qZ" => Submodule.mkQ (Submodule.span ℤ {a})
local notation "star" => canonicalRayStar fan ray

abbrev OriginalStarLinkRay :=
  {ρ : fan.Ray // ρ ≠ ray ∧ ∃ σ : OriginalRayStarCone fan ray, ρ.toCone ≤ σ.val}

include regular in
theorem exists_oldStarPairCone (other : OriginalStarLinkRay fan ray) :
    ∃ σ : OriginalRayStarCone fan ray,
      ∀ ρ : fan.Ray, ρ.toCone ≤ σ.val ↔ ρ = ray ∨ ρ = other.val := by
  obtain ⟨parent,below⟩ := other.property.2
  obtain ⟨face,_,rays⟩ := exists_cone_raySet_eq_of_subset fan regular parent.val
    {ρ | ρ = ray ∨ ρ = other.val} (by
      rintro ρ (rfl | rfl)
      · exact parent.property
      · exact below)
  exact ⟨⟨face,(rays ray).mpr (Or.inl rfl)⟩,rays⟩

def oldStarPairCone (other : OriginalStarLinkRay fan ray) : OriginalRayStarCone fan ray :=
  (exists_oldStarPairCone fan regular ray other).choose

theorem oldStarPairCone_rays (other : OriginalStarLinkRay fan ray) (ρ : fan.Ray) :
    ρ.toCone ≤ (oldStarPairCone fan regular ray other).val ↔ ρ = ray ∨ ρ = other.val :=
  (exists_oldStarPairCone fan regular ray other).choose_spec ρ

theorem oldStarPairCone_other (other : OriginalStarLinkRay fan ray) :
    other.val.toCone ≤ (oldStarPairCone fan regular ray other).val :=
  (oldStarPairCone_rays fan regular ray other other.val).mpr (Or.inr rfl)

theorem oldStarPairCone_le_iff (other : OriginalStarLinkRay fan ray)
    (σ : OriginalRayStarCone fan ray) :
    oldStarPairCone fan regular ray other ≤ σ ↔ other.val.toCone ≤ σ.val := by
  constructor
  · intro below
    exact (oldStarPairCone_other fan regular ray other).trans below
  · intro below
    apply fanCone_le_of_rays fan
    intro ρ member
    rcases (oldStarPairCone_rays fan regular ray other ρ).mp member with rfl | rfl
    · exact σ.property
    · exact below

theorem selectedRay_projection_zero : q (fanRayRealVector fan ray) = 0 :=
  LinearMap.mem_ker.mp (by
    rw [Submodule.ker_mkQ]
    exact Submodule.mem_span_singleton_self _)

theorem selectedRay_map_eq_bot : PointedCone.map q ray.toCone.val = ⊥ := by
  rw [fanRay_eq_hull_realVector,cone_map_hull,Set.image_singleton,
    selectedRay_projection_zero fan ray]
  exact Submodule.span_zero_singleton _

theorem oldStarPairCone_map (other : OriginalStarLinkRay fan ray) :
    PointedCone.map q (oldStarPairCone fan regular ray other).val.val =
      PointedCone.hull ℝ {q (fanRayRealVector fan other.val)} := by
  let cone := (oldStarPairCone fan regular ray other).val
  apply le_antisymm
  · have below : cone.val ≤ PointedCone.comap q
        (PointedCone.hull ℝ {q (fanRayRealVector fan other.val)}) := by
      rw [← (fan.isToricCone cone.property).hull_primitiveGenerator fan.lattice]
      apply Submodule.span_le.mpr
      rintro _ ⟨_,⟨ρ,rfl⟩,rfl⟩
      change q (i (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ρ)) ∈
        PointedCone.hull ℝ {q (fanRayRealVector fan other.val)}
      rw [← fanRayPrimitiveGenerator_ofToricRay fan cone ρ]
      change q (fanRayRealVector fan (Fan.Ray.ofToricRay fan cone ρ)) ∈
        PointedCone.hull ℝ {q (fanRayRealVector fan other.val)}
      have alternatives := (oldStarPairCone_rays fan regular ray other
        (Fan.Ray.ofToricRay fan cone ρ)).mp (Fan.Ray.toCone_ofToricRay_le fan cone ρ)
      rcases alternatives with first | second
      · rw [first,selectedRay_projection_zero fan ray]
        exact Submodule.zero_mem _
      · rw [second]
        exact PointedCone.subset_hull (Set.mem_singleton _)
    intro z member
    obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp member
    exact below hx
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact PointedCone.mem_map.mpr ⟨fanRayRealVector fan other.val,
      oldStarPairCone_other fan regular ray other (fanRayRealVector_mem fan other.val),rfl⟩

include regular in
theorem oldStarRay_projected_nonzero (other : OriginalStarLinkRay fan ray) :
    q (fanRayRealVector fan other.val) ≠ 0 := by
  have primitive := canonicalRayStar_otherRay_primitive fan regular ray
    (oldStarPairCone fan regular ray other) other.val
    (oldStarPairCone_other fan regular ray other) other.property.1
  have lattice := rayQuotient_isIntegralLattice i a fan.lattice (selectedRay_isPrimitive fan ray)
  have nonzero := lattice.injective.ne primitive.ne_zero
  simpa only [map_zero,rayQuotientLatticeMap_apply,fanRayRealVector] using nonzero

theorem oldStarPairCone_image_finrank (other : OriginalStarLinkRay fan ray) :
    Module.finrank ℝ (Submodule.span ℝ
      ((PointedCone.map q (oldStarPairCone fan regular ray other).val.val) :
        Set (RayQuotientSpace i a))) = 1 := by
  rw [oldStarPairCone_map fan regular ray other]
  exact PointedCone.finrank_span_coe_hull_singleton
    (oldStarRay_projected_nonzero fan regular ray other)

/-- The actual quotient ray determined by an adjacent original ray. -/
def oldStarRayProjection (other : OriginalStarLinkRay fan ray) : (star).Ray :=
  ⟨⟨PointedCone.map q (oldStarPairCone fan regular ray other).val.val,
    (mem_canonicalRayStar_iff fan ray _).mpr
      ⟨(oldStarPairCone fan regular ray other).val.val,
        (oldStarPairCone fan regular ray other).val.property,
        (oldStarPairCone fan regular ray other).property,PointedCone.IsFaceOf.refl _⟩⟩,
    oldStarPairCone_image_finrank fan regular ray other⟩

/-- Primitive vectors, rather than merely real ray directions, match
under the literal quotient map. -/
theorem oldStarRayProjection_primitive (other : OriginalStarLinkRay fan ray) :
    qZ (fanRayPrimitiveGenerator fan other.val) =
      fanRayPrimitiveGenerator star (oldStarRayProjection fan regular ray other) := by
  let projected := oldStarRayProjection fan regular ray other
  have primitive := canonicalRayStar_otherRay_primitive fan regular ray
    (oldStarPairCone fan regular ray other) other.val
    (oldStarPairCone_other fan regular ray other) other.property.1
  have property : IsPrimitiveGenerator (rayQuotientLatticeMap i a)
      (projected.toToricRay star projected.toCone le_rfl)
      (qZ (fanRayPrimitiveGenerator fan other.val)) := by
    apply isPrimitiveGenerator_iff.mpr
    refine ⟨?_,primitive⟩
    rw [rayQuotientLatticeMap_apply]
    change q (fanRayRealVector fan other.val) ∈
      PointedCone.map q (oldStarPairCone fan regular ray other).val.val
    exact PointedCone.mem_map.mpr ⟨fanRayRealVector fan other.val,
      oldStarPairCone_other fan regular ray other (fanRayRealVector_mem fan other.val),rfl⟩
  exact property.eq_primitiveGenerator (star).lattice ((star).isToricCone projected.toCone.property)

theorem oldStarRayProjection_injective : Function.Injective (oldStarRayProjection fan regular ray) := by
  intro first second same
  have coneEq : oldStarPairCone fan regular ray first = oldStarPairCone fan regular ray second := by
    apply (originalStarOrderIso fan ray).injective
    exact congrArg (fun ρ : (star).Ray => ρ.toCone) same
  have below := oldStarPairCone_other fan regular ray first
  rw [coneEq] at below
  rcases (oldStarPairCone_rays fan regular ray second first.val).mp below with old | same
  · exact False.elim (first.property.1 old)
  · exact Subtype.ext same

omit regular ray in
theorem fanRays_eq_of_le (first second : fan.Ray) (below : first.toCone ≤ second.toCone) :
    first = second := by
  have localEq := ToricRay.eq_of_toPointedCone_le
    (fan.isToricCone second.toCone.property).salient
    (ν := first.toToricRay fan second.toCone below)
    (ρ := second.toToricRay fan second.toCone le_rfl) below
  exact congrArg (Fan.Ray.ofToricRay fan second.toCone) localEq

theorem oldStarRayProjection_surjective : Function.Surjective (oldStarRayProjection fan regular ray) := by
  intro δ
  let σ := (originalStarOrderIso fan ray).symm δ.toCone
  have imageEq : PointedCone.map q σ.val.val = δ.toCone.val :=
    congrArg Subtype.val ((originalStarOrderIso fan ray).apply_symm_apply δ.toCone)
  have existsOther : ∃ ρ : fan.Ray, ρ.toCone ≤ σ.val ∧ ρ ≠ ray := by
    by_contra missing
    have below : σ.val ≤ ray.toCone := by
      apply fanCone_le_of_rays fan
      intro ρ member
      have same : ρ = ray := by
        by_contra different
        exact missing ⟨ρ,member,different⟩
      rw [same]
    have zeroImage : PointedCone.map q σ.val.val = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← selectedRay_map_eq_bot fan ray]
      intro z member
      obtain ⟨x,hx,rfl⟩ := PointedCone.mem_map.mp member
      exact PointedCone.mem_map.mpr ⟨x,below hx,rfl⟩
    exact (Fan.Ray.toCone_ne_bot star δ) (imageEq.symm.trans zeroImage)
  obtain ⟨ρ,below,different⟩ := existsOther
  let source : OriginalStarLinkRay fan ray := ⟨ρ,different,σ,below⟩
  refine ⟨source,fanRays_eq_of_le star _ δ ?_⟩
  change PointedCone.map q (oldStarPairCone fan regular ray source).val.val ≤ δ.toCone.val
  rw [← imageEq]
  exact (original_star_projection_le_iff fan ray _ σ).mpr
    ((oldStarPairCone_le_iff fan regular ray source σ).mpr below)

/-- The exact finite ray dictionary, including the original integral
primitive-vector lifts used in the completed-star construction. -/
def originalStarRayEquiv : OriginalStarLinkRay fan ray ≃ (star).Ray :=
  Equiv.ofBijective (oldStarRayProjection fan regular ray)
    ⟨oldStarRayProjection_injective fan regular ray,oldStarRayProjection_surjective fan regular ray⟩

end ToricPower.FanSubdivision
end
