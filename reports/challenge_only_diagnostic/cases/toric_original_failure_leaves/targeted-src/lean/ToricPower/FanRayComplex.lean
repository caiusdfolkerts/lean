module

public import ToricPower.FanRayIndex
public import ToricPower.CechDowkerFaces
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face

/-!
# The incidence complex is the actual ray complex of a regular fan

The geometric input is the proved simplicial-cone face theorem in TauCeti:
every subset of the rays of a regular cone is exactly the ray set of a face.
Here that theorem is transported from cone rays to the intrinsic rays of the
whole fan.  Thus the negative-ray incidence complex has precisely the
nonempty faces of the induced fan complex, not extra simplices inserted by
definition.  The empty face is handled by the augmented cochain convention
in the cohomological development.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (fan : Fan i)

/-- Every subset of the rays of a regular cone is the exact ray set of a
cone of the same fan.  This includes the empty subset. -/
theorem exists_cone_raySet_eq_of_subset (regular : fan.IsRegular)
    (cone : fan.cones) (rays : Set fan.Ray)
    (contained : ∀ ray ∈ rays, ray.toCone ≤ cone) :
    ∃ face : fan.cones, face ≤ cone ∧
      ∀ ray : fan.Ray, ray.toCone ≤ face ↔ ray ∈ rays := by
  let localRays : Set (ToricRay cone.val) :=
    {ray | Fan.Ray.ofToricRay fan cone ray ∈ rays}
  obtain ⟨face, exactRays⟩ := exists_face_rays_eq_of_isSimplicial
    (((Fan.isRegular_iff).mp regular cone.val cone.property).isSimplicial fan.lattice) localRays
  let fanFace : fan.cones :=
    ⟨face.toPointedCone, fan.mem_of_isFaceOf cone.property face.isFaceOf⟩
  have face_le : fanFace ≤ cone := face.isFaceOf.le
  refine ⟨fanFace, face_le, ?_⟩
  intro ray
  by_cases lies : ray.toCone ≤ cone
  · have returns : Fan.Ray.ofToricRay fan cone (ray.toToricRay fan cone lies) = ray := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have comparison := exactRays (ray.toToricRay fan cone lies)
    change (ray.toCone.val ≤ face.toPointedCone ↔
      Fan.Ray.ofToricRay fan cone (ray.toToricRay fan cone lies) ∈ rays) at comparison
    rw [returns] at comparison
    exact comparison
  · constructor
    · intro inFace
      exact False.elim (lies (inFace.trans face_le))
    · intro inRays
      exact False.elim (lies (contained ray inRays))

/-- Finite nonempty subsets of rays lying in a common cone.  The next theorem
identifies these with literal cone ray sets under regularity. -/
def coneRaySubsetComplex : PreAbstractSimplicialComplex fan.Ray where
  faces := {rays | rays.Nonempty ∧ ∃ cone : fan.cones,
    ∀ ray ∈ rays, ray.toCone ≤ cone}
  isRelLowerSet_faces := by
    intro rays member
    refine ⟨member.1, ?_⟩
    intro smaller subset nonempty
    obtain ⟨cone, contains⟩ := member.2
    exact ⟨nonempty, cone, fun ray present => contains ray (subset present)⟩

theorem mem_coneRaySubsetComplex_iff_raySet (regular : fan.IsRegular)
    (rays : Finset fan.Ray) :
    rays ∈ coneRaySubsetComplex fan ↔ rays.Nonempty ∧
      ∃ cone : fan.cones, ∀ ray : fan.Ray, ray.toCone ≤ cone ↔ ray ∈ rays := by
  constructor
  · rintro ⟨nonempty, cone, contains⟩
    obtain ⟨face, _, exactRays⟩ := exists_cone_raySet_eq_of_subset fan regular
      cone (rays : Set fan.Ray) contains
    exact ⟨nonempty, face, exactRays⟩
  · rintro ⟨nonempty, cone, exactRays⟩
    exact ⟨nonempty, cone, fun ray present => (exactRays ray).mpr present⟩

/-- The row complex for any enumeration of all charts is literally the
induced complex on the selected negative rays.  The conclusion uses exact
ray sets of actual fan cones, with no common-chart proxy left over. -/
theorem negativeRayComplex_face_iff_cone_raySet (regular : fan.IsRegular)
    {Index : Type} (charts : Index → fan.cones)
    (surjective : Function.Surjective charts) (negative : fan.Ray → Prop)
    (rays : Finset (NegativeSupportCech.NegativeRay negative)) :
    rays ∈ NegativeSupportCech.negativeRayComplex
      (fun ray index => ray.toCone ≤ charts index) negative ↔
      rays.Nonempty ∧ ∃ cone : fan.cones, ∀ ray : fan.Ray,
        ray.toCone ≤ cone ↔ ∃ proof : negative ray, ⟨ray, proof⟩ ∈ rays := by
  constructor
  · rintro ⟨nonempty, index, contains⟩
    let selected : Set fan.Ray :=
      {ray | ∃ proof : negative ray, ⟨ray, proof⟩ ∈ rays}
    have inChart : ∀ ray ∈ selected, ray.toCone ≤ charts index := by
      rintro ray ⟨proof, present⟩
      exact contains ⟨ray, proof⟩ present
    obtain ⟨face, _, exactRays⟩ := exists_cone_raySet_eq_of_subset fan regular
      (charts index) selected inChart
    exact ⟨nonempty, face, exactRays⟩
  · rintro ⟨nonempty, cone, exactRays⟩
    obtain ⟨index, rfl⟩ := surjective cone
    refine ⟨nonempty, index, ?_⟩
    intro ray present
    exact (exactRays ray.val).mpr ⟨ray.property, present⟩

end ToricPower
