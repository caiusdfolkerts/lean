module

public import Continuation.Divisor.CoordinateCriterion

/-!
# Every complete regular fan has the geometric finite-ray-set interface

The finite generators are the canonical primitive vectors on the actual
one-dimensional faces of each cone. The construction preserves every
geometric cone and every primitive vector. Its downward and intersection
axioms follow from the genuine face lattice, rather than being postulated
for a new fan with merely the same ray set.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.FanInterfaces

open Set TauCeti.Toric
open PaperVerification.ToricGeometry
open scoped Classical BigOperators

variable {n : ℕ}

local notation "ι" => Unimodular.FanBridge.standardEmbedding n

/-- The canonical primitive lattice generators of the actual rays of a cone. -/
def primitiveRaySet (hι : IsIntegralLattice ι)
    {C : PointedCone ℝ (Ambient n)} (hC : IsToricCone ι C) : Finset (Lattice n) := by
  letI := ToricRay.finite_of_fg hC.fg
  letI : Fintype (ToricRay C) := Fintype.ofFinite _
  exact Finset.univ.image (primitiveGenerator hι hC)

lemma mem_primitiveRaySet_iff (hι : IsIntegralLattice ι)
    {C : PointedCone ℝ (Ambient n)} (hC : IsToricCone ι C) (u : Lattice n) :
    u ∈ primitiveRaySet hι hC ↔ ∃ ρ : ToricRay C, IsPrimitiveGenerator ι ρ u := by
  letI := ToricRay.finite_of_fg hC.fg
  letI : Fintype (ToricRay C) := Fintype.ofFinite _
  simp only [primitiveRaySet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ, isPrimitiveGenerator_primitiveGenerator hι hC ρ⟩
  · rintro ⟨ρ, hu⟩
    exact ⟨ρ, (hu.eq_primitiveGenerator hι hC).symm⟩

lemma primitiveRaySet_hull (hι : IsIntegralLattice ι)
    {C : PointedCone ℝ (Ambient n)} (hC : IsToricCone ι C) :
    latticeRayCone (primitiveRaySet hι hC) = C := by
  letI := ToricRay.finite_of_fg hC.fg
  letI : Fintype (ToricRay C) := Fintype.ofFinite _
  rw [latticeRayCone_eq_hull_image]
  simpa only [primitiveRaySet, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, dictionaryEmbedding_eq] using hC.hull_primitiveGenerator hι

lemma primitiveRaySet_mem_cone (hι : IsIntegralLattice ι)
    {C : PointedCone ℝ (Ambient n)} (hC : IsToricCone ι C)
    {u : Lattice n} (hu : u ∈ primitiveRaySet hι hC) : ι u ∈ C := by
  obtain ⟨ρ, hu⟩ := (mem_primitiveRaySet_iff hι hC u).mp hu
  exact ρ.1.isFaceOf.le hu.mem

/-- Primitive vectors on a face are exactly the ambient primitive ray
vectors whose images lie in that face. -/
lemma mem_primitiveRaySet_face_iff (hι : IsIntegralLattice ι)
    {C D : PointedCone ℝ (Ambient n)} (hC : IsToricCone ι C)
    (hDC : D.IsFaceOf C) (u : Lattice n) :
    u ∈ primitiveRaySet hι (hC.of_isFaceOf hDC) ↔
      u ∈ primitiveRaySet hι hC ∧ ι u ∈ D := by
  constructor
  · intro hu
    obtain ⟨ρ, hρ⟩ := (mem_primitiveRaySet_iff hι (hC.of_isFaceOf hDC) u).mp hu
    exact ⟨(mem_primitiveRaySet_iff hι hC u).mpr
      ⟨ToricRay.faceEmbedding hDC ρ, (isPrimitiveGenerator_faceEmbedding hDC ρ).mpr hρ⟩,
      ρ.1.isFaceOf.le hρ.mem⟩
  · rintro ⟨hu, huD⟩
    obtain ⟨ρ, hρ⟩ := (mem_primitiveRaySet_iff hι hC u).mp hu
    have hle : ρ.toPointedCone ≤ D := by
      rw [ρ.eq_hull_singleton (hC.salient.anti ρ.1.isFaceOf.le) hρ.mem
        (by simpa using hι.injective.ne hρ.ne_zero)]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huD)
    have hrange : ρ ∈ Set.range (ToricRay.faceEmbedding hDC) := by
      rw [ToricRay.range_faceEmbedding]
      exact hle
    obtain ⟨ν, hν⟩ := hrange
    exact (mem_primitiveRaySet_iff hι (hC.of_isFaceOf hDC) u).mpr
      ⟨ν, (isPrimitiveGenerator_faceEmbedding hDC ν).mp (hν.symm ▸ hρ)⟩

/-- All primitive generators of a regular cone extend to one full
integral basis in exactly the prescribed ambient rank. -/
lemma primitiveRaySet_smooth (hι : IsIntegralLattice ι)
    {C : PointedCone ℝ (Ambient n)} (hC : IsRegularCone ι C) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      primitiveRaySet hι hC.toIsToricCone = I.image b := by
  obtain ⟨m, b, r, hb⟩ := hC.exists_basis
  let e := b.indexEquiv (Pi.basisFun ℤ (Fin n))
  let b' := b.reindex e
  letI := ToricRay.finite_of_fg hC.fg
  letI : Fintype (ToricRay C) := Fintype.ofFinite _
  let I := Finset.univ.image (fun ρ => e (r ρ))
  have hb' (ρ : ToricRay C) : b' (e (r ρ)) =
      primitiveGenerator hι hC.toIsToricCone ρ := by
    simp only [b', Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    exact (hb.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator hι hC.toIsToricCone
  refine ⟨b', I, ?_⟩
  ext u
  constructor
  · intro hu
    obtain ⟨ρ, hρ⟩ := (mem_primitiveRaySet_iff hι hC.toIsToricCone u).mp hu
    exact Finset.mem_image.mpr ⟨e (r ρ),
      Finset.mem_image.mpr ⟨ρ, Finset.mem_univ _, rfl⟩,
      (hb' ρ).trans (hρ.eq_primitiveGenerator hι hC.toIsToricCone).symm⟩
  · intro hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hj
    rw [hb']
    exact (mem_primitiveRaySet_iff hι hC.toIsToricCone _).mpr
      ⟨ρ, isPrimitiveGenerator_primitiveGenerator hι hC.toIsToricCone ρ⟩

/-- Every subset of the primitive generators of a regular cone is the
exact primitive ray set of a genuine face. -/
lemma primitiveRaySet_subset_face (hι : IsIntegralLattice ι)
    {C : PointedCone ℝ (Ambient n)} (hC : IsRegularCone ι C)
    (A : Finset (Lattice n)) (hA : A ⊆ primitiveRaySet hι hC.toIsToricCone) :
    ∃ D : C.Face, primitiveRaySet hι (hC.toIsToricCone.of_isFaceOf D.isFaceOf) = A := by
  let S : Set (ToricRay C) := {ρ | primitiveGenerator hι hC.toIsToricCone ρ ∈ A}
  let D := (hC.faceOrderIso hι).symm S
  refine ⟨D, ?_⟩
  ext u
  rw [mem_primitiveRaySet_face_iff hι hC.toIsToricCone D.isFaceOf u]
  constructor
  · rintro ⟨hu, hDu⟩
    obtain ⟨ρ, hρ⟩ := (mem_primitiveRaySet_iff hι hC.toIsToricCone u).mp hu
    have hρD : ρ ∈ hC.faceOrderIso hι D := by
      apply (hC.mem_faceOrderIso_iff hι D ρ).mpr
      rw [← hρ.eq_primitiveGenerator hι hC.toIsToricCone]
      exact (PointedCone.Face.mem_toPointedCone (F := D) (ι u)).mp hDu
    have hρS : ρ ∈ S := by simpa only [D, OrderIso.apply_symm_apply] using hρD
    simpa only [S, Set.mem_setOf_eq,
      ← hρ.eq_primitiveGenerator hι hC.toIsToricCone] using hρS
  · intro hu
    refine ⟨hA hu, ?_⟩
    obtain ⟨ρ, hρ⟩ := (mem_primitiveRaySet_iff hι hC.toIsToricCone u).mp (hA hu)
    have hρS : ρ ∈ S := by
      simpa only [S, Set.mem_setOf_eq,
        ← hρ.eq_primitiveGenerator hι hC.toIsToricCone] using hu
    have hρD : ρ ∈ hC.faceOrderIso hι D := by
      simpa only [D, OrderIso.apply_symm_apply] using hρS
    have hm := (hC.mem_faceOrderIso_iff hι D ρ).mp hρD
    apply (PointedCone.Face.mem_toPointedCone (F := D) (ι u)).mpr
    simpa only [← hρ.eq_primitiveGenerator hι hC.toIsToricCone] using hm

/-- The complete regular fan represented by the primitive vectors of
all its actual cones. -/
def geometricFan (Φ : Fan (Unimodular.FanBridge.standardEmbedding n))
    (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular) :
    PaperVerification.ToricGeometry.SmoothCompleteFan n := by
  letI : Fintype Φ.cones := Fintype.ofFinite _
  let raysOf : Φ.cones → Finset (Lattice n) :=
    fun C => primitiveRaySet Φ.lattice (Φ.isToricCone C.property)
  refine {
    cones := Finset.univ.image raysOf
    smooth := ?_
    downward := ?_
    intersection := ?_
    complete := ?_ }
  · intro s hs
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hs
    exact primitiveRaySet_smooth Φ.lattice
      (Fan.isRegular_iff.mp hregular C.val C.property)
  · intro s hs t hts
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨D, hD⟩ := primitiveRaySet_subset_face Φ.lattice
      (Fan.isRegular_iff.mp hregular C.val C.property) t hts
    let D' : Φ.cones := ⟨D.toPointedCone, Φ.mem_of_isFaceOf C.property D.isFaceOf⟩
    exact Finset.mem_image.mpr ⟨D', Finset.mem_univ _, hD⟩
  · intro s hs t ht
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp ht
    have hCD := Φ.inf_isFaceOf_left C.property D.property
    have hDC := Φ.inf_isFaceOf_right C.property D.property
    have hset : primitiveRaySet Φ.lattice (Φ.isToricCone (Φ.inf_mem C.property D.property)) =
        raysOf C ∩ raysOf D := by
      ext u
      constructor
      · intro hu
        have hC := (mem_primitiveRaySet_face_iff Φ.lattice
          (Φ.isToricCone C.property) hCD u).mp hu
        have hD := (mem_primitiveRaySet_face_iff Φ.lattice
          (Φ.isToricCone D.property) hDC u).mp hu
        exact Finset.mem_inter.mpr ⟨hC.1, hD.1⟩
      · intro hu
        obtain ⟨huC, huD⟩ := Finset.mem_inter.mp hu
        apply (mem_primitiveRaySet_face_iff Φ.lattice
          (Φ.isToricCone C.property) hCD u).mpr
        exact ⟨huC, primitiveRaySet_mem_cone Φ.lattice (Φ.isToricCone C.property) huC,
          primitiveRaySet_mem_cone Φ.lattice (Φ.isToricCone D.property) huD⟩
    rw [← hset]
    simp only [raysOf, primitiveRaySet_hull]
  · intro x
    obtain ⟨C, hC, hx⟩ := Φ.isComplete_iff.mp hcomplete x
    refine ⟨raysOf ⟨C, hC⟩, Finset.mem_image.mpr ⟨⟨C, hC⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [raysOf, primitiveRaySet_hull] using hx

variable (Φ : Fan (Unimodular.FanBridge.standardEmbedding n))
  (hcomplete : Φ.IsComplete) (hregular : Φ.IsRegular)

/-- Every geometric cone is preserved exactly in both directions. -/
theorem dictionaryToricFan_geometricFan :
    dictionaryToricFan (geometricFan Φ hcomplete hregular) = Φ := by
  letI : Fintype Φ.cones := Fintype.ofFinite _
  apply Fan.ext
  ext C
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hs
    simpa only [primitiveRaySet_hull] using D.property
  · intro hC
    refine ⟨primitiveRaySet Φ.lattice (Φ.isToricCone hC), ?_,
      primitiveRaySet_hull Φ.lattice (Φ.isToricCone hC)⟩
    exact Finset.mem_image.mpr ⟨⟨C, hC⟩, Finset.mem_univ _, rfl⟩

/-- Primitive lattice generators are unchanged, including their signs. -/
theorem geometricFan_ray_iff (u : Lattice n) :
    u ∈ (geometricFan Φ hcomplete hregular).rays ↔ Unimodular.ConeBases.IsRay Φ u := by
  rw [← dictionaryToricFan_ray_iff, dictionaryToricFan_geometricFan]

#print axioms primitiveRaySet_subset_face
#print axioms geometricFan
#print axioms dictionaryToricFan_geometricFan
#print axioms geometricFan_ray_iff

end Unimodular.FanInterfaces
