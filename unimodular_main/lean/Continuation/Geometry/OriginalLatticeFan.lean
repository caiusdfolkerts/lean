module

public import Continuation.Geometry.OriginalLatticeAtlas
public import Continuation.Divisor.FanInterfaces
public import Recovery.Unimodular.PriorExtensions.FanEquivCompatibility

@[expose] public section

/-!
# The fan belonging to the original-lattice atlas

The real coordinate map is obtained by scalar extension of the integral
basis.  Mapping the complete regular coordinate fan back along this map
produces an ordinary fan in the original lattice.  Its cones are exactly
the cones whose literal dual semigroups occur in the proved open atlas.
The scheme itself is still the original `F.fanScheme k`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry TauCeti.Toric
open scoped Classical

universe u v

namespace PaperVerification.OriginalLatticeCharts

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    {ι : N →+ V} (hi : IsIntegralLattice ι)

/-- Coordinates on the actual ambient real vector space, obtained by
scalar extension of the same integral basis. -/
def realCoordinates : V ≃ₗ[ℝ] Ambient n :=
  (hi.isBaseChange.basis b).equivFun

@[simp] theorem realCoordinates_lattice (v : N) :
    realCoordinates b hi (ι v) =
      PaperVerification.ToricGeometry.embed n (b.equivFun v) := by
  ext j
  change (hi.isBaseChange.basis b).repr (ι v) j = (b.repr v j : ℝ)
  exact hi.isBaseChange.basis_repr_comp_apply b v j

@[simp] theorem realCoordinates_symm_lattice (v : Lattice n) :
    (realCoordinates b hi).symm (PaperVerification.ToricGeometry.embed n v) =
      ι (b.equivFun.symm v) := by
  apply (realCoordinates b hi).injective
  simp only [LinearEquiv.apply_symm_apply, realCoordinates_lattice,
    LinearEquiv.apply_symm_apply]

private theorem cone_map_inverse {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (C : PointedCone ℝ V) :
    (C.map e.toLinearMap).map e.symm.toLinearMap = C := by
  rw [PointedCone.map_map]
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
  rw [he, PointedCone.map_id]

private theorem cone_map_injective {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) : Function.Injective (fun C : PointedCone ℝ V => C.map e.toLinearMap) := by
  intro C D h
  have h' := congrArg (fun K => K.map e.symm.toLinearMap) h
  simpa only [cone_map_inverse] using h'

private theorem cone_map_inf {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : V ≃ₗ[ℝ] W) (C D : PointedCone ℝ V) :
    (C ⊓ D).map e.toLinearMap = C.map e.toLinearMap ⊓ D.map e.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyD⟩, rfl⟩
    exact ⟨⟨y, hyC, rfl⟩, ⟨y, hyD, rfl⟩⟩
  · rintro ⟨⟨y, hy, hey⟩, ⟨z, hz, hez⟩⟩
    have hyz : y = z := e.injective (hey.trans hez.symm)
    exact ⟨y, ⟨hy, hyz.symm ▸ hz⟩, hey⟩

private theorem image_coordinates_roundtrip (S : Finset N) :
    (S.image b.equivFun).image b.equivFun.symm = S := by
  rw [Finset.image_image]
  have hf : (b.equivFun.symm : Lattice n → N) ∘ (b.equivFun : N → Lattice n) = id :=
    funext b.equivFun.symm_apply_apply
  rw [hf, Finset.image_id]

variable (F : SmoothCompleteFan n)

/-- The ordinary fan in the original integral lattice. Every cone is
the inverse real image of an actual cone of the coordinate fan. -/
def originalFan : Fan ι where
  lattice := hi
  cones := (fun C : PointedCone ℝ (Ambient n) =>
    C.map (realCoordinates b hi).symm.toLinearMap) ''
      (Unimodular.FanInterfaces.dictionaryToricFan F).cones
  finite_cones := (Unimodular.FanInterfaces.dictionaryToricFan F).finite_cones.image _
  isToricCone := by
    rintro D ⟨C, hC, rfl⟩
    exact ((Unimodular.FanInterfaces.dictionaryToricFan F).isToricCone hC).map
      (f := b.equivFun.symm.toAddMonoidHom)
      (fun v => realCoordinates_symm_lattice b hi v)
      (realCoordinates b hi).symm.injective
  mem_of_isFaceOf := by
    rintro D K ⟨C, hC, rfl⟩ hK
    have hk := hK.map (realCoordinates b hi).toLinearMap (realCoordinates b hi).injective
    change (K.map (realCoordinates b hi).toLinearMap).IsFaceOf
      ((C.map (realCoordinates b hi).symm.toLinearMap).map
        (realCoordinates b hi).toLinearMap) at hk
    have hback : (C.map (realCoordinates b hi).symm.toLinearMap).map
        (realCoordinates b hi).toLinearMap = C := by
      simpa only [LinearEquiv.symm_symm] using
        cone_map_inverse (realCoordinates b hi).symm C
    rw [hback] at hk
    exact ⟨K.map (realCoordinates b hi).toLinearMap,
      (Unimodular.FanInterfaces.dictionaryToricFan F).mem_of_isFaceOf hC hk,
      cone_map_inverse (realCoordinates b hi) K⟩
  inf_isFaceOf_left := by
    rintro C' D' ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    rw [← cone_map_inf]
    exact ((Unimodular.FanInterfaces.dictionaryToricFan F).inf_isFaceOf_left hC hD).map
      (realCoordinates b hi).symm.toLinearMap (realCoordinates b hi).symm.injective

/-- The comparison records both the integral lattice and every real cone. -/
def originalFanEquiv :
    FanEquiv (Unimodular.FanInterfaces.dictionaryToricFan F) (originalFan b hi F) where
  latticeEquiv := b.equivFun.symm.toAddEquiv
  realEquiv := (realCoordinates b hi).symm
  map_lattice v := realCoordinates_symm_lattice b hi v
  map_mem C := by
    constructor
    · rintro ⟨D, hD, he⟩
      exact (cone_map_injective (realCoordinates b hi).symm he) ▸ hD
    · intro hC
      exact ⟨C, hC, rfl⟩

theorem originalFan_complete : (originalFan b hi F).IsComplete :=
  (originalFanEquiv b hi F).isComplete_iff.mpr
    (Unimodular.FanInterfaces.dictionaryToricFan_complete F)

theorem originalFan_regular : (originalFan b hi F).IsRegular :=
  (originalFanEquiv b hi F).isRegular_iff.mpr
    (Unimodular.FanInterfaces.dictionaryToricFan_regular F)

theorem coordinateCone_inverse_image (s : Finset (Lattice n)) :
    (latticeRayCone s).map (realCoordinates b hi).symm.toLinearMap =
      latticeCone (ι := ι) (s.image b.equivFun.symm) := by
  rw [Unimodular.FanInterfaces.latticeRayCone_eq_hull_image]
  simp only [latticeCone, PointedCone.map, PointedCone.hull, Submodule.map_span,
    Finset.coe_image, Set.image_image]
  congr 1
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, realCoordinates_symm_lattice b hi v |>.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, realCoordinates_symm_lattice b hi v⟩

/-- The ordinary fan consists exactly of the cones used by the actual
original-lattice affine atlas; this is an equality of complete cone sets. -/
theorem originalFan_cones_eq_range :
    (originalFan b hi F).cones =
      Set.range (fun s : OriginalConeIndex b F => latticeCone (ι := ι) s.val) := by
  ext C
  constructor
  · rintro ⟨D, ⟨s, hs, rfl⟩, rfl⟩
    let t : F.ConeIndex := ⟨s, hs⟩
    obtain ⟨r, hr⟩ := coordinateIndex_surjective b F t
    have hrs : r.val.image b.equivFun = s := congrArg Subtype.val hr
    refine ⟨r, ?_⟩
    change latticeCone (ι := ι) r.val =
      (latticeRayCone s).map (realCoordinates b hi).symm.toLinearMap
    rw [coordinateCone_inverse_image, ← hrs, image_coordinates_roundtrip]
  · rintro ⟨s, rfl⟩
    refine ⟨latticeRayCone (s.val.image b.equivFun),
      ⟨s.val.image b.equivFun, s.property, rfl⟩, ?_⟩
    change (latticeRayCone (s.val.image b.equivFun)).map
      (realCoordinates b hi).symm.toLinearMap = latticeCone (ι := ι) s.val
    rw [coordinateCone_inverse_image, image_coordinates_roundtrip]

end PaperVerification.OriginalLatticeCharts

#print axioms PaperVerification.OriginalLatticeCharts.originalFanEquiv
#print axioms PaperVerification.OriginalLatticeCharts.originalFan_cones_eq_range
