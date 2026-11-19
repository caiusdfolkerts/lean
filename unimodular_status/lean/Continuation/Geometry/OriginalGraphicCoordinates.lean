module

public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Recovery.Unimodular.GraphicSectionRing.CoordinateGeometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Difference polytopes in an arbitrary original integral lattice

The real coordinate map is derived by scalar extension of the given integral
coordinate isomorphism. The original real set, its lattice points, and every
positive dilation are retained. No smoothness, reflexivity, nonempty interior,
or full-dimensionality hypothesis is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TauCeti.Toric
open scoped BigOperators Pointwise

universe u v

namespace Unimodular.GraphicSectionRing.OriginalLattice

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [AddCommGroup V] [Module ℝ V]

/-- Finite integral coordinates exist from the actual lattice hypothesis.
The coordinate isomorphism used in the graphic presentation is not an
additional assertion that a finite basis exists. -/
theorem integral_coordinates_exist {ι : N →+ V} (hi : IsIntegralLattice ι) :
    ∃ d : ℕ, Nonempty (N ≃ₗ[ℤ] Lattice d) := by
  letI : Module.Free ℤ N := hi.free
  letI : Module.Finite ℤ N := hi.finite
  exact ⟨Module.finrank ℤ N, ⟨(Module.finBasis ℤ N).equivFun⟩⟩

variable {d : ℕ} {ι : N →+ V} (hi : IsIntegralLattice ι)
    (e : N ≃ₗ[ℤ] Lattice d)

/-- The integral basis specified by the given coordinate isomorphism. -/
def coordinateBasis : Module.Basis (Fin d) ℤ N :=
  (Pi.basisFun ℤ (Fin d)).map e.symm

@[simp] theorem coordinateBasis_repr (x : N) (i : Fin d) :
    (coordinateBasis e).repr x i = e x i := by
  change (Pi.basisFun ℤ (Fin d)).repr (e x) i = e x i
  simp only [Pi.basisFun_repr]

/-- The actual real extension, obtained from the lattice scalar-extension
proof and the specified integral coordinate basis. -/
def realCoordinates : V ≃ₗ[ℝ] RealLattice d :=
  (hi.isBaseChange.basis (coordinateBasis e)).equivFun

@[simp] theorem realCoordinates_lattice (x : N) :
    realCoordinates hi e (ι x) = latticeCast (e x) := by
  ext i
  change (hi.isBaseChange.basis (coordinateBasis e)).repr (ι x) i =
    (e x i : ℝ)
  change (hi.isBaseChange.basis (coordinateBasis e)).repr (ι.toIntLinearMap x) i = _
  rw [hi.isBaseChange.basis_repr_comp_apply, coordinateBasis_repr]
  rw [algebraMap_int_eq]
  rfl

@[simp] theorem realCoordinates_symm_lattice (x : Lattice d) :
    (realCoordinates hi e).symm (latticeCast x) = ι (e.symm x) := by
  apply (realCoordinates hi e).injective
  simp only [LinearEquiv.apply_symm_apply, realCoordinates_lattice,
    LinearEquiv.apply_symm_apply]

/-- The literal preimage of the real difference-inequality body. -/
def coordinateBody (C : Set (Constraint d)) : Set V :=
  (realCoordinates hi e) ⁻¹' body C

@[simp] theorem lattice_mem_coordinateBody (C : Set (Constraint d)) (x : N) :
    ι x ∈ coordinateBody hi e C ↔ Satisfies C (e x) := by
  change realCoordinates hi e (ι x) ∈ body C ↔ _
  rw [realCoordinates_lattice, latticeCast_mem_body]

/-- Coordinates commute with every real dilation, including the empty-body
and degree-zero cases. No division or positivity premise is needed here. -/
theorem lattice_mem_dilate (C : Set (Constraint d)) (k : ℕ) (x : N) :
    ι x ∈ (k : ℝ) • coordinateBody hi e C ↔
      latticeCast (e x) ∈ (k : ℝ) • body C := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨realCoordinates hi e y, hy, ?_⟩
    have h := congrArg (realCoordinates hi e) hyx
    simpa only [map_smul, realCoordinates_lattice] using h
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(realCoordinates hi e).symm y, ?_, ?_⟩
    · change realCoordinates hi e ((realCoordinates hi e).symm y) ∈ body C
      simpa only [LinearEquiv.apply_symm_apply] using hy
    · apply (realCoordinates hi e).injective
      simpa only [map_smul, LinearEquiv.apply_symm_apply,
        realCoordinates_lattice] using hyx


/-- The existing standard-coordinate body's identity-coordinate case is the
same literal difference body. This joins the two real-set presentations. -/
theorem standard_coordinateBody_eq (C : Set (Constraint d)) :
    RealCoordinates.coordinateBody (LinearEquiv.refl ℤ (Lattice d)) C = body C := by
  have he : (RealCoordinates.equivalence (LinearEquiv.refl ℤ (Lattice d))).toLinearMap =
      LinearMap.id := by
    apply (Pi.basisFun ℝ (Fin d)).ext
    intro i
    change RealCoordinates.equivalence (LinearEquiv.refl ℤ (Lattice d))
      (Pi.basisFun ℝ (Fin d) i) = Pi.basisFun ℝ (Fin d) i
    simpa only [LinearEquiv.refl_apply, RealCoordinates.cast_basis] using
      RealCoordinates.equivalence_cast (LinearEquiv.refl ℤ (Lattice d))
        (Pi.basisFun ℤ (Fin d) i)
  ext x
  change RealCoordinates.equivalence (LinearEquiv.refl ℤ (Lattice d)) x ∈ body C ↔ x ∈ body C
  rw [show RealCoordinates.equivalence (LinearEquiv.refl ℤ (Lattice d)) x = x from
    LinearMap.congr_fun he x]

/-- Variables are the actual original lattice points, not coordinate labels. -/
abbrev LatticePoint (ι : N →+ V) (P : Set V) := {x : N // ι x ∈ P}

variable (C : Set (Constraint d)) (P : Set V)
    (hP : P = coordinateBody hi e C)

/-- The point-label equivalence is proved from the real-set presentation. -/
def pointEquiv : LatticePoint ι P ≃ GraphicSectionRing.Point C where
  toFun x := ⟨e x.val, (lattice_mem_coordinateBody hi e C x.val).mp (by
    simpa only [hP] using x.property)⟩
  invFun x := ⟨e.symm x.val, by
    rw [hP]
    apply (lattice_mem_coordinateBody hi e C _).mpr
    simpa only [e.apply_symm_apply] using x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)

@[simp] theorem pointEquiv_val (x : LatticePoint ι P) :
    (pointEquiv hi e C P hP x).val = e x.val := rfl

include hP in
/-- The actual image of the original polytope, not only its integral points. -/
theorem coordinate_image : realCoordinates hi e '' P = body C := by
  subst P
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨(realCoordinates hi e).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
    change realCoordinates hi e ((realCoordinates hi e).symm y) ∈ body C
    simpa only [LinearEquiv.apply_symm_apply] using hy

include hP in
/-- All positive integer-decomposition degrees on the original lattice.
The sum is an equality in N, not an equality after forgetting coordinates. -/
theorem integer_decomposition {k : ℕ} (hk : 0 < k) (x : N)
    (hx : ι x ∈ (k : ℝ) • P) :
    ∃ z : Fin k → N, (∀ i, ι (z i) ∈ P) ∧ ∑ i, z i = x := by
  obtain ⟨z, hz, hsum⟩ := GraphicSectionRing.integer_decomposition hk (e x)
    ((lattice_mem_dilate hi e C k x).mp (by simpa only [hP] using hx))
  refine ⟨fun i => e.symm (z i), ?_, ?_⟩
  · intro i
    rw [hP]
    apply (lattice_mem_coordinateBody hi e C _).mpr
    rw [e.apply_symm_apply]
    exact latticeCast_mem_body.mp (hz i)
  · rw [← map_sum, hsum, e.symm_apply_apply]

section Bounded

variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {j : N →+ W} (hj : IsIntegralLattice j)
    (Q : Set W) (hQ : Q = coordinateBody hj e C)

include hQ in
/-- The scalar extension is continuous because its dimension is derived
from the integral lattice. Boundedness is transported from the original set. -/
theorem body_bounded (hbounded : Bornology.IsBounded Q) :
    Bornology.IsBounded (body C) := by
  letI : FiniteDimensional ℝ W := hj.finiteDimensional
  let f := (realCoordinates hj e).toContinuousLinearEquiv
  have h := f.toContinuousLinearMap.lipschitzWith.isBounded_image hbounded
  change Bornology.IsBounded (realCoordinates hj e '' Q) at h
  rwa [coordinate_image hj e C Q hQ] at h

include hQ in
/-- No finite-point premise is imposed; boundedness proves it. -/
theorem coordinate_points_finite (hbounded : Bornology.IsBounded Q) :
    Finite (GraphicSectionRing.Point C) := by
  letI : Fintype (GraphicSectionRing.LatticePoint (body C)) :=
    (finite_lattice_points_of_bounded (body C)
      (body_bounded e C hj Q hQ hbounded)).fintype
  let f : GraphicSectionRing.Point C → GraphicSectionRing.LatticePoint (body C) :=
    fun x => ⟨x.val, latticeCast_mem_body.mpr x.property⟩
  exact Finite.of_injective f (fun x y h => Subtype.ext
    (congrArg (fun z : GraphicSectionRing.LatticePoint (body C) => z.val) h))

include hQ in
theorem lattice_points_finite (hbounded : Bornology.IsBounded Q) :
    Finite (LatticePoint j Q) := by
  letI : Finite (GraphicSectionRing.Point C) :=
    coordinate_points_finite e C hj Q hQ hbounded
  exact Finite.of_injective (pointEquiv hj e C Q hQ)
    (pointEquiv hj e C Q hQ).injective

end Bounded

#print axioms integral_coordinates_exist
#print axioms realCoordinates_lattice
#print axioms lattice_mem_dilate
#print axioms integer_decomposition
#print axioms lattice_points_finite

end Unimodular.GraphicSectionRing.OriginalLattice
