module

public import Recovery.Unimodular.GraphicSectionRing.RealCoordinates
public import Recovery.Unimodular.GraphicSectionRing.SectionAlgebra
public import Recovery.Unimodular.GraphicSectionRing.PolytopeEndpoints

/-!
# The genuine section semigroup in the original lattice coordinates

The degree is retained and only the lattice exponent is changed by the given
integral equivalence. The equivalence of actual monoid algebras, the map from
original lattice-point variables, and its original toric kernel are all proved.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.GraphicSectionRing

variable {n d : ℕ}

/-- Actual scaled inequalities in the original exponent lattice. -/
def coordinateSemigroup (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d)) :
    AddSubmonoid (ℕ × Lattice n) :=
  (sectionSemigroup C).comap (degreeMap e.toAddMonoidHom)

theorem mem_coordinateSemigroup (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (z : ℕ × Lattice n) : z ∈ coordinateSemigroup e C ↔
      (z.1 = 0 → z.2 = 0) ∧
      ∀ c ∈ C, difference (e z.2) c.left c.right ≤ (z.1 : ℤ) * c.bound := by
  change ((z.1 = 0 → e z.2 = 0) ∧ _) ↔ _
  constructor
  · intro h
    refine ⟨fun hz => e.injective ?_, h.2⟩
    rw [h.1 hz, map_zero]
  · intro h
    refine ⟨fun hz => ?_, h.2⟩
    rw [h.1 hz, map_zero]

theorem degreeMap_inverse (e : Lattice n ≃ₗ[ℤ] Lattice d) (z : ℕ × Lattice d) :
    degreeMap e.toAddMonoidHom (degreeMap e.symm.toAddMonoidHom z) = z :=
  Prod.ext rfl (e.apply_symm_apply z.2)

/-- The exact degree-preserving equivalence of the two actual exponent semigroups. -/
def coordinateSemigroupEquiv (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d)) :
    coordinateSemigroup e C ≃+ sectionSemigroup C where
  toFun z := ⟨degreeMap e.toAddMonoidHom z.val, z.property⟩
  invFun z := ⟨degreeMap e.symm.toAddMonoidHom z.val, by
    change degreeMap e.toAddMonoidHom (degreeMap e.symm.toAddMonoidHom z.val) ∈ sectionSemigroup C
    rw [degreeMap_inverse]
    exact z.property⟩
  left_inv z := Subtype.ext (degreeMap_inverse e.symm z.val)
  right_inv z := Subtype.ext (degreeMap_inverse e z.val)
  map_add' x y := Subtype.ext ((degreeMap e.toAddMonoidHom).map_add x.val y.val)

@[simp] theorem coordinateSemigroupEquiv_val (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (z : coordinateSemigroup e C) :
    (coordinateSemigroupEquiv e C z).val = (z.val.1, e z.val.2) := rfl

@[simp] theorem coordinateSemigroupEquiv_degree (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (z : coordinateSemigroup e C) :
    (coordinateSemigroupEquiv e C z).val.1 = z.val.1 := rfl

abbrev CoordinateAlgebra (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (K : Type*) [CommSemiring K] := AddMonoidAlgebra K (coordinateSemigroup e C)

def coordinateAlgebraEquiv (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (K : Type*) [CommSemiring K] : CoordinateAlgebra e C K ≃ₐ[K] SectionAlgebra C K :=
  AddMonoidAlgebra.domCongr K K (coordinateSemigroupEquiv e C)

/-- The variables are the actual lattice points of the original real polytope. -/
def coordinatePointEquiv (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d)) :
    LatticePoint (RealCoordinates.coordinateBody e C) ≃ Point C where
  toFun a := ⟨e a.val, (RealCoordinates.cast_mem_coordinateBody e C a.val).mp a.property⟩
  invFun a := ⟨e.symm a.val, (RealCoordinates.cast_mem_coordinateBody e C _).mpr (by
    simpa only [e.apply_symm_apply] using a.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)

def coordinateDegreeOne (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (a : LatticePoint (RealCoordinates.coordinateBody e C)) : coordinateSemigroup e C :=
  ⟨(1, a.val), (degreeOnePoint (coordinatePointEquiv e C a)).property⟩

@[simp] theorem coordinateSemigroupEquiv_degreeOne (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (a : LatticePoint (RealCoordinates.coordinateBody e C)) :
    coordinateSemigroupEquiv e C (coordinateDegreeOne e C a) =
      degreeOnePoint (coordinatePointEquiv e C a) := rfl

/-- The ordinary polynomial map on the original variables. -/
def coordinateSectionMap (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (K : Type*) [CommSemiring K] :
    MvPolynomial (LatticePoint (RealCoordinates.coordinateBody e C)) K →ₐ[K]
      CoordinateAlgebra e C K :=
  (coordinateAlgebraEquiv e C K).symm.toAlgHom.comp
    ((sectionMap C K).comp (MvPolynomial.renameEquiv K (coordinatePointEquiv e C)).toAlgHom)

@[simp] theorem coordinateSectionMap_X (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (K : Type*) [CommSemiring K]
    (a : LatticePoint (RealCoordinates.coordinateBody e C)) :
    coordinateSectionMap e C K (MvPolynomial.X a) =
      AddMonoidAlgebra.single (coordinateDegreeOne e C a) 1 := by
  apply (coordinateAlgebraEquiv e C K).injective
  change coordinateAlgebraEquiv e C K
    ((coordinateAlgebraEquiv e C K).symm
      (sectionMap C K ((MvPolynomial.renameEquiv K (coordinatePointEquiv e C)) (MvPolynomial.X a)))) = _
  rw [AlgEquiv.apply_symm_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, sectionMap_X]
  exact (AddMonoidAlgebra.domCongr_single (coordinateSemigroupEquiv e C)
    (coordinateDegreeOne e C a) (1 : K)).symm

/-- Every original section monomial is generated by original degree-one lattice points. -/
theorem coordinateSectionMap_surjective (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (K : Type*) [CommSemiring K] :
    Function.Surjective (coordinateSectionMap e C K) := by
  intro f
  obtain ⟨g, hg⟩ := sectionMap_surjective C K (coordinateAlgebraEquiv e C K f)
  refine ⟨(MvPolynomial.renameEquiv K (coordinatePointEquiv e C)).symm g, ?_⟩
  change (coordinateAlgebraEquiv e C K).symm
    (sectionMap C K ((MvPolynomial.renameEquiv K (coordinatePointEquiv e C))
      ((MvPolynomial.renameEquiv K (coordinatePointEquiv e C)).symm g))) = f
  rw [AlgEquiv.apply_symm_apply, hg, AlgEquiv.symm_apply_apply]

def coordinateAmbientMap (e : Lattice n ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d))
    (K : Type*) [CommSemiring K] :
    CoordinateAlgebra e C K →ₐ[K] AddMonoidAlgebra K (ℕ × Lattice n) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (coordinateSemigroup e C).subtype

theorem coordinateAmbientMap_injective (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (K : Type*) [CommSemiring K] :
    Function.Injective (coordinateAmbientMap e C K) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

theorem coordinateAmbientMap_comp (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (K : Type*) [CommSemiring K] :
    (coordinateAmbientMap e C K).comp (coordinateSectionMap e C K) =
      toricMap (Subtype.val : LatticePoint (RealCoordinates.coordinateBody e C) → Lattice n) K := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, coordinateSectionMap_X, toricMap_X,
    coordinateAmbientMap, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The kernel is the actual toric ideal on the original lattice variables. -/
theorem coordinateSectionMap_ker (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (K : Type*) [CommSemiring K] :
    RingHom.ker (coordinateSectionMap e C K).toRingHom =
      toricIdeal (Subtype.val : LatticePoint (RealCoordinates.coordinateBody e C) → Lattice n) K := by
  ext f
  change coordinateSectionMap e C K f = 0 ↔ toricMap Subtype.val K f = 0
  constructor
  · intro h
    have hc := DFunLike.congr_fun (coordinateAmbientMap_comp e C K) f
    rw [AlgHom.comp_apply, h, map_zero] at hc
    exact hc.symm
  · intro h
    apply coordinateAmbientMap_injective e C K
    rw [map_zero]
    change ((coordinateAmbientMap e C K).comp (coordinateSectionMap e C K)) f = 0
    rw [coordinateAmbientMap_comp, h]

/-- A proved quotient presentation of the literal original-lattice section algebra. -/
def coordinateQuotientEquiv (e : Lattice n ≃ₗ[ℤ] Lattice d)
    (C : Set (Constraint d)) (K : Type*) [CommRing K] :
    (MvPolynomial (LatticePoint (RealCoordinates.coordinateBody e C)) K ⧸
      toricIdeal (Subtype.val : LatticePoint (RealCoordinates.coordinateBody e C) → Lattice n) K) ≃ₐ[K]
        CoordinateAlgebra e C K := by
  rw [← coordinateSectionMap_ker e C K]
  exact Ideal.quotientKerAlgEquivOfSurjective (coordinateSectionMap_surjective e C K)

#print axioms coordinateSemigroupEquiv
#print axioms coordinateAlgebraEquiv
#print axioms coordinateSectionMap_surjective
#print axioms coordinateSectionMap_ker
#print axioms coordinateQuotientEquiv

end Unimodular.GraphicSectionRing

#check Unimodular.GraphicSectionRing.coordinateQuotientEquiv
