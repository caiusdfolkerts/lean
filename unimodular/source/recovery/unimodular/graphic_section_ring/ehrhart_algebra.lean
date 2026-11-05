module

public import Recovery.Unimodular.GraphicSectionRing.CoordinateGeometry
public import Recovery.Unimodular.GraphicSectionRing.FilteredSectionAlgebra
public import Recovery.Unimodular.FlagKoszul.AlgebraTransport

/-!
# The actual Ehrhart algebra on original-polytope variables

The polynomial map sends the variable of x in P to the literal exponent
(1,x). Its surjectivity and its exact original toric kernel are proved.
The augmentation is verified on every actual homogeneous monomial.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise

namespace Unimodular.GraphicSectionRing

variable {n d : ℕ} (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
  (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C)

def ehrhartPointEquiv : LatticePoint P ≃ Point C where
  toFun a := ⟨e a.val, (RealCoordinates.cast_mem_coordinateBody e C a.val).mp (by
    simpa only [hP] using a.property)⟩
  invFun a := ⟨e.symm a.val, by
    rw [hP]
    apply (RealCoordinates.cast_mem_coordinateBody e C _).mpr
    simpa only [e.apply_symm_apply] using a.property⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)

/-- The actual degree-one exponent associated with an original lattice point. -/
def ehrhartDegreeOne (a : LatticePoint P) : ehrhartSemigroup P e C hP :=
  ⟨(1, a.val), Or.inr ⟨by change (0 : ℕ) < 1; exact Nat.zero_lt_succ 0,
    by simpa only [Nat.cast_one, one_smul] using a.property⟩⟩

@[simp] theorem sectionEhrhartIndex_degreeOne (a : LatticePoint P) :
    sectionEhrhartIndex P e C hP (degreeOnePoint (ehrhartPointEquiv P e C hP a)) =
      ehrhartDegreeOne P e C hP a := by
  apply Subtype.ext
  exact Prod.ext rfl (e.symm_apply_apply a.val)

variable (K : Type*)

section Ring
variable [CommRing K]

/-- The ordinary polynomial homomorphism on the original variables x in P. -/
def ehrhartPolynomialMap : MvPolynomial (LatticePoint P) K →ₐ[K] EhrhartAlgebra P e C hP K :=
  MvPolynomial.aeval (fun a => AddMonoidAlgebra.single (ehrhartDegreeOne P e C hP a) 1)

@[simp] theorem ehrhartPolynomialMap_X (a : LatticePoint P) :
    ehrhartPolynomialMap P e C hP K (MvPolynomial.X a) =
      AddMonoidAlgebra.single (ehrhartDegreeOne P e C hP a) 1 := by
  simp only [ehrhartPolynomialMap, MvPolynomial.aeval_X]

theorem sectionEhrhart_comp_map :
    (sectionEhrhartEquiv P e C hP K).toAlgHom.comp
      ((sectionMap C K).comp (MvPolynomial.renameEquiv K (ehrhartPointEquiv P e C hP)).toAlgHom) =
      ehrhartPolynomialMap P e C hP K := by
  apply MvPolynomial.algHom_ext
  intro a
  change sectionEhrhartEquiv P e C hP K
    (sectionMap C K ((MvPolynomial.renameEquiv K (ehrhartPointEquiv P e C hP))
      (MvPolynomial.X a))) = ehrhartPolynomialMap P e C hP K (MvPolynomial.X a)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, sectionMap_X,
    sectionEhrhartEquiv_single, sectionEhrhartIndex_degreeOne, ehrhartPolynomialMap_X]

/-- Genuine normal generation of the actual original-polytope Ehrhart algebra. -/
theorem ehrhartPolynomialMap_surjective : Function.Surjective (ehrhartPolynomialMap P e C hP K) := by
  rw [← sectionEhrhart_comp_map P e C hP K]
  exact (sectionEhrhartEquiv P e C hP K).surjective.comp
    ((sectionMap_surjective C K).comp (MvPolynomial.renameEquiv K (ehrhartPointEquiv P e C hP)).surjective)

def ehrhartAmbientMap : EhrhartAlgebra P e C hP K →ₐ[K] AddMonoidAlgebra K (ℕ × Lattice n) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (ehrhartSemigroup P e C hP).subtype

theorem ehrhartAmbientMap_injective : Function.Injective (ehrhartAmbientMap P e C hP K) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

theorem ehrhartAmbientMap_comp :
    (ehrhartAmbientMap P e C hP K).comp (ehrhartPolynomialMap P e C hP K) =
      toricMap (Subtype.val : LatticePoint P → Lattice n) K := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, ehrhartPolynomialMap_X, toricMap_X,
    ehrhartAmbientMap, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The kernel is exactly the original lattice-point relation ideal. -/
theorem ehrhartPolynomialMap_ker : RingHom.ker (ehrhartPolynomialMap P e C hP K).toRingHom =
    toricIdeal (Subtype.val : LatticePoint P → Lattice n) K := by
  ext f
  change ehrhartPolynomialMap P e C hP K f = 0 ↔ toricMap Subtype.val K f = 0
  constructor
  · intro h
    have hc := DFunLike.congr_fun (ehrhartAmbientMap_comp P e C hP K) f
    rw [AlgHom.comp_apply, h, map_zero] at hc
    exact hc.symm
  · intro h
    apply ehrhartAmbientMap_injective P e C hP K
    rw [map_zero]
    change ((ehrhartAmbientMap P e C hP K).comp (ehrhartPolynomialMap P e C hP K)) f = 0
    rw [ehrhartAmbientMap_comp, h]

/-- A proved equivalence with the quotient by the actual original toric ideal. -/
def ehrhartQuotientEquiv :
    (MvPolynomial (LatticePoint P) K ⧸ toricIdeal (Subtype.val : LatticePoint P → Lattice n) K) ≃ₐ[K]
      EhrhartAlgebra P e C hP K := by
  rw [← ehrhartPolynomialMap_ker P e C hP K]
  exact Ideal.quotientKerAlgEquivOfSurjective (ehrhartPolynomialMap_surjective P e C hP K)

/-- The ordinary homogeneous degree is the literal first coordinate. -/
def ehrhartInternalDegree : ehrhartSemigroup P e C hP →+ ℕ where
  toFun z := z.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem ehrhartInternalDegree_transport (z : sectionSemigroup C) :
    ehrhartInternalDegree P e C hP (sectionEhrhartIndex P e C hP z) = internalDegree C z := rfl

end Ring

section Field
variable [Field K]

/-- The transported augmentation is an actual algebra map; the following
formula proves it is precisely extraction of the degree-zero coefficient. -/
def ehrhartAugmentation : EhrhartAlgebra P e C hP K →ₐ[K] K :=
  FlagKoszul.AlgebraTransport.augmentation (sectionEhrhartEquiv P e C hP K)
    (sectionAugmentation C K)

@[simp] theorem ehrhartAugmentation_single (z : ehrhartSemigroup P e C hP) (a : K) :
    ehrhartAugmentation P e C hP K (AddMonoidAlgebra.single z a) =
      if z.val.1 = 0 then a else 0 := by
  change sectionAugmentation C K
    ((sectionEhrhartEquiv P e C hP K).symm (AddMonoidAlgebra.single z a)) = _
  rw [sectionEhrhartEquiv, AddMonoidAlgebra.domCongr_symm, AddMonoidAlgebra.domCongr_single,
    sectionAugmentation_single]
  rfl

end Field

#print axioms ehrhartPolynomialMap_surjective
#print axioms ehrhartPolynomialMap_ker
#print axioms ehrhartQuotientEquiv
#print axioms ehrhartAugmentation_single

end Unimodular.GraphicSectionRing

#check Unimodular.GraphicSectionRing.ehrhartPolynomialMap_ker
