module

public import Continuation.Geometry.OriginalGraphicAlgebra
import all Continuation.Geometry.OriginalGraphicAlgebra

public import Mathlib.Algebra.Module.ULift
import all Mathlib.Algebra.Module.ULift

public import Continuation.Geometry.OriginalGraphicPolytope
public import Mathlib.Algebra.Field.ULift

/-!
# Original Ehrhart algebras over independently sized coefficient fields

The original lattice and the coefficient field have independent universes.
The ring remains literally `K[E(P)]`. Its scalar field is represented by the
canonically isomorphic `ULift K` in the ring's universe, so the existing
ordinary derived-Tor construction applies without changing the ring or its
exponents. The augmentation kernel and the original residue module are
identified explicitly. No concentration or acyclicity is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TauCeti.Toric CategoryTheory
open scoped BigOperators Pointwise MonomialOrder

universe u v w

namespace Unimodular.GraphicSectionRing.OriginalLattice.AllFields

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {ι : N →+ V} (hi : IsIntegralLattice ι)
    (e : N ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d)) (P : Set V)
    (hP : P = coordinateBody hi e C)
    (K : Type w) [Field K]

/-- Scalars act by their underlying original field element. -/
local instance coefficientFieldAlgebra : Algebra (ULift.{u} K) K :=
  ULift.algebra' K K

/-- The actual coefficient-field isomorphism, with no extension of scalars. -/
def coefficientDown : ULift.{u} K ≃ₐ[ULift.{u} K] K where
  __ := (ULift.ringEquiv : ULift.{u} K ≃+* K)
  commutes' _ := rfl

/-- Coefficient transport fixes every original Ehrhart exponent. -/
def coefficientEquiv :
    EhrhartAlgebra hi e C P hP (ULift.{u} K) ≃ₐ[ULift.{u} K]
      EhrhartAlgebra hi e C P hP K :=
  AddMonoidAlgebra.mapAlgEquiv (ULift.{u} K) (ehrhartSemigroup hi e C P hP)
    (coefficientDown K)

@[simp] theorem coefficientEquiv_single (z : ehrhartSemigroup hi e C P hP)
    (a : ULift.{u} K) :
    coefficientEquiv hi e C P hP K (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single z a.down := by
  change AddMonoidAlgebra.mapAlgHom (ehrhartSemigroup hi e C P hP)
    (coefficientDown K).toAlgHom (AddMonoidAlgebra.single z a) = _
  exact AddMonoidAlgebra.mapAlgHom_single (coefficientDown K).toAlgHom z a

/-- The source and target are now in the same universe. The target is the
unchanged original monoid algebra with coefficients in K. -/
def sectionEquiv :
    SectionAlgebra C (ULift.{u} K) ≃ₐ[ULift.{u} K] EhrhartAlgebra hi e C P hP K :=
  (sectionEhrhartEquiv hi e C P hP (ULift.{u} K)).trans
    (coefficientEquiv hi e C P hP K)

@[simp] theorem sectionEquiv_single (z : sectionSemigroup C) (a : ULift.{u} K) :
    sectionEquiv hi e C P hP K (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (sectionEhrhartIndex hi e C P hP z) a.down := by
  change coefficientEquiv hi e C P hP K
    (sectionEhrhartEquiv hi e C P hP (ULift.{u} K) (AddMonoidAlgebra.single z a)) = _
  rw [sectionEhrhartEquiv_single, coefficientEquiv_single]

@[simp] theorem sectionEquiv_symm_single (z : ehrhartSemigroup hi e C P hP) (a : K) :
    (sectionEquiv hi e C P hP K).symm (AddMonoidAlgebra.single z a) =
      AddMonoidAlgebra.single (semigroupEquiv hi e C P hP z) (ULift.up a) := by
  apply (sectionEquiv hi e C P hP K).injective
  rw [AlgEquiv.apply_symm_apply, sectionEquiv_single]
  change AddMonoidAlgebra.single z a =
    AddMonoidAlgebra.single
      ((semigroupEquiv hi e C P hP).symm ((semigroupEquiv hi e C P hP) z)) a
  rw [AddEquiv.symm_apply_apply]

/-- The independently defined ordinary K-valued degree-zero augmentation. -/
def originalAugmentation : EhrhartAlgebra hi e C P hP K →ₐ[K] K :=
  FlagKoszul.AlgebraTransport.augmentation (sectionEhrhartEquiv hi e C P hP K)
    (sectionAugmentation C K)

@[simp] theorem originalAugmentation_single (z : ehrhartSemigroup hi e C P hP) (a : K) :
    originalAugmentation hi e C P hP K (AddMonoidAlgebra.single z a) =
      if z.val.1 = 0 then a else 0 := by
  change sectionAugmentation C K
    ((sectionEhrhartEquiv hi e C P hP K).symm (AddMonoidAlgebra.single z a)) = _
  simp only [sectionEhrhartEquiv, AddMonoidAlgebra.domCongr_symm,
    AddMonoidAlgebra.domCongr_single, sectionAugmentation_single]
  rfl

/-- The augmentation of the unchanged ring into the canonical field copy. -/
def liftedAugmentation : EhrhartAlgebra hi e C P hP K →ₐ[ULift.{u} K] ULift.{u} K :=
  FlagKoszul.AlgebraTransport.augmentation (sectionEquiv hi e C P hP K)
    (sectionAugmentation C (ULift.{u} K))

@[simp] theorem liftedAugmentation_single (z : ehrhartSemigroup hi e C P hP) (a : K) :
    liftedAugmentation hi e C P hP K (AddMonoidAlgebra.single z a) =
      if z.val.1 = 0 then ULift.up a else 0 := by
  change sectionAugmentation C (ULift.{u} K)
    ((sectionEquiv hi e C P hP K).symm (AddMonoidAlgebra.single z a)) = _
  simp only [sectionEquiv_symm_single, sectionAugmentation_single]
  rfl

theorem augmentation_down_single (z : ehrhartSemigroup hi e C P hP) (a : K) :
    (liftedAugmentation hi e C P hP K (AddMonoidAlgebra.single z a)).down =
      originalAugmentation hi e C P hP K (AddMonoidAlgebra.single z a) := by
  rw [liftedAugmentation_single, originalAugmentation_single]
  split_ifs <;> rfl

/-- The lifted map is precisely the original augmentation followed by up. -/
theorem augmentation_down_hom :
    (ULift.ringEquiv : ULift.{u} K ≃+* K).toRingHom.comp
        (liftedAugmentation hi e C P hP K).toRingHom =
      (originalAugmentation hi e C P hP K).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    exact augmentation_down_single hi e C P hP K 0 a
  · intro z
    exact augmentation_down_single hi e C P hP K z 1

@[simp] theorem augmentation_down (x : EhrhartAlgebra hi e C P hP K) :
    (liftedAugmentation hi e C P hP K x).down =
      originalAugmentation hi e C P hP K x :=
  DFunLike.congr_fun (augmentation_down_hom hi e C P hP K) x

/-- The actual ideal acting trivially on the residue is unchanged. -/
theorem augmentation_kernel :
    RingHom.ker (liftedAugmentation hi e C P hP K).toRingHom =
      RingHom.ker (originalAugmentation hi e C P hP K).toRingHom := by
  ext x
  change liftedAugmentation hi e C P hP K x = 0 ↔
    originalAugmentation hi e C P hP K x = 0
  constructor
  · intro hx
    rw [← augmentation_down]
    exact congrArg ULift.down hx
  · intro hx
    apply ULift.down_injective
    change (liftedAugmentation hi e C P hP K x).down = 0
    rw [augmentation_down, hx]

/-- The original K-residue with its original augmentation action, placed
canonically in the universe of modules over the unchanged Ehrhart ring. -/
def originalResidueModule : ModuleCat.{max u w} (EhrhartAlgebra hi e C P hP K) := by
  letI : Module (EhrhartAlgebra hi e C P hP K) K :=
    Module.compHom K (originalAugmentation hi e C P hP K).toRingHom
  letI : Module (EhrhartAlgebra hi e C P hP K) (ULift.{u} K) := ULift.module'
  exact ModuleCat.of (EhrhartAlgebra hi e C P hP K) (ULift.{u} K)

/-- Actual module identification, not a renamed residue assumption. -/
def residueIso :
    PaperVerification.AugmentationCoinvariants.augmentationModule
        (liftedAugmentation hi e C P hP K) ≅
      originalResidueModule hi e C P hP K :=
  LinearEquiv.toModuleIso
    (show (PaperVerification.AugmentationCoinvariants.augmentationModule
      (liftedAugmentation hi e C P hP K)) ≃ₗ[EhrhartAlgebra hi e C P hP K]
      (originalResidueModule hi e C P hP K) from
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        apply ULift.down_injective
        change (liftedAugmentation hi e C P hP K a).down * x.down =
          originalAugmentation hi e C P hP K a * x.down
        rw [augmentation_down] })

@[simp] theorem residueIso_hom_apply
    (x : PaperVerification.AugmentationCoinvariants.augmentationModule
      (liftedAugmentation hi e C P hP K)) :
    (residueIso hi e C P hP K).hom x = x := rfl

/-- The genuine left-derived functor evaluated on the actual original
augmentation residue. Only its canonical universe representation is used. -/
def ordinaryTorOriginalResidueIso (r : ℕ) :
    PaperVerification.AugmentationCoinvariants.augmentationTor
        (liftedAugmentation hi e C P hP K) r ≅
      ((PaperVerification.AugmentationCoinvariants.functor
        (liftedAugmentation hi e C P hP K)).leftDerived r).obj
          (originalResidueModule hi e C P hP K) :=
  ((PaperVerification.AugmentationCoinvariants.functor
    (liftedAugmentation hi e C P hP K)).leftDerived r).mapIso
      (residueIso hi e C P hP K)

def homogeneousBasis :
    Module.Basis (Option (FlagKoszul.Positive (FlagModel.Relation C))) (ULift.{u} K)
      (EhrhartAlgebra hi e C P hP K) :=
  FlagKoszul.AlgebraTransport.basis (sectionEquiv hi e C P hP K)
    (FlagModel.basis C (ULift.{u} K))

@[simp] theorem homogeneousBasis_none : homogeneousBasis hi e C P hP K none = 1 :=
  FlagKoszul.AlgebraTransport.unit_transport (sectionEquiv hi e C P hP K)
    (FlagModel.basis C (ULift.{u} K)) (FlagModel.basis_none C (ULift.{u} K))

@[simp] theorem homogeneousBasis_some (z : FlagKoszul.Positive (FlagModel.Relation C)) :
    homogeneousBasis hi e C P hP K (some z) =
      AddMonoidAlgebra.single (sectionEhrhartIndex hi e C P hP (sectionDegree C z.val)) 1 := by
  change sectionEquiv hi e C P hP K (FlagModel.basis C (ULift.{u} K) (some z)) = _
  simp only [FlagModel.basis_some, sectionEquiv_single]
  rfl

/-- The grading is the original exponent's first coordinate. -/
theorem homogeneousBasis_degree (z : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartInternalDegree hi e C P hP
        (sectionEhrhartIndex hi e C P hP (sectionDegree C z.val)) =
      FlagKoszul.positiveDegree (FlagModel.Relation C) z := by
  rw [ehrhartInternalDegree_transport]
  exact internalDegree_sectionDegree C z.val

@[simp] theorem augmentation_basis (z : FlagKoszul.Positive (FlagModel.Relation C)) :
    liftedAugmentation hi e C P hP K (homogeneousBasis hi e C P hP K (some z)) = 0 :=
  FlagKoszul.AlgebraTransport.augmentation_transport (sectionEquiv hi e C P hP K)
    (sectionAugmentation C (ULift.{u} K)) (FlagModel.basis C (ULift.{u} K))
    (FlagModel.augmentation_basis C (ULift.{u} K)) z

theorem product_degree :
    ∀ x y z, PaperVerification.AugmentedAlgebraBasis.productCoefficients
      (homogeneousBasis hi e C P hP K) x y z ≠ 0 →
      FlagKoszul.positiveDegree (FlagModel.Relation C) z =
        FlagKoszul.positiveDegree (FlagModel.Relation C) x +
          FlagKoszul.positiveDegree (FlagModel.Relation C) y :=
  FlagKoszul.AlgebraTransport.productDegree_transport (sectionEquiv hi e C P hP K)
    (FlagModel.basis C (ULift.{u} K)) (FlagKoszul.positiveDegree (FlagModel.Relation C))
    (FlagModel.product_degree C (ULift.{u} K))

/-- Ordinary derived augmentation Tor of the unchanged original ring.
The coefficient-field and basis-index lifts reconcile universes only.
The preceding residue isomorphism and augmentation-kernel equality identify
the original residue action and its genuine left-derived coinvariants. -/
abbrev EhrhartIsKoszul : Prop :=
  PaperVerification.WeightedBar.HasDiagonalTor (liftedAugmentation hi e C P hP K)
    (FlagKoszul.BarReindex.basis
      (Equiv.ulift.symm : FlagKoszul.Positive (FlagModel.Relation C) ≃
        ULift.{max u w} (FlagKoszul.Positive (FlagModel.Relation C)))
      (homogeneousBasis hi e C P hP K))
    (FlagKoszul.BarReindex.unit_transport Equiv.ulift.symm (homogeneousBasis hi e C P hP K)
      (homogeneousBasis_none hi e C P hP K))
    (FlagKoszul.BarReindex.augmentation_transport Equiv.ulift.symm
      (liftedAugmentation hi e C P hP K) (homogeneousBasis hi e C P hP K)
      (augmentation_basis hi e C P hP K))
    (FlagKoszul.positiveDegree (FlagModel.Relation C) ∘ Equiv.ulift)
    (FlagKoszul.BarReindex.productDegree_transport Equiv.ulift.symm
      (homogeneousBasis hi e C P hP K) (FlagKoszul.positiveDegree (FlagModel.Relation C))
      (product_degree hi e C P hP K))

theorem ehrhartAlgebra_hasDiagonalTor (hbounded : Bornology.IsBounded P) :
    EhrhartIsKoszul hi e C P hP K := by
  letI : Finite (GraphicSectionRing.Point C) := coordinate_points_finite e C hi P hP hbounded
  letI : Fintype (GraphicSectionRing.Point C) := Fintype.ofFinite _
  exact FlagKoszul.AlgebraTransport.hasDiagonalTor_ulift
    (sectionEquiv hi e C P hP K) (sectionAugmentation C (ULift.{u} K))
    (FlagModel.basis C (ULift.{u} K)) (FlagModel.basis_none C (ULift.{u} K))
    (FlagModel.augmentation_basis C (ULift.{u} K))
    (FlagKoszul.positiveDegree (FlagModel.Relation C)) (FlagModel.product_degree C (ULift.{u} K))
    (FlagKoszul.positiveDegree_pos (FlagModel.Relation C))
    (Koszul.section_reduced_cycle_is_boundary C)

/-- Proposition 6.10 with independent universes for the original lattice
and every coefficient field. Original polynomial variables, coefficients,
Ehrhart exponents and all positive integer dilations remain unchanged. -/
theorem theorem_6_10_arbitrary_lattice (hbounded : Bornology.IsBounded P) :
    (∃ m : MonomialOrder.{u,u} (LatticePoint ι P),
      initialIdeal m (toricIdeal (Subtype.val : LatticePoint ι P → N) K) =
        quadraticMonomialIdeal (e ∘ (Subtype.val : LatticePoint ι P → N)) K ∧
      ∀ z ∈ forbiddenExponents (e ∘ (Subtype.val : LatticePoint ι P → N)),
        z.degree = 2 ∧ ∀ x, z x ≤ 1) ∧
    (∀ k : ℕ, 0 < k → ∀ x : N, ι x ∈ (k : ℝ) • P →
      ∃ z : Fin k → N, (∀ i, ι (z i) ∈ P) ∧ ∑ i, z i = x) ∧
    Function.Surjective (ehrhartPolynomialMap hi e C P hP K) ∧
    RingHom.ker (ehrhartPolynomialMap hi e C P hP K).toRingHom =
      toricIdeal (Subtype.val : LatticePoint ι P → N) K ∧
    EhrhartIsKoszul hi e C P hP K := by
  refine ⟨squarefree_quadratic_initial_ideal hi e C P hP hbounded K, ?_,
    ehrhartPolynomialMap_surjective hi e C P hP K,
    ehrhartPolynomialMap_ker hi e C P hP K,
    ehrhartAlgebra_hasDiagonalTor hi e C P hP K hbounded⟩
  intro k hk x hx
  exact integer_decomposition hi e C P hP hk x hx

#print axioms coefficientEquiv_single
#print axioms sectionEquiv_single
#print axioms augmentation_down_hom
#print axioms augmentation_kernel
#print axioms residueIso
#print axioms ordinaryTorOriginalResidueIso
#print axioms homogeneousBasis_degree
#print axioms ehrhartAlgebra_hasDiagonalTor
#print axioms theorem_6_10_arbitrary_lattice

end Unimodular.GraphicSectionRing.OriginalLattice.AllFields
