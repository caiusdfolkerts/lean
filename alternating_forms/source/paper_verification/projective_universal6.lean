module

public import paper_verification.ambient_generic1
import all paper_verification.ambient_generic1
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Logic.Equiv.Option
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.UnitPivotKernel -/


/-!
# The kernel of a row with a unit pivot

This is the coordinate calculation for the kernel of the universal line
quotient on a projective chart. The distinguished coordinate is `none`.
All other coordinates are retained, while the pivot coordinate is their
negative weighted sum. The construction works over every commutative ring.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.UnitPivotKernel

variable (R : Type*) [CommRing R] (I : Type*) [Fintype I]

/-- A finite row as a linear map on coordinate vectors. -/
def row (a : Option I → R) : (Option I → R) →ₗ[R] R where
  toFun v := ∑ i, a i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_left_comm (a i) r (v i)

@[simp]
lemma row_apply (a : Option I → R) (v : Option I → R) :
    row R I a v = a none * v none + ∑ i : I, a (some i) * v (some i) := by
  simp only [row, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_option]

/-- The literal kernel is freely parametrized by the coordinates other
than the pivot, whenever the pivot coefficient equals one. -/
def kernelEquiv (a : Option I → R) (ha : a none = 1) :
    (row R I a).ker ≃ₗ[R] (I → R) where
  toFun v i := v.val (some i)
  invFun w :=
    ⟨fun i => i.elim (-(∑ j : I, a (some j) * w j)) w, by
      change row R I a _ = 0
      simp [row_apply, ha]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | some i => rfl
    | none =>
        have hv : v.val none + ∑ i : I, a (some i) * v.val (some i) = 0 := by
          simpa only [LinearMap.mem_ker, row_apply, ha, one_mul] using v.property
        exact (eq_neg_iff_add_eq_zero.mpr hv).symm
  right_inv w := rfl
  map_add' v w := rfl
  map_smul' r v := rfl

@[simp]
lemma kernelEquiv_apply (a : Option I → R) (ha : a none = 1)
    (v : (row R I a).ker) (i : I) : kernelEquiv R I a ha v i = v.val (some i) := rfl

@[simp]
lemma kernelEquiv_symm_some (a : Option I → R) (ha : a none = 1)
    (w : I → R) (i : I) : ((kernelEquiv R I a ha).symm w).val (some i) = w i := rfl

@[simp]
lemma kernelEquiv_symm_none (a : Option I → R) (ha : a none = 1)
    (w : I → R) : ((kernelEquiv R I a ha).symm w).val none =
      -(∑ i : I, a (some i) * w i) := rfl

/-- The same coordinate projection is bijective in any linearly equivalent
presentation of the kernel. This form applies directly to maps on sections
of actual module sheaves. -/
theorem kernel_projection_bijective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e : M ≃ₗ[R] (Option I → R))
    (a : Option I → R) (ha : a none = 1)
    (h : ∀ x, f x = 0 ↔ row R I a (e x) = 0) :
    Function.Bijective (fun x : f.ker => fun i => e x.val (some i)) := by
  let toRow : f.ker → (row R I a).ker := fun x =>
    ⟨e x.val, (h x.val).mp (LinearMap.mem_ker.mp x.property)⟩
  have htoRow : Function.Bijective toRow := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hxy)
    · intro v
      let x : f.ker := ⟨e.symm v.val, (h (e.symm v.val)).mpr (by
        rw [e.apply_symm_apply]
        exact LinearMap.mem_ker.mp v.property)⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply v.val
  exact (kernelEquiv R I a ha).bijective.comp htoRow

end PaperVerification.UnitPivotKernel
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.UnitPivotKernel"

section ComponentSource_1
/- Original module: PaperVerification.SheafUnitPivotKernel -/


/-!
# Local frames for the kernel of a line quotient

The morphism is the genuine morphism from a finite power of the structure
sheaf specified by its sections. On an open where its distinguished section
trivializes the target, its actual categorical kernel is a free module sheaf
on the remaining coordinates. The frame morphism is coordinate projection,
so its naturality is inherited from the original sheaf morphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped BigOperators

namespace PaperVerification.SheafUnitPivotKernel

universe u
variable {X : Scheme.{u}} (M : X.Modules) {I : Type u} [Fintype I]
  (s : Option I → M.sections)

/-- Retain the coordinates other than the distinguished coordinate. -/
def projection : kernel (SheafCoordinateMorphisms.fromSections M s) ⟶
    SheafModulePowers.structurePower X I :=
  kernel.ι (SheafCoordinateMorphisms.fromSections M s) ≫
    SheafModulePowers.reindex (SheafOfModules.unit X.ringCatSheaf)
      (Option I) I Option.some

theorem projection_coordinate (i : I) :
    projection M s ≫ Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i =
      kernel.ι (SheafCoordinateMorphisms.fromSections M s) ≫
        Pi.π (fun _ : Option I => SheafOfModules.unit X.ringCatSheaf) (some i) := by
  rw [projection, Category.assoc, SheafModulePowers.reindex_projection]

/-- Local coordinates turn the original sheaf morphism into a literal
one-row matrix, with the chosen section giving its unit pivot. -/
theorem map_coordinates (V : X.Opens)
    (e : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V))
    (x : (SheafModulePowers.structurePower X (Option I)).val.obj (op V)) :
    (SheafCoordinateMorphisms.fromSections M s).val.app (op V) x =
      e (UnitPivotKernel.row Γ(X, V) I
        (fun i => e.symm ((s i).eval (op V)))
        (SheafModulePowers.sectionsEquiv (SheafOfModules.unit X.ringCatSheaf)
          (Option I) V x)) := by
  rw [SheafCoordinateMorphisms.fromSections_apply]
  have h := SheafCoordinateMorphisms.sum_smul_eq_frame e
    (SheafModulePowers.sectionsEquiv (SheafOfModules.unit X.ringCatSheaf)
      (Option I) V x)
    (fun i => e.symm ((s i).eval (op V))) (fun i => (s i).eval (op V))
    (fun i => e.apply_symm_apply _)
  refine h.trans (congrArg e ?_)
  change (∑ i : Option I, (fun (c d : Γ(X, V)) => c * d)
      (SheafModulePowers.sectionsEquiv (SheafOfModules.unit X.ringCatSheaf)
        (Option I) V x i) (e.symm ((s i).eval (op V)))) =
    ∑ i : Option I, (fun (c d : Γ(X, V)) => c * d)
      (e.symm ((s i).eval (op V)))
      (SheafModulePowers.sectionsEquiv (SheafOfModules.unit X.ringCatSheaf)
        (Option I) V x i)
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- On sections, the actual kernel projection is a bijection whenever the
distinguished section is a basis of the target line. -/
theorem projection_bijective (V : X.Opens)
    (e : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V))
    (he : e 1 = (s none).eval (op V)) :
    Function.Bijective ((projection M s).val.app (op V)) := by
  letI : CommRing (X.ringCatSheaf.obj.obj (op V)) :=
    inferInstanceAs (CommRing Γ(X, V))
  let eA := SheafModulePowers.sectionsEquiv (SheafOfModules.unit X.ringCatSheaf)
    (Option I) V
  let eB := SheafModulePowers.sectionsEquiv (SheafOfModules.unit X.ringCatSheaf) I V
  let eK := SheafModuleKernels.sectionsEquiv
    (SheafCoordinateMorphisms.fromSections M s) V
  let f : (SheafModulePowers.structurePower X (Option I)).val.obj (op V) →ₗ[Γ(X, V)]
      M.val.obj (op V) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map
      (SheafCoordinateMorphisms.fromSections M s)).hom
  let a : Option I → Γ(X, V) := fun i => e.symm ((s i).eval (op V))
  have ha : a none = 1 := by
    change e.symm ((s none).eval (op V)) = 1
    rw [← he, e.symm_apply_apply]
  have hz (x) : f x = 0 ↔ UnitPivotKernel.row Γ(X, V) I a (eA x) = 0 := by
    change (SheafCoordinateMorphisms.fromSections M s).val.app (op V) x = 0 ↔ _
    rw [map_coordinates M s V e x]
    exact e.map_eq_zero_iff
  have hP := UnitPivotKernel.kernel_projection_bijective Γ(X, V) I f eA a ha hz
  have hc (x) : eB ((projection M s).val.app (op V) x) =
      fun i => eA (eK x).val (some i) := by
    funext i
    have hB := SheafModulePowers.sectionsEquiv_apply
      (SheafOfModules.unit X.ringCatSheaf) I V ((projection M s).val.app (op V) x) i
    have hProjection := congrArg
      (fun g : kernel (SheafCoordinateMorphisms.fromSections M s) ⟶
          SheafOfModules.unit X.ringCatSheaf => g.val.app (op V) x)
      (projection_coordinate M s i)
    have hA := SheafModulePowers.sectionsEquiv_apply
      (SheafOfModules.unit X.ringCatSheaf) (Option I) V (eK x).val (some i)
    have hK := congrArg
      (fun z : (SheafModulePowers.structurePower X (Option I)).val.obj (op V) =>
        (Pi.π (fun _ : Option I => SheafOfModules.unit X.ringCatSheaf) (some i)).val.app
          (op V) z)
      (SheafModuleKernels.sectionsEquiv_coe
        (SheafCoordinateMorphisms.fromSections M s) V x)
    exact hB.trans (hProjection.trans (hA.trans hK).symm)
  have hb : Function.Bijective (fun x => eB ((projection M s).val.app (op V) x)) := by
    have hfun : (fun x => eB ((projection M s).val.app (op V) x)) =
        (fun x => fun i => eA (eK x).val (some i)) := funext hc
    rw [hfun]
    exact hP.comp eK.bijective
  constructor
  · intro x y hxy
    exact hb.injective (congrArg eB hxy)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (eB y)
    exact ⟨x, eB.injective hx⟩

/-- The kernel is actually trivial on an open where the pivot section
trivializes the target. No separate compatibility hypothesis on the section
coordinates is needed: the frame is the restriction of `projection`. -/
def frameIso (U : X.Opens)
    (e : ∀ (V : X.Opens), V ≤ U → Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V))
    (he : ∀ (V : X.Opens) (hV : V ≤ U), e V hV 1 = (s none).eval (op V)) :
    (kernel (SheafCoordinateMorphisms.fromSections M s)).over U ≅
      (SheafModulePowers.structurePower X I).over U :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective
        (((projection M s).over U).val.app V).hom
        (projection_bijective M s V.unop.left (e V.unop.left V.unop.hom.le)
          (he V.unop.left V.unop.hom.le))).toModuleIso)
      (fun _ _ f => ((projection M s).over U).val.naturality f)

end PaperVerification.SheafUnitPivotKernel
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SheafUnitPivotKernel"

section ComponentSource_2
/- Original module: PaperVerification.SheafFiniteCoordinates -/


/-!
# Coproduct and product coordinates for finite free sheaves

The canonical map from the free sheaf (defined as a coproduct) to the finite
power of the structure sheaf carries a basis vector to the same coordinate
vector. A section-defined morphism is unchanged by this comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace PaperVerification.SheafFiniteCoordinates

universe u
variable {X : AlgebraicGeometry.Scheme.{u}} {I : Type u} [Fintype I]

/-- The actual coordinate-vector inclusion into the product sheaf. -/
def basisInclusion (i : I) : SheafOfModules.unit X.ringCatSheaf ⟶
    SheafModulePowers.structurePower X I := by
  classical
  exact Pi.lift (fun j => if i = j then 𝟙 _ else 0)

/-- The coproduct universal property gives the comparison with the product. -/
def freeToPower : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
    SheafModulePowers.structurePower X I :=
  Sigma.desc basisInclusion

theorem basisInclusion_fromSections (M : X.Modules) (s : I → M.sections) (i : I) :
    basisInclusion i ≫ SheafCoordinateMorphisms.fromSections M s =
      (SheafOfModules.unitHomEquiv M).symm (s i) := by
  classical
  simp only [SheafCoordinateMorphisms.fromSections, Preadditive.comp_sum,
    ← Category.assoc]
  have hb (j : I) : basisInclusion (X := X) i ≫
      Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) j =
        (if i = j then 𝟙 _ else 0) := Pi.lift_comp_π _ j
  rw [Finset.sum_eq_single i]
  · exact (congrArg (fun q => q ≫ (SheafOfModules.unitHomEquiv M).symm (s i))
      (hb i)).trans (by simp)
  · intro j hj hji
    exact (congrArg (fun q => q ≫ (SheafOfModules.unitHomEquiv M).symm (s j))
      (hb j)).trans (by simp [Ne.symm hji])
  · simp

/-- Both universal descriptions evaluate the same actual family of sections. -/
theorem freeToPower_fromSections (M : X.Modules) (s : I → M.sections) :
    freeToPower ≫ SheafCoordinateMorphisms.fromSections M s =
      (SheafOfModules.freeHomEquiv M).symm s := by
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  change (SheafOfModules.unitHomEquiv M)
      (SheafOfModules.ιFree i ≫ (freeToPower ≫
        SheafCoordinateMorphisms.fromSections M s)) = _
  rw [← Category.assoc]
  change (SheafOfModules.unitHomEquiv M)
      ((Sigma.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        Sigma.desc basisInclusion) ≫ SheafCoordinateMorphisms.fromSections M s) = _
  rw [Sigma.ι_desc, basisInclusion_fromSections]
  simp

end PaperVerification.SheafFiniteCoordinates
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SheafFiniteCoordinates"

section ComponentSource_3
/- Original module: PaperVerification.ProjectiveUniversalQuotient -/


/-!
# The universal quotient on an actual projective spectrum

Degree-one homogeneous elements give genuine sections of the original
twisting sheaf. If their basic opens cover the projective spectrum, the
associated map from a free module sheaf onto `O(1)` is an epimorphism.
The proof uses local chart generators and sheaf separation. In particular,
it constructs the universal quotient on polynomial projective space over
any commutative ring, with every rank allowed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace PaperVerification.ProjectiveUniversalQuotient

variable {A σ I : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The compatible family of sections represented by `a/1`. -/
def homogeneousSection (a : 𝒜 1) : (Proj.twistingSheaf 𝒜 (1 : ℤ)).sections :=
  PresheafOfModules.sectionsMk
    (fun U => Proj.toTwistingSheaf 𝒜 (n := (1 : ℤ)) rfl U.unop a)
    (fun _ _ _ => rfl)

/-- Evaluation of degree-one homogeneous generators, as a morphism of
actual sheaves of modules on `Proj`. -/
def quotientMap (a : I → 𝒜 1) :
    SheafOfModules.free (R := (Proj 𝒜).ringCatSheaf) I ⟶
      Proj.twistingSheaf 𝒜 (1 : ℤ) :=
  (SheafOfModules.freeHomEquiv _).symm (fun i => homogeneousSection (a i))

lemma quotientMap_freeSection (a : I → 𝒜 1) (i : I) (U : (Proj 𝒜).Opens) :
    Scheme.Modules.Hom.app (X := Proj 𝒜) (quotientMap a) U
        ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op U)) =
      Proj.toTwistingSheaf 𝒜 (n := (1 : ℤ)) rfl U (a i) := by
  exact congrArg (fun s : (Proj.twistingSheaf 𝒜 (1 : ℤ)).sections => s.val (op U))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i => homogeneousSection (a i)) i)

lemma homogeneousSection_eq_chartGenerator (a : 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 (a : A)) :
    Proj.toTwistingSheaf 𝒜 (n := (1 : ℤ)) rfl U a =
      Proj.twistingSheaf.chartGenerator 1 (a : A) a.property U hU := by
  apply Proj.twistingSheaf.ext
  intro x
  simp only [Proj.toTwistingSheaf_apply_apply, Proj.twistingSheaf.chartGenerator_apply]
  congr 1 <;> first | rfl | (apply Subtype.ext; simp) | simp

/-- A covering family of degree-one coordinates generates the actual
twisting sheaf in degree one. -/
theorem quotientMap_epi (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) : Epi (quotientMap a) := by
  constructor
  intro N f g hfg
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  let F : TopCat.Sheaf AddCommGrpCat (Proj 𝒜) := ⟨N.val.presheaf, N.isSheaf⟩
  let W : I → (Proj 𝒜).Opens := fun i => U ⊓ Proj.basicOpen 𝒜 (a i : A)
  refine F.eq_of_locally_eq' W U (fun i => homOfLE inf_le_left) ?_ _ _ ?_
  · change U ≤ ⨆ i, U ⊓ Proj.basicOpen 𝒜 (a i : A)
    rw [← inf_iSup_eq, hcover, inf_top_eq]
  · intro i
    let j : W i ⟶ U := homOfLE inf_le_left
    have hi : (Scheme.Modules.Hom.app (X := Proj 𝒜) f (W i)) (Proj.toTwistingSheaf 𝒜 rfl (W i) (a i)) =
        (Scheme.Modules.Hom.app (X := Proj 𝒜) g (W i)) (Proj.toTwistingSheaf 𝒜 rfl (W i) (a i)) := by
      have h := congrArg (fun q => Scheme.Modules.Hom.app (X := Proj 𝒜) q (W i)
        ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op (W i)))) hfg
      change Scheme.Modules.Hom.app (X := Proj 𝒜) f (W i)
          (Scheme.Modules.Hom.app (X := Proj 𝒜) (quotientMap a) (W i)
            ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op (W i)))) =
        Scheme.Modules.Hom.app (X := Proj 𝒜) g (W i)
          (Scheme.Modules.Hom.app (X := Proj 𝒜) (quotientMap a) (W i)
            ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op (W i)))) at h
      erw [quotientMap_freeSection] at h
      exact h
    erw [homogeneousSection_eq_chartGenerator (a i) (W i) inf_le_right] at hi
    obtain ⟨r, hr⟩ :=
      (Proj.twistingSheaf.chartSectionsLinearEquiv 1 (a i : A) (a i).property
        (W i) inf_le_right).surjective
          ((Proj.twistingSheaf 𝒜 (1 : ℤ)).presheaf.map j.op s)
    change N.val.presheaf.map j.op (Scheme.Modules.Hom.app (X := Proj 𝒜) f U s) = N.val.presheaf.map j.op (Scheme.Modules.Hom.app (X := Proj 𝒜) g U s)
    erw [← ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf (X := Proj 𝒜) f).naturality j.op) s,
      ← ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf (X := Proj 𝒜) g).naturality j.op) s]
    change Scheme.Modules.Hom.app (X := Proj 𝒜) f (W i) ((Proj.twistingSheaf 𝒜 (1 : ℤ)).presheaf.map j.op s) =
      Scheme.Modules.Hom.app (X := Proj 𝒜) g (W i) ((Proj.twistingSheaf 𝒜 (1 : ℤ)).presheaf.map j.op s)
    erw [← hr, Proj.twistingSheaf.chartSectionsLinearEquiv_apply,
      Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hi]

section FiniteCoordinates

variable [Fintype I]

/-- The same universal quotient, expressed on the actual finite product
`O^I` used by the kernel and local-frame APIs. -/
def powerQuotient (a : I → 𝒜 1) :
    SheafModulePowers.structurePower (Proj 𝒜) I ⟶ Proj.twistingSheaf 𝒜 (1 : ℤ) :=
  SheafCoordinateMorphisms.fromSections _ (fun i => homogeneousSection (a i))

theorem powerQuotient_epi (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) : Epi (powerQuotient a) := by
  haveI := quotientMap_epi a hcover
  haveI : Epi (SheafFiniteCoordinates.freeToPower ≫ powerQuotient a) := by
    rw [powerQuotient, SheafFiniteCoordinates.freeToPower_fromSections]
    exact inferInstanceAs (Epi (quotientMap a))
  exact epi_of_epi SheafFiniteCoordinates.freeToPower (powerQuotient a)

/-- The original universal quotient has a free kernel on each coordinate
chart. Its inverse frame restores the omitted coordinate by the usual
negative weighted sum; the forward frame is actual coordinate projection. -/
def kernelFrameIso (a : Option I → 𝒜 1) :
    (kernel (powerQuotient a)).over (Proj.basicOpen 𝒜 (a none : A)) ≅
      (SheafModulePowers.structurePower (Proj 𝒜) I).over
        (Proj.basicOpen 𝒜 (a none : A)) :=
  SheafUnitPivotKernel.frameIso (Proj.twistingSheaf 𝒜 (1 : ℤ))
    (fun i => homogeneousSection (a i)) (Proj.basicOpen 𝒜 (a none : A))
    (fun V hV => Proj.twistingSheaf.chartSectionsLinearEquiv 1
      (a none : A) (a none).property V hV)
    (by
      intro V hV
      change Proj.twistingSheaf.chartSectionsLinearEquiv 1
        (a none : A) (a none).property V hV 1 =
          Proj.toTwistingSheaf 𝒜 rfl V (a none)
      rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
      exact (homogeneousSection_eq_chartGenerator (a none) V hV).symm)

end FiniteCoordinates

section Polynomial

variable (R : Type) [CommRing R] (J : Type) [Fintype J] [DecidableEq J]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate generators of the ordinary polynomial projective
space, as degree-one homogeneous elements. -/
def polynomialCoordinates (j : J) : MvPolynomial.homogeneousSubmodule J R 1 :=
  ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X R j⟩

theorem polynomialCoordinates_cover :
    (⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule J R)
      (polynomialCoordinates R J j : MvPolynomial J R)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  rw [← Set.image_univ]
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro d hd
  have hdeg : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp hd)
  by_contra! h
  have hzero : d = 0 := by
    ext j
    exact h j (Set.mem_univ j)
  rw [hzero, map_zero] at hdeg
  omega

/-- The genuine universal line quotient `O^J → O(1)` on polynomial
projective space, over every commutative coefficient ring. -/
theorem polynomialQuotient_epi : Epi (quotientMap (polynomialCoordinates R J)) :=
  quotientMap_epi _ (polynomialCoordinates_cover R J)

end Polynomial

end PaperVerification.ProjectiveUniversalQuotient
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjectiveUniversalQuotient"

section ComponentSource_4
/- Original module: PaperVerification.LocallyFreeOfFrames -/


/-!
# Local frames as native local-freeness data

An actual family of free-sheaf isomorphisms on an open cover gives Mathlib's
`IsLocallyFree` property and, for finite frames, its `IsFiniteType` property.
The construction retains the given sections as the local generators. It
therefore supplies the quasicoherence instance needed by relative `Proj`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace PaperVerification.LocallyFreeOfFrames

universe u
variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-- An ordinary open cover is a cover of the terminal object in the
actual open-set site. -/
theorem coversTop_of_iSup (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤) :
    (Opens.grothendieckTopology X).CoversTop U := by
  intro V x hx
  have hxU : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxU
  exact ⟨V ⊓ U i, homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩, hx, hi⟩

variable (M : X.Modules) (U : ι → X.Opens) (hU : (⨆ i, U i) = ⊤)
  (I : ι → Type u)
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (I i) ≅ M.over (U i))

include U hU I e

/-- The supplied actual frames define the native local generating sections. -/
def localGenerators : M.LocalGeneratorsData where
  I := ι
  X := U
  coversTop := coversTop_of_iSup U hU
  generators i := (SheafOfModules.free.generatingSections (I i)).ofEpi (e i).hom

instance localGenerators_isLocallyFreeData :
    (localGenerators M U hU I e).IsLocallyFreeData where
  isIso i := by
    change ι at i
    change IsIso ((SheafOfModules.free.generatingSections (I i)).ofEpi (e i).hom).π
    erw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π, Category.id_comp]
    infer_instance

/-- Local freeness follows from the actual covering frames. -/
theorem isLocallyFree : M.IsLocallyFree :=
  (localGenerators M U hU I e).isLocallyFree

instance localGenerators_isFiniteType [∀ i, Finite (I i)] :
    (localGenerators M U hU I e).IsFiniteType where
  isFiniteType i := by
    constructor
    exact inferInstanceAs (Finite (I i))

/-- A family of finite actual frames gives native finite type as well. -/
theorem isFiniteType [∀ i, Finite (I i)] : M.IsFiniteType := by
  constructor
  exact ⟨localGenerators M U hU I e, inferInstance⟩

end PaperVerification.LocallyFreeOfFrames
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.LocallyFreeOfFrames"

section ComponentSource_5
/- Original module: PaperVerification.ProjectiveUniversalLocalFreeness -/


/-!
# The universal kernel is a genuine vector bundle

Every coordinate can serve as the unit pivot. Reindexing the actual finite
power sheaf transports the explicit kernel frame to each standard open.
These frames give native local freeness and finite type for the categorical
kernel of `O^I → O(1)`, over an arbitrary commutative base ring.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace PaperVerification.SheafFiniteCoordinates

universe u
variable {X : Scheme.{u}}

/-- The standard biproduct comparison identifies the actual free sheaf
with the finite power of the structure sheaf. -/
def freePowerIso (I : Type u) [Fintype I] :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      SheafModulePowers.structurePower X I := by
  letI : HasBiproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf) :=
    HasBiproduct.of_hasProduct _
  exact (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    biproduct.isoProduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)

/-- Restriction of the same finite power retains its actual free frame. -/
def freeOverPowerIso (I : Type u) [Fintype I] (U : X.Opens) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
      (SheafModulePowers.structurePower X I).over U := by
  letI : (SheafOfModules.overFunctor X.ringCatSheaf U).Additive := { map_add := rfl }
  exact SheafOfModules.mapFreeIso (SheafOfModules.overFunctor X.ringCatSheaf U) I (Iso.refl _) ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso (freePowerIso I)

/-- Coordinate changes act by their actual product projections. -/
def reindexIso (M : X.Modules) {I J : Type u} (e : J ≃ I) :
    SheafModulePowers.power M I ≅ SheafModulePowers.power M J where
  hom := SheafModulePowers.reindex M I J e
  inv := SheafModulePowers.reindex M J I e.symm
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, SheafModulePowers.reindex_projection,
      Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, SheafModulePowers.reindex_projection,
      Equiv.symm_apply_apply, Category.id_comp]

/-- Reindexing the coordinates and the evaluated sections together leaves
the original sheaf morphism unchanged. -/
theorem reindex_fromSections (M : X.Modules) {I J : Type u}
    [Fintype I] [Fintype J] (e : J ≃ I) (s : I → M.sections) :
    (reindexIso (SheafOfModules.unit X.ringCatSheaf) e).hom ≫
      SheafCoordinateMorphisms.fromSections M (s ∘ e) =
        SheafCoordinateMorphisms.fromSections M s := by
  simp only [SheafCoordinateMorphisms.fromSections, Preadditive.comp_sum,
    ← Category.assoc, reindexIso]
  calc
    _ = ∑ j : J, Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) (e j) ≫
        (SheafOfModules.unitHomEquiv M).symm (s (e j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun q => q ≫ (SheafOfModules.unitHomEquiv M).symm (s (e j)))
        (SheafModulePowers.reindex_projection
          (SheafOfModules.unit X.ringCatSheaf) I J e j)
    _ = _ := e.sum_comp (fun i =>
      Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        (SheafOfModules.unitHomEquiv M).symm (s i))

end PaperVerification.SheafFiniteCoordinates

namespace PaperVerification.ProjectiveUniversalQuotient

variable {A σ I : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] [Fintype I] [DecidableEq I]

/-- The actual universal kernel has the frame omitting coordinate `i` on
its corresponding standard open. This includes every finite rank. -/
def kernelFrameAt (a : I → 𝒜 1) (i : I) :
    (kernel (powerQuotient a)).over (Proj.basicOpen 𝒜 (a i : A)) ≅
      (SheafModulePowers.structurePower (Proj 𝒜) {j : I // j ≠ i}).over
        (Proj.basicOpen 𝒜 (a i : A)) := by
  let e := Equiv.optionSubtypeNe i
  let p := SheafFiniteCoordinates.reindexIso
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) e
  let k := kernel.mapIso (f := powerQuotient a) (powerQuotient (a ∘ e)) p
    (Iso.refl _) (by
      change powerQuotient a = p.hom ≫ powerQuotient (a ∘ e)
      exact (SheafFiniteCoordinates.reindex_fromSections (Proj.twistingSheaf 𝒜 (1 : ℤ))
          e (fun j => homogeneousSection (a j))).symm)
  exact (SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf
      (Proj.basicOpen 𝒜 (a i : A))).mapIso k ≪≫ kernelFrameIso (a ∘ e)

/-- The actual free-sheaf frame on each coordinate open. -/
def kernelFreeFrameAt (a : I → 𝒜 1) (i : I) :
    SheafOfModules.free
      (R := (Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 (a i : A)))
      {j : I // j ≠ i} ≅
        (kernel (powerQuotient a)).over (Proj.basicOpen 𝒜 (a i : A)) :=
  SheafFiniteCoordinates.freeOverPowerIso _ _ ≪≫ (kernelFrameAt a i).symm

/-- Covering homogeneous coordinates make the genuine universal kernel
locally free in Mathlib's original sense. -/
theorem kernel_isLocallyFree (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) :
    (kernel (powerQuotient a)).IsLocallyFree :=
  LocallyFreeOfFrames.isLocallyFree _ _ hcover
    (fun i => {j : I // j ≠ i}) (kernelFreeFrameAt a)

/-- The same actual universal kernel is of finite type. -/
theorem kernel_isFiniteType (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) :
    (kernel (powerQuotient a)).IsFiniteType :=
  LocallyFreeOfFrames.isFiniteType _ _ hcover
    (fun i => {j : I // j ≠ i}) (kernelFreeFrameAt a)

/-- Consequently this kernel has the genuine quasicoherence required
for its relative projectivization. -/
theorem kernel_isQuasicoherent (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) :
    (kernel (powerQuotient a)).IsQuasicoherent := by
  letI := kernel_isLocallyFree a hcover
  infer_instance

end PaperVerification.ProjectiveUniversalQuotient
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.ProjectiveUniversalLocalFreeness"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.UnitPivotKernel.kernelEquiv, "definition"),
    (`PaperVerification.UnitPivotKernel.kernel_projection_bijective, "theorem"),
    (`PaperVerification.SheafFiniteCoordinates.freeToPower_fromSections, "theorem"),
    (`PaperVerification.SheafUnitPivotKernel.projection_bijective, "theorem"),
    (`PaperVerification.SheafUnitPivotKernel.frameIso, "definition"),
    (`PaperVerification.ProjectiveUniversalQuotient.quotientMap_epi, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.powerQuotient_epi, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.kernelFrameIso, "definition"),
    (`PaperVerification.ProjectiveUniversalQuotient.polynomialCoordinates_cover, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.polynomialQuotient_epi, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.kernel_isLocallyFree, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.kernel_isFiniteType, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.kernel_isQuasicoherent, "theorem"),
    (`PaperVerification.ProjectiveUniversalQuotient.kernelFrameAt, "definition"),
    (`PaperVerification.LocallyFreeOfFrames.isLocallyFree, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "2eda59f888fd766122c53f35cfee6f5c"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:2eda59f888fd766122c53f35cfee6f5c"
