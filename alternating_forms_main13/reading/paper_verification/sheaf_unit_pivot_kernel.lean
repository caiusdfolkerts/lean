module

public import PaperVerification.SheafModuleKernels
public import PaperVerification.SheafCoordinateMorphisms
public import PaperVerification.UnitPivotKernel

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
