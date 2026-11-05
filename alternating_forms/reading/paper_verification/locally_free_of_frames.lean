module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

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
