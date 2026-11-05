module

public import PaperVerification.ToricCartierOrders
public import PaperVerification.ToricModuleFrameGluing

@[expose] public section

/-!
# Local Cartier frames under an actual line-bundle isomorphism

An isomorphism of the underlying module sheaves need not preserve their
fractional embeddings. It does, however, preserve the regular change of
coordinates between two transported frames. This distinction is used
when proving that degree depends only on the actual line bundle.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes

namespace ModuleFrame

variable {X : Scheme.{u}} {M N : X.Modules} (F : M ≅ N)
    {U : X.Opens} (e : ModuleFrame N U)

def precompose : ModuleFrame M U :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso F ≪≫ e

@[simp] theorem precompose_coordinates (V : X.Opens) (hV : V≤U)
    (s : Γ(M,V)) :
    (e.precompose F).coordinates V hV s = e.coordinates V hV (F.hom.app V s) := rfl

@[simp] theorem precompose_generator (V : X.Opens) (hV : V≤U) :
    F.hom.app V ((e.precompose F).generator V hV) = e.generator V hV := by
  apply (e.coordinates V hV).injective
  rw [← precompose_coordinates,coordinates_generator,coordinates_generator]

end ModuleFrame

namespace CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)
    (F : D.sheaf ≅ E.sheaf)

/-- Ratios of transported rational generators agree, even though the
individual generators need not have the same rational value. -/
theorem precompose_frameRatio {U V : X.Opens} [Nonempty U] [Nonempty V]
    (e : E.Frame U) (q : E.Frame V) :
    D.frameRationalGenerator (ModuleFrame.precompose F e) /
      D.frameRationalGenerator (ModuleFrame.precompose F q) =
        E.frameRationalGenerator e / E.frameRationalGenerator q := by
  let W := U⊓V
  letI : Nonempty W := ⟨⟨genericPoint X,genericPoint_mem_open X U,
    genericPoint_mem_open X V⟩⟩
  let c := (ModuleFrame.precompose F q).coordinates W inf_le_right
    ((ModuleFrame.precompose F e).generator W inf_le_left)
  have hD : (ModuleFrame.precompose F e).generator W inf_le_left =
      c • (ModuleFrame.precompose F q).generator W inf_le_right :=
    (ModuleFrame.precompose F q).section_eq W inf_le_right _
  have hE := congrArg (F.hom.app W) hD
  rw [ModuleFrame.precompose_generator,Scheme.Modules.Hom.app_smul,
    ModuleFrame.precompose_generator] at hE
  have hDv := congrArg (D.sectionValue W) hD
  have hEv := congrArg (E.sectionValue W) hE
  change D.sectionValue W (D.frameGenerator (ModuleFrame.precompose F e) W inf_le_left) =
    D.sectionValue W (c • D.frameGenerator (ModuleFrame.precompose F q) W inf_le_right) at hDv
  change E.sectionValue W (E.frameGenerator e W inf_le_left) =
    E.sectionValue W (c • E.frameGenerator q W inf_le_right) at hEv
  rw [D.sectionValue_frameGenerator,D.sectionValue_smul,D.sectionValue_frameGenerator] at hDv
  rw [E.sectionValue_frameGenerator,E.sectionValue_smul,E.sectionValue_frameGenerator] at hEv
  calc
    D.frameRationalGenerator (ModuleFrame.precompose F e) /
        D.frameRationalGenerator (ModuleFrame.precompose F q) = X.germToFunctionField W c := by
      rw [hDv,mul_div_cancel_right₀ _ (D.frameRationalGenerator_ne_zero _)]
    _ = E.frameRationalGenerator e / E.frameRationalGenerator q := by
      rw [hEv,mul_div_cancel_right₀ _ (E.frameRationalGenerator_ne_zero _)]

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.precompose_frameRatio
