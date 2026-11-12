module

public import ToricPower.AffineOpenIntrinsicLabelHomExact
public import ToricPower.AffineSectionsColimits
public import ToricPower.CellularHomAdjunction
public import ToricPower.SchemeAffineLinear

/-! # Unrestricted colimits of actual affine invertible-label Hom diagrams

Each invertible source is represented by an actual Cartier divisor.
Its Hom functor is the inverse Cartier tensor equivalence followed by
actual affine sections, so it preserves all small colimits. The linear
restriction--pushforward adjunction transports this statement to the
whole original Hom diagram on an affine open direct image.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
  [IsIntegral X] {C : Type u} [Category.{u} C] (P : Cᵒᵖ ⥤ QCoh X)

local instance affineHomUnderlyingLinear : Linear k (_root_.SheafOfModules X.ringCatSheaf) :=
  Scheme.Modules.baseLinear k X

/-- The actual coefficient-natural Cartier tensor--section description
of one intrinsic quasicoherent Hom component. -/
def quasicoherentHomCartierComponentIso (c : C) (D : CartierDivisor X)
    (e : (P.obj (op c)).obj ≅ D.sheaf) :
    Cellular.homDiagram k P ⋙ (evaluation C (ModuleCat.{u} k)).obj c ≅
      (quasicoherentCartierTensorEquivalence D).inverse ⋙
        quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤ :=
  NatIso.ofComponents (fun M =>
    ((quasicoherentUnderlyingHomLinearEquiv k X (P.obj (op c)) M).trans
      ((Linear.homCongr k e (Iso.refl M.obj)).trans
        (cartierHomSectionsLinearEquiv k X D M.obj))).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change cartierHomSectionsLinearEquiv k X D N.obj
        ((e.inv ≫ (g ≫ f).hom) ≫ 𝟙 N.obj) =
      (FiniteCover.schemeBaseSections k X ⊤).map
        ((tensorLeft (-D).sheaf).map f.hom)
        (cartierHomSectionsLinearEquiv k X D M.obj ((e.inv ≫ g.hom) ≫ 𝟙 M.obj))
    simp only [Category.comp_id]
    exact (congrArg (cartierHomSectionsLinearEquiv k X D N.obj)
      (Category.assoc e.inv g.hom f.hom).symm).trans
      (cartierHomSectionsLinearEquiv_coefficient k X D f.hom (e.inv ≫ g.hom)))

/-- An actual invertible-label Hom diagram on an integral affine scheme
preserves every small colimit, with no finite-generation condition on
the target coefficient modules. -/
theorem quasicoherentAffineInvertibleHom_preservesColimits [IsAffine X]
    (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      X (P.obj (op c)).obj) :
    PreservesColimitsOfSize.{u,u} (Cellular.homDiagram k P) := by
  apply preservesColimits_of_evaluation
  intro c
  letI := invertible c
  obtain ⟨D,⟨e⟩⟩ := CartierDivisor.exists_nonempty_iso_sheaf
    (⟨(P.obj (op c)).obj,inferInstance⟩ : TauCeti.AlgebraicGeometry.InvertibleSheaf X)
  letI := affineBaseSections_preservesColimits k X ⊤ (isAffineOpen_top X)
  exact preservesColimits_of_natIso (quasicoherentHomCartierComponentIso k X P c D e).symm

variable {U : Scheme.{u}} [U.Over (Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [IsAffineHom j] [j.IsOver (Spec (.of k))]

instance quasicoherentAffinePushforward_baseLinear :
    (quasicoherentAffinePushforward j).Linear k where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.pushforward j).map_smul r f.hom

/-- The genuine open adjunction transfers unrestricted colimit
preservation to the complete original affine direct-image Hom diagram. -/
theorem quasicoherentOpenIntrinsicLabelHom_preservesColimits
    [IsAffine U] [IsIntegral U]
    (invertible : ∀ c, TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      X (P.obj (op c)).obj) :
    PreservesColimitsOfSize.{u,u} (quasicoherentOpenIntrinsicLabelHom k j P) := by
  have restricted (c : C) : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible U
      ((P ⋙ quasicoherentRestriction j).obj (op c)).obj := by
    letI := invertible c
    exact InvertibleRestriction.invertible_restrict j (P.obj (op c)).obj
  letI := quasicoherentAffineInvertibleHom_preservesColimits k U
    (P ⋙ quasicoherentRestriction j) restricted
  exact preservesColimits_of_natIso
    (Cellular.homDiagramAdjunctionIso k P (quasicoherentOpenAdjunction j))

end ToricPower

end
