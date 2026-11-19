module

public import ToricPower.ArrangementPowerCoverComponents
public import ToricPower.ArrangementPowerLiftGeometry
public import ToricPower.ProductComponentDetection

/-!
# The selected integral branch inside the complete covering

An arbitrary integral translation `u` selects component `[-u]` of the
pulled-back universal covering. Its residue at `(c,m)` is exactly
`[m-u]`; its integral quotient is the carry used by the actual inverse
branch. The target coefficient retains the full universal diagram in
every component.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

local notation "W" => WeightedIncidenceObject A
local notation "B" => powerResidueFunctor A ell positive
local notation "L" => universalWeightFunctor A

/-- The actual whole component selected by an arbitrary integral
translation, before forgetting any covering coordinate. -/
def powerUniversalIntegralLift (u : Fin n → ℤ) :
    W ⥤ PowerUniversalObject A ell positive :=
  ProductComponent.embedding (latticeResidueOf ell positive (-u)) ⋙
    powerComponentsToUniversal A ell positive

def powerUniversalIntegralLiftProjectionIso (u : Fin n → ℤ) :
    powerUniversalIntegralLift A ell positive u ⋙ Elements.π (Elements.π B ⋙ L) ≅
      weightedPowerCoverLift A ell positive u := by
  have residue (c : W) :
      latticeResidueTranslate ell positive c.2 (latticeResidueOf ell positive (-u)) =
        latticeResidueOf ell positive (c.2-u) :=
    (latticeResidueOf_add ell positive (-u) c.2).symm.trans
      (congrArg (latticeResidueOf ell positive) (by abel))
  exact NatIso.ofComponents (fun c =>
    { hom := ⟨𝟙 c.1, by
        change latticeResidueTranslate ell positive 0
          (latticeResidueTranslate ell positive c.2 (latticeResidueOf ell positive (-u))) = _
        rw [latticeResidueTranslate_zero]
        exact residue c⟩
      inv := ⟨𝟙 c.1, by
        change latticeResidueTranslate ell positive 0
          (latticeResidueOf ell positive (c.2-u)) = _
        rw [latticeResidueTranslate_zero]
        exact (residue c).symm⟩
      hom_inv_id := by apply Elements.hom_ext; exact Category.id_comp _
      inv_hom_id := by apply Elements.hom_ext; exact Category.id_comp _ }) (by
        intro c d f
        apply Elements.hom_ext
        change f.val ≫ 𝟙 _ = 𝟙 _ ≫ f.val
        simp only [Category.comp_id,Category.id_comp])

/-- The selected component still contains the entire universal target. -/
def powerUniversalIntegralLiftCoefficientIso (u : Fin n → ℤ) :
    powerUniversalIntegralLift A ell positive u ⋙ powerUniversalToWeighted A ell positive ≅
      𝟭 W :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact Subsingleton.elim _ _)

/-- The same full target occurs in every residue component. -/
def powerAllComponentsCoefficientIso :
    powerComponentsToUniversal A ell positive ⋙ powerUniversalToWeighted A ell positive ≅
      CategoryTheory.Prod.snd (Discrete (LatticeResidues (Fin n) ell)) W :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; exact Subsingleton.elim _ _)

/-- The component source is precisely the quotient of the geometric
inverse branch, with its original integral carry on every incidence. -/
def powerUniversalIntegralLiftBranchIso (u : Fin n → ℤ) :
    powerUniversalIntegralLift A ell positive u ⋙
        Elements.π (Elements.π B ⋙ L) ⋙ powerBranchFunctor A ell positive ≅
      weightedPowerBranchFunctor A ell positive u ⋙
        weightedToElements A ⋙ Elements.π L :=
  Functor.isoWhiskerRight (powerUniversalIntegralLiftProjectionIso A ell positive u)
      (powerBranchFunctor A ell positive) ≪≫
    (weightedPowerBranchProjectionIso A ell positive u).symm

end ToricPower.IntegralArrangement

end
