module

public import ToricPower.SchemePullbackTensorQuasicoherent
public import ToricPower.InternalDualTensorInverse

/-!
# Pullback of specified inverse tensor pairings

The inverse pairings are pulled back using the canonical tensor and unit
comparisons. A pairing square remains the same pairing square after
pullback. This is the concrete duality input for the diagonal labels;
it does not require an internal Hom of arbitrary quasicoherent sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual pulled-back evaluation, with the canonical tensor map. -/
def pullbackPairingIso {L D : Y.Modules} [L.IsQuasicoherent]
    (evaluation : L ⊗ D ≅ 𝟙_ Y.Modules) :
    (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj D ≅
      𝟙_ X.Modules :=
  (quasicoherentPullbackTensorIso f L D).symm ≪≫
    (Scheme.Modules.pullback f).mapIso evaluation ≪≫
      Scheme.Modules.pullbackObjUnitIso f

/-- Compatibility retains the given morphisms and the given evaluation
maps, including every canonical pullback comparison. -/
theorem pullbackPairingIso_naturality
    {L D L' D' : Y.Modules} [L.IsQuasicoherent] [L'.IsQuasicoherent]
    (evaluation : L ⊗ D ≅ 𝟙_ Y.Modules)
    (evaluation' : L' ⊗ D' ≅ 𝟙_ Y.Modules)
    (a : L ⟶ L') (b : D' ⟶ D)
    (pairing : L ◁ b ≫ evaluation.hom = a ▷ D' ≫ evaluation'.hom) :
    (Scheme.Modules.pullback f).obj L ◁ (Scheme.Modules.pullback f).map b ≫
        (pullbackPairingIso f evaluation).hom =
      (Scheme.Modules.pullback f).map a ▷ (Scheme.Modules.pullback f).obj D' ≫
        (pullbackPairingIso f evaluation').hom := by
  letI := pullbackTensorComparisonLeft_isIso f L D'
  apply (cancel_epi (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) L D')).mp
  simp only [pullbackPairingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_right_assoc,
    Functor.OplaxMonoidal.δ_natural_left_assoc]
  simp only [quasicoherentPullbackTensorIso, asIso_inv, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, pairing]

/-- Pullback carries a specified inverse factor to the actual internal
dual of the pulled-back line, through the specified evaluation. -/
def pullbackInverseInternalDualIso {L D : Y.Modules}
    [L.IsQuasicoherent] [D.IsQuasicoherent]
    (eDL : D ⊗ L ≅ 𝟙_ Y.Modules) (eLD : L ⊗ D ≅ 𝟙_ Y.Modules) :
    (Scheme.Modules.pullback f).obj D ≅
      (internalDual X.Modules).obj (op ((Scheme.Modules.pullback f).obj L)) :=
  inverseTensorInternalDualIso _ _ (pullbackPairingIso f eDL) (pullbackPairingIso f eLD)

end ToricPower

end
