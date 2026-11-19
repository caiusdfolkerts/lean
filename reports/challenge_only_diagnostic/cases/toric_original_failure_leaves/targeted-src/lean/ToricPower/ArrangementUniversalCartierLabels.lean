module

public import ToricPower.ArrangementUniversalTheta
public import ToricPower.ArrangementUniversalCover
public import ToricPower.ArrangementPowerQuasicoherent
public import ToricPower.ToricMonomialDualityFunctor

/-! # Actual Cartier labels on the full universal arrangement

The absolute ceiling label at a cell translated by `-m` differs from
its normalized label by the principal character `m`. The comparison
below uses multiplication by the literal character `-m`. Its naturality
is the exact lattice-carry equation for every weighted incidence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "W" => WeightedIncidenceObject A
local notation "U" => UniversalIncidenceObject A
local notation "C" => IncidenceObject A

/-- The complete weighted projection, with every actual carry retained. -/
def weightedCellProjection : W ⥤ C :=
  weightedToElements A ⋙ Elements.π (universalWeightFunctor A)

theorem weightedAbsoluteDualCoefficients (c : W) (ρ : fan.Ray) :
    universalDualCoefficients fan basis rays ((weightedIncidenceToCells A).obj c) ρ =
      normalizedDualCartierCoefficients fan basis rays c.1 ρ -
        basis.equivFun.symm c.2 (fanRayPrimitiveGenerator fan ρ) := by
  change c.1.2.val.val.1 (.inl (rays.symm ρ)) +
      augmentedLatticePairing A (-c.2) (.inl (rays.symm ρ)) - 1 = _
  rw [augmentedLatticePairing_neg]
  change c.1.2.val.val.1 (.inl (rays.symm ρ)) -
      rayPairing A c.2 (rays.symm ρ) - 1 =
    -(-c.1.2.val.val.1 (.inl (rays.symm ρ))) - 1 -
      basis.equivFun.symm c.2 (fanRayPrimitiveGenerator fan ρ)
  rw [fanArrangementMatrix_character fan basis rays]
  omega

/-- The true principal-character comparison on every full lattice lift. -/
def weightedAbsoluteDualCoefficientIso :
    weightedIncidenceToCells A ⋙ universalDualCoefficientDiagram fan basis rays ≅
      weightedCellProjection fan basis rays ⋙ normalizedDualCoefficientDiagram fan basis rays :=
  NatIso.ofComponents (fun c =>
    { hom := ⟨-basis.equivFun.symm c.2,by
        intro ρ
        change 0 ≤ normalizedDualCartierCoefficients fan basis rays c.1 ρ -
          universalDualCoefficients fan basis rays ((weightedIncidenceToCells A).obj c) ρ +
            (-basis.equivFun.symm c.2) (fanRayPrimitiveGenerator fan ρ)
        rw [weightedAbsoluteDualCoefficients]
        simp only [AddMonoidHom.neg_apply]
        omega⟩
      inv := ⟨basis.equivFun.symm c.2,by
        intro ρ
        change 0 ≤
          universalDualCoefficients fan basis rays ((weightedIncidenceToCells A).obj c) ρ -
          normalizedDualCartierCoefficients fan basis rays c.1 ρ +
            basis.equivFun.symm c.2 (fanRayPrimitiveGenerator fan ρ)
        rw [weightedAbsoluteDualCoefficients]
        omega⟩
      hom_inv_id := Subtype.ext (neg_add_cancel _)
      inv_hom_id := Subtype.ext (add_neg_cancel _) }) (by
    intro c d f
    apply Subtype.ext
    change (0 : N →+ ℤ) + -basis.equivFun.symm d.2 =
      -basis.equivFun.symm c.2 + -basis.equivFun.symm f.val.val
    rw [zero_add]
    exact (congrArg (fun m : Fin n → ℤ => -basis.equivFun.symm m) f.property).trans
      (by rw [_root_.map_add,neg_add]))

/-- Normalization is undone on the actual universal cells, through
the explicit equivalence and its genuine counit. -/
def universalNormalizedDualCoefficientIso :
    universalDualCoefficientDiagram fan basis rays ≅
      universalCoverProjection A ⋙ normalizedDualCoefficientDiagram fan basis rays :=
  (Functor.leftUnitor (universalDualCoefficientDiagram fan basis rays)).symm ≪≫
    Functor.isoWhiskerRight (weightedExplicitCellEquivalence A).counitIso.symm
      (universalDualCoefficientDiagram fan basis rays) ≪≫
    Functor.isoWhiskerLeft (cellsToWeighted A)
      (weightedAbsoluteDualCoefficientIso fan basis rays)

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

/-- Actual Cartier module sheaves, not only coefficient vectors, obey
the same complete deck-character comparison. -/
def universalNormalizedCartierDiagramIso :
    universalDualCoefficientDiagram fan basis rays ⋙
        ToricMonomial.realization fan nonempty regular ≅
      universalCoverProjection A ⋙
        normalizedDualCartierDiagram fan nonempty regular basis rays :=
  Functor.isoWhiskerRight (universalNormalizedDualCoefficientIso fan basis rays)
    (ToricMonomial.realization fan nonempty regular)

/-- The absolute dual line labels in the actual quasicoherent category. -/
def universalDualQuasicoherentDiagram : U ⥤ QCoh fan.algebraicRealization :=
  universalDualCoefficientDiagram fan basis rays ⋙
    ToricMonomial.quasicoherent fan nonempty regular

/-- The same comparison in QCoh retains the exact underlying character maps. -/
def universalNormalizedQuasicoherentDiagramIso :
    universalDualQuasicoherentDiagram fan basis rays nonempty regular ≅
      universalCoverProjection A ⋙
        normalizedDualQuasicoherentDiagram fan nonempty regular basis rays :=
  Functor.fullyFaithfulCancelRight (quasicoherentInclusion fan.algebraicRealization)
    (universalNormalizedCartierDiagramIso fan basis rays nonempty regular)

/-- Tensor the absolute labels with arbitrary actual coefficients. -/
def universalDualTensorDiagram : QCoh fan.algebraicRealization ⥤
    U ⥤ QCoh fan.algebraicRealization :=
  (curriedTensor (QCoh fan.algebraicRealization)).flip ⋙
    (Functor.whiskeringLeft U (QCoh fan.algebraicRealization)
      (QCoh fan.algebraicRealization)).obj
      (universalDualQuasicoherentDiagram fan basis rays nonempty regular)

/-- Naturality holds simultaneously in all universal incidences and
all quasicoherent coefficients. -/
def universalNormalizedTensorDiagramIso :
    universalDualTensorDiagram fan basis rays nonempty regular ≅
      normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays ⋙
        (Functor.whiskeringLeft U C (QCoh fan.algebraicRealization)).obj
          (universalCoverProjection A) :=
  NatIso.ofComponents (fun M =>
    Functor.isoWhiskerRight
      (universalNormalizedQuasicoherentDiagramIso fan basis rays nonempty regular)
      ((curriedTensor (QCoh fan.algebraicRealization)).flip.obj M)) (by
        intro M M' f
        apply NatTrans.ext
        funext c
        exact (((curriedTensor (QCoh fan.algebraicRealization)).flip.map f).naturality
          ((universalNormalizedQuasicoherentDiagramIso fan basis rays nonempty regular).hom.app c)).symm)

end ToricPower

end
