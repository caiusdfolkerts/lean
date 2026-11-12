module

public import ToricPower.SchemePushforwardBaseSections
public import ToricPower.CartierCovariantHomSections
public import ToricPower.ClosedCopowerHom
public import ToricPower.ClosedContravariantCoefficient
public import ToricPower.ArrangementCellularChainCoefficientFunctor
public import ToricPower.ArrangementCellularHomTargetNaturality

/-! # Global sections of the actual finite dual-Cartier chains

The entire target functor of global sections is the ordinary Hom chain
of the original finite cellular cochains. The comparison retains the
actual Cartier adjunction mates, closed-support maps, all cellular signs,
and every target morphism. In particular it applies to an injective
resolution with its original differential.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor
open ToricPower.IntegralArrangement

namespace ToricPower

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [Field k]
  (X : Scheme) [X.Over (Spec (.of k))] [IsIntegral X]
  (P : IncidenceObject A ⥤ CartierSources X)
  (supported : IncidenceObject A → Prop)
  (downward : ∀ {c d : IncidenceObject A}, (c ⟶ d) → supported d → supported c)

local instance closedCartierChainBiproducts : HasFiniteBiproducts (QCoh X) :=
  HasFiniteBiproducts.of_hasFiniteProducts

local notation "Γ" => quasicoherentInclusion X ⋙ FiniteCover.schemeBaseSections k X ⊤
local notation "Q" => P ⋙ cartierSourcesQuasicoherent X

def closedCartierChainFunctor : QCoh X ⥤ ChainComplex (QCoh X) ℕ :=
  (P.op ⋙ cartierSourcesQuasicoherentInverseTensor X).flip ⋙
    Cellular.closedContravariantLabelEndofunctor supported downward ⋙
      arrangementCellularChainFunctor A k

def closedCartierCochain : CochainComplex (QCoh X) ℕ :=
  arrangementCellularCochainComplex A k
    (Cellular.covariantCopowerDiagram k Q (Cellular.closedScalarDiagram k supported downward))

/-- Naturality is at the full chain-functor level, not only on homology. -/
def closedCartierChainSectionsFunctorIso :
    closedCartierChainFunctor A k X P supported downward ⋙
      (Γ).mapHomologicalComplex (.down ℕ) ≅
    cellularOrdinaryHomFunctor A k
      (Cellular.covariantCopowerDiagram k Q (Cellular.closedScalarDiagram k supported downward)) := by
  let D := (P.op ⋙ cartierSourcesQuasicoherentInverseTensor X).flip
  let E := Cellular.closedContravariantLabelEndofunctor
    (B := QCoh X) supported downward
  let E' := Cellular.closedContravariantLabelEndofunctor
    (B := ModuleCat k) supported downward
  let first := isoWhiskerLeft (D ⋙ E)
    (cellularChainCoefficientFunctorIso A k Γ)
  let second := isoWhiskerRight
    (isoWhiskerLeft D (Cellular.closedContravariantCoefficientFunctorIso
      supported downward Γ)) (arrangementCellularChainFunctor A k)
  let third := isoWhiskerRight (cartierCovariantHomSectionsIso k X P).symm
    (E' ⋙ arrangementCellularChainFunctor A k)
  let fourth := isoWhiskerRight
    (Cellular.closedCopowerHomFunctorIso k Q supported downward).symm
      (arrangementCellularChainFunctor A k)
  let fifth := (cellularHomTargetFunctorIso A k
    (Cellular.covariantCopowerDiagram k Q (Cellular.closedScalarDiagram k supported downward))).symm
  exact first ≪≫ second ≪≫ third ≪≫ fourth ≪≫ fifth

end ToricPower

end

