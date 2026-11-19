module

public import ToricPower.CechContractibleVanishing
public import ToricPower.CellularCechDual

/-! # The canonical constant cochain augmentation of a contractible nerve -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open ToricPower.NegativeSupportRelative ToricPower.CechIncidenceChains
open ToricPower.CechCanonicalAugmentation ToricPower.CechContractibleVanishing
open BondalThomsen.ConvexNerveReducedCochainAcyclicity

namespace ToricPower

variable (k : Type) [Field k]

abbrev augmentationScalarMap : AddCommGrpCat.of k ⟶
    (scalarCoefficientDual k).obj (op incidenceAugmentationObject) :=
  CechReducedSingular.augmentationScalarMap k

theorem augmentationScalarMap_value (a : k) :
    (Sigma.ι (fun _ : Unit => AddCommGrpCat.of ℤ) () ≫
      augmentationScalarMap k a) (1 : ℤ) = a := by
  change (Sigma.ι _ () ≫ augmentationScalar k a) (1 : ℤ) = a
  simp [augmentationScalar]

instance augmentationScalarMap_isIso : IsIso (augmentationScalarMap k) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b h
    have value := congrArg (fun f : incidenceAugmentationObject ⟶ AddCommGrpCat.of k =>
      (Sigma.ι (fun _ : Unit => AddCommGrpCat.of ℤ) () ≫ f) (1 : ℤ)) h
    exact (augmentationScalarMap_value k a).symm.trans
      (value.trans (augmentationScalarMap_value k b))
  · intro f
    refine ⟨(Sigma.ι (fun _ : Unit => AddCommGrpCat.of ℤ) () ≫ f) (1 : ℤ),?_⟩
    apply Sigma.hom_ext
    intro i
    cases i
    apply AddCommGrpCat.hom_ext
    apply (zmultiplesHom k).symm.injective
    exact augmentationScalarMap_value k _

variable {Ray : Type*} {Chart : Type}

/-- This is the actual dual of the integral augmentation, with the
canonical scalar identification at the source. -/
def negativeConstantChainMap (incidence : Ray → Chart → Prop) (negative : Ray → Prop) :
    (CochainComplex.single₀ AddCommGrpCat).obj (AddCommGrpCat.of k) ⟶
      negativeComplex k incidence negative :=
  (CochainComplex.single₀ AddCommGrpCat).map (augmentationScalarMap k) ≫
    (Cellular.dualSingleZeroIso (scalarCoefficientDual k) incidenceAugmentationObject).inv ≫
      dualChainMap k (incidenceChainAugmentationMap incidence negative) ≫
        (incidenceDualIso k incidence negative).hom

theorem negativeConstantChainMap_zero (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) (a : k) (t : forbiddenTuple incidence negative 0) :
    (negativeConstantChainMap k incidence negative).f 0 a t = a := by
  have value := congrFun
    (incidenceDualEvaluation_extension k incidence negative 0 (fun _ => a)) t
  rw [incidenceDualExtension_constant] at value
  exact value

variable [Finite Chart]

theorem negativeConstantChainMap_quasiIso (incidence : Ray → Chart → Prop)
    (negative : Ray → Prop) [ContractibleSpace (incidenceRealization incidence negative)] :
    QuasiIso (negativeConstantChainMap k incidence negative) := by
  let e := contractibleIncidenceAugmentationEquiv incidence negative
  have same : e.hom = incidenceChainAugmentationMap incidence negative := by
    apply HomologicalComplex.to_single_hom_ext
    exact contractibleIncidenceAugmentationEquiv_hom incidence negative
  haveI : QuasiIso (dualChainMap k (incidenceChainAugmentationMap incidence negative)) := by
    rw [← same]
    change QuasiIso (dualChainHomotopyEquiv k e).inv
    infer_instance
  unfold negativeConstantChainMap
  infer_instance

end ToricPower

end
