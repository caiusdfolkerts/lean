module

public import ToricPower.ArrangementDualPowerSplitting
public import ToricPower.ArrangementPowerIncidence
public import ToricPower.ElementDiagramPushdown
public import ToricPower.ToricMonomialCategory

/-!
# Power decomposition of the entire normalized dual diagram

The direct image includes every residue sheet. Every incidence carries
the actual sheet permutation and carry character. The isomorphism is
natural on the whole translated incidence category.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 2000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

/-- Dualizing a monomial map keeps its scalar character. -/
def normalizedDualCoefficientDiagram : C ⥤ ToricMonomial.Object fan where
  obj c := ⟨normalizedDualCartierCoefficients fan basis rays c⟩
  map {c d} f := ⟨-basis.equivFun.symm f.val, by
    intro ρ
    have h := (diagonalEntryRegular_of_incidence fan basis rays f).2 ρ
    dsimp only [normalizedDualCartierCoefficients]
    simp only [AddMonoidHom.neg_apply]
    omega⟩
  map_id c := by
    apply Subtype.ext
    simp only [incidence_id_val, map_zero, neg_zero]
    rfl
  map_comp f g := by
    apply Subtype.ext
    simp only [incidence_comp_val, map_add, neg_add]
    rfl

/-- The actual covariant normalized dual Cartier diagram. -/
def normalizedDualCartierDiagram : C ⥤ fan.algebraicRealization.Modules :=
  normalizedDualCoefficientDiagram fan basis rays ⋙
    ToricMonomial.realization fan nonempty regular

variable (ell : ℕ) (positive : 0 < ell)

local notation "B" => powerResidueFunctor A ell positive
local notation "W" => PowerIncidenceObject A ell positive

include positive

/-- The literal character equation for the global residue inclusion. -/
theorem powerResidue_character_carry {c d : W} (f : c ⟶ d) :
    -basis.equivFun.symm (latticeResidueRepresentative c.val) +
      (-basis.equivFun.symm f.hom.val) =
    -basis.equivFun.symm (latticeResidueRepresentative d.val) +
      ell • (-basis.equivFun.symm (latticeResidueCarry ell positive f.hom.val c.val)) := by
  have h := latticeResidueTranslate_carry ell positive f.hom.val c.val
  have residue : latticeResidueTranslate ell positive f.hom.val c.val = d.val := f.map_val
  rw [residue, natCast_zsmul] at h
  simpa only [map_add, map_nsmul, neg_add, smul_neg] using
    congrArg (fun a => -basis.equivFun.symm a) h

/-- The original residue coefficients before the inverse-branch identification. -/
def powerResidueDualCoefficientDiagram : W ⥤ ToricMonomial.Object fan where
  obj c := ⟨toricResidueCoefficients fan
    (normalizedDualCartierCoefficients fan basis rays c.obj) ell
    ((negativeCharacterBasis basis).equivFun.symm (latticeResidueRepresentative c.val))⟩
  map {c d} f := ⟨-basis.equivFun.symm (latticeResidueCarry ell positive f.hom.val c.val), by
    simpa only [negativeCharacterBasis_character] using
      toricResidueMonomial_nonnegative fan
        (normalizedDualCartierCoefficients fan basis rays c.obj)
        (normalizedDualCartierCoefficients fan basis rays d.obj) ell positive
        (-basis.equivFun.symm f.hom.val)
        (-basis.equivFun.symm (latticeResidueRepresentative c.val))
        (-basis.equivFun.symm (latticeResidueRepresentative d.val))
        (-basis.equivFun.symm (latticeResidueCarry ell positive f.hom.val c.val))
        (powerResidue_character_carry fan basis rays ell positive f)
        ((normalizedDualCoefficientDiagram fan basis rays).map f.hom).property⟩
  map_id c := by
    apply Subtype.ext
    exact congrArg (fun h => h.val)
      ((powerBranchFunctor A ell positive ⋙
        normalizedDualCoefficientDiagram fan basis rays).map_id c)
  map_comp f g := by
    apply Subtype.ext
    exact congrArg (fun h => h.val)
      ((powerBranchFunctor A ell positive ⋙
        normalizedDualCoefficientDiagram fan basis rays).map_comp f g)

/-- Coefficient equality is realized by the unit character, naturally. -/
def powerResidueDualCoefficientIso :
    powerResidueDualCoefficientDiagram fan basis rays ell positive ≅
      powerBranchFunctor A ell positive ⋙ normalizedDualCoefficientDiagram fan basis rays :=
  NatIso.ofComponents (fun c => ToricMonomial.coefficientIso fan _ _ (by
    change toricResidueCoefficients fan
      (normalizedDualCartierCoefficients fan basis rays c.obj) ell
      ((negativeCharacterBasis basis).equivFun.symm (latticeResidueRepresentative c.val)) = _
    rw [negativeCharacterBasis_character, normalizedDualCartier_residue fan basis rays ell positive]
    rfl)) (by
      intro c d f
      apply Subtype.ext
      exact (add_zero _).trans (zero_add _).symm)

def powerResidueDualCartierDiagram : W ⥤ fan.algebraicRealization.Modules :=
  powerResidueDualCoefficientDiagram fan basis rays ell positive ⋙
    ToricMonomial.realization fan nonempty regular

def powerResidueDualBranchIso :
    powerResidueDualCartierDiagram fan nonempty regular basis rays ell positive ≅
      powerBranchFunctor A ell positive ⋙
        normalizedDualCartierDiagram fan nonempty regular basis rays :=
  Functor.isoWhiskerRight (powerResidueDualCoefficientIso fan basis rays ell positive)
    (ToricMonomial.realization fan nonempty regular)

/-- The actual global residue inclusions along every lifted incidence. -/
def powerResidueDualInclusion :
    powerResidueDualCartierDiagram fan nonempty regular basis rays ell positive ⟶
      Functor.Elements.π B ⋙ normalizedDualCartierDiagram fan nonempty regular basis rays ⋙
        Scheme.Modules.pushforward (toricPowerMap fan ell) := by
  letI := toricSchemeIntegral fan nonempty
  exact {
    app := fun c => toricResidueSheafMap fan nonempty regular
      (normalizedDualCartierCoefficients fan basis rays c.obj) ell positive
      ((negativeCharacterBasis basis).equivFun.symm (latticeResidueRepresentative c.val))
    naturality := fun {c d} f => by
      have h := toricResidueSheafMap_monomial fan nonempty regular
        (normalizedDualCartierCoefficients fan basis rays c.obj)
        (normalizedDualCartierCoefficients fan basis rays d.obj) ell positive
        (-basis.equivFun.symm f.hom.val)
        ((negativeCharacterBasis basis).equivFun.symm (latticeResidueRepresentative c.val))
        ((negativeCharacterBasis basis).equivFun.symm (latticeResidueRepresentative d.val))
        (-basis.equivFun.symm (latticeResidueCarry ell positive f.hom.val c.val))
        (by simpa only [negativeCharacterBasis_character] using
          powerResidue_character_carry fan basis rays ell positive f)
        ((normalizedDualCoefficientDiagram fan basis rays).map f.hom).property
      simpa only [powerResidueDualCartierDiagram, powerResidueDualCoefficientDiagram,
        normalizedDualCartierDiagram, normalizedDualCoefficientDiagram,
        Functor.comp_map, ToricMonomial.realization, Functor.Elements.π_map,
        Functor.Elements.π_obj] using h.symm }

/-- Sum the canonical inclusions as a map of whole diagrams. -/
def powerResidueDualPushdownMap :
    ElementPushdown.obj B
        (powerResidueDualCartierDiagram fan nonempty regular basis rays ell positive) ⟶
      normalizedDualCartierDiagram fan nonempty regular basis rays ⋙
        Scheme.Modules.pushforward (toricPowerMap fan ell) where
  app c := Sigma.desc (fun r : (B).obj c =>
    (powerResidueDualInclusion fan nonempty regular basis rays ell positive).app
      ((B).elementsMk c r))
  naturality {c d} f := by
    apply Sigma.hom_ext
    intro r
    let E := powerResidueDualCartierDiagram fan nonempty regular basis rays ell positive
    let α := powerResidueDualInclusion fan nonempty regular basis rays ell positive
    change ElementPushdown.inclusion B E c r ≫
        (ElementPushdown.map B E f ≫ Sigma.desc (fun t => α.app ((B).elementsMk d t))) =
      ElementPushdown.inclusion B E c r ≫
        (Sigma.desc (fun t => α.app ((B).elementsMk c t)) ≫
          (normalizedDualCartierDiagram fan nonempty regular basis rays ⋙
            Scheme.Modules.pushforward (toricPowerMap fan ell)).map f)
    rw [ElementPushdown.inclusion_map_assoc]
    simp only [ElementPushdown.inclusion, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    exact α.naturality (ElementPushdown.lift B f r)

/-- This component is the genuine global residue splitting. -/
theorem powerResidueDualPushdownMap_app_isIso (c : C) :
    IsIso ((powerResidueDualPushdownMap fan nonempty regular basis rays ell positive).app c) := by
  letI := toricSchemeIntegral fan nonempty
  let family := toricResidueSheafFamily fan nonempty regular (negativeCharacterBasis basis)
    (normalizedDualCartierCoefficients fan basis rays c) ell
  letI := toricResidueSheafSum_isIso fan nonempty regular (negativeCharacterBasis basis)
    (normalizedDualCartierCoefficients fan basis rays c) ell positive
  have h : (powerResidueDualPushdownMap fan nonempty regular basis rays ell positive).app c =
      (biproduct.isoCoproduct family).inv ≫ toricResidueSheafSum fan nonempty regular
        (negativeCharacterBasis basis) (normalizedDualCartierCoefficients fan basis rays c)
        ell positive := by
    apply Sigma.hom_ext
    intro r
    simp only [powerResidueDualPushdownMap, powerResidueDualInclusion, Sigma.ι_comp_desc,
      biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc]
    exact (toricResidueSheafSum_summand fan nonempty regular (negativeCharacterBasis basis)
      (normalizedDualCartierCoefficients fan basis rays c) ell positive r).symm
  rw [h]
  infer_instance

/-- The complete natural power decomposition, including every residue and wall. -/
def normalizedDualCartierPowerDiagramIso :
    ElementPushdown.obj B (powerBranchFunctor A ell positive ⋙
      normalizedDualCartierDiagram fan nonempty regular basis rays) ≅
        normalizedDualCartierDiagram fan nonempty regular basis rays ⋙
          Scheme.Modules.pushforward (toricPowerMap fan ell) := by
  haveI (c : C) : IsIso
      ((powerResidueDualPushdownMap fan nonempty regular basis rays ell positive).app c) :=
    powerResidueDualPushdownMap_app_isIso fan nonempty regular basis rays ell positive c
  exact (ElementPushdown.functor B).mapIso
      (powerResidueDualBranchIso fan nonempty regular basis rays ell positive).symm ≪≫
    NatIso.ofComponents (fun c => asIso
      ((powerResidueDualPushdownMap fan nonempty regular basis rays ell positive).app c))
      (fun f => (powerResidueDualPushdownMap fan nonempty regular basis rays ell positive).naturality f)

end ToricPower

end
