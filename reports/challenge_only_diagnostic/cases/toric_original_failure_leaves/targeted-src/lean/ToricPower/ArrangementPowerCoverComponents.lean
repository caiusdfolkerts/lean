module

public import ToricPower.ArrangementUniversalCover
public import ToricPower.ArrangementPowerIncidence
public import ToricPower.ElementPullbackBaseChange
public import Mathlib.CategoryTheory.Products.Basic

/-!
# All components of the pulled-back universal covering

Over a power-cover object `(c,r)`, the universal covering still has
every lattice weight `m`. Its component label is the residue `r−m`.
This label is invariant under every incidence. The resulting category
is explicitly the product of the full universal weighted category and
the discrete set of all power residues.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

local notation "B" => powerResidueFunctor A ell positive
local notation "L" => universalWeightFunctor A
local notation "W" => WeightedIncidenceObject A

abbrev PowerUniversalObject := (Elements.π B ⋙ L).Elements

/-- Forget only the finite residue, retaining the entire lattice weight. -/
def powerUniversalToWeighted : PowerUniversalObject A ell positive ⥤ W where
  obj c := (c.obj.obj,c.val)
  map f := ⟨f.hom.hom,f.map_val.symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The residue difference is constant on every genuine incidence. -/
def powerUniversalComponent (c : PowerUniversalObject A ell positive) :
    LatticeResidues (Fin n) ell :=
  latticeResidueTranslate ell positive (-(show Fin n → ℤ from c.val)) c.obj.val

theorem powerUniversalComponent_map {c d : PowerUniversalObject A ell positive}
    (f : c ⟶ d) : powerUniversalComponent A ell positive c =
      powerUniversalComponent A ell positive d := by
  have weight : (show Fin n → ℤ from c.val) + f.hom.hom.val = d.val := f.map_val
  have residue : latticeResidueTranslate ell positive f.hom.hom.val c.obj.val =
      d.obj.val := f.hom.map_val
  dsimp only [powerUniversalComponent]
  rw [← weight,← residue,← latticeResidueTranslate_add]
  congr 1
  abel

def powerUniversalToComponents : PowerUniversalObject A ell positive ⥤
    Discrete (LatticeResidues (Fin n) ell) × W where
  obj c := (⟨powerUniversalComponent A ell positive c⟩,
    (powerUniversalToWeighted A ell positive).obj c)
  map f := (Discrete.eqToHom (powerUniversalComponent_map A ell positive f),
    (powerUniversalToWeighted A ell positive).map f)
  map_id _ := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  map_comp _ _ := by
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl

/-- Every residue component contains every universal cell. -/
def powerComponentsToUniversal :
    Discrete (LatticeResidues (Fin n) ell) × W ⥤ PowerUniversalObject A ell positive where
  obj c := (Elements.π B ⋙ L).elementsMk
    ((B).elementsMk c.2.1 (latticeResidueTranslate ell positive c.2.2 c.1.as)) c.2.2
  map {c d} f :=
    ⟨⟨f.2.val,by
      change latticeResidueTranslate ell positive f.2.val.val
        (latticeResidueTranslate ell positive c.2.2 c.1.as) =
        latticeResidueTranslate ell positive d.2.2 d.1.as
      rw [← latticeResidueTranslate_add,← f.2.property,Discrete.eq_of_hom f.1]⟩,
      f.2.property.symm⟩
  map_id _ := by
    apply Elements.hom_ext
    apply Elements.hom_ext
    rfl
  map_comp _ _ := by
    apply Elements.hom_ext
    apply Elements.hom_ext
    rfl

instance powerUniversalToWeighted_faithful :
    (powerUniversalToWeighted A ell positive).Faithful where
  map_injective h := by
    apply Elements.hom_ext
    apply Elements.hom_ext
    exact congrArg Subtype.val h

/-- The complete product decomposition; no sheet or component is removed. -/
def powerUniversalComponentsEquivalence : PowerUniversalObject A ell positive ≌
    Discrete (LatticeResidues (Fin n) ell) × W where
  functor := powerUniversalToComponents A ell positive
  inverse := powerComponentsToUniversal A ell positive
  unitIso := NatIso.ofComponents (fun c => eqToIso (by
    cases c with
    | @mk c m =>
      cases c with
      | @mk c r =>
        change (Elements.π B ⋙ L).elementsMk ((B).elementsMk c r) m =
          (Elements.π B ⋙ L).elementsMk ((B).elementsMk c
            (latticeResidueTranslate ell positive m
              (latticeResidueTranslate ell positive (-(show Fin n → ℤ from m)) r))) m
        rw [← latticeResidueTranslate_add,neg_add_cancel,latticeResidueTranslate_zero])) (by
      intros
      apply (powerUniversalToWeighted A ell positive).map_injective
      exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun c => eqToIso (by
    rcases c with ⟨⟨r⟩,c,m⟩
    change (Discrete.mk (latticeResidueTranslate ell positive (-m)
      (latticeResidueTranslate ell positive m r)),(c,m)) = (Discrete.mk r,(c,m))
    rw [← latticeResidueTranslate_add,add_neg_cancel,latticeResidueTranslate_zero])) (by
      intros
      apply Prod.ext <;> exact Subsingleton.elim _ _)
  functor_unitIso_comp _ := by
    apply Prod.ext <;> exact Subsingleton.elim _ _

end ToricPower.IntegralArrangement

end
