module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The colimit of increasing free-module supports

For an increasing exhaustive family of subsets of an arbitrary index
type, extension by zero exhibits the full finitely supported module as
the actual categorical colimit. The proof gives the universal map on
each basis vector and proves independence of its chosen finite stage.
No uniform bound on the index set or on the support stages is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.ModuleIncreasingSupport

variable (R : Type) [CommRing R] {I : Type} (S : ℕ → Set I) (mono : Monotone S)

def indexMap {r t : ℕ} (h : r ≤ t) : S r → S t := fun i => ⟨i.val, mono h i.property⟩

def diagram : ℕ ⥤ ModuleCat.{0} R where
  obj r := ModuleCat.of R (S r →₀ R)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain (R := R) (M := R) (indexMap S mono f.le))
  map_id r := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i a
    change Finsupp.mapDomain (indexMap S mono le_rfl) (Finsupp.single i a) = Finsupp.single i a
    rw [Finsupp.mapDomain_single]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i a
    change Finsupp.mapDomain (indexMap S mono (f.le.trans g.le)) (Finsupp.single i a) =
      Finsupp.mapDomain (indexMap S mono g.le)
        (Finsupp.mapDomain (indexMap S mono f.le) (Finsupp.single i a))
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    rfl

def fullSupportCocone : Cocone (diagram R S mono) where
  pt := ModuleCat.of R (I →₀ R)
  ι :=
    { app r := ModuleCat.ofHom (Finsupp.lmapDomain (R := R) (M := R) Subtype.val)
      naturality r t f := by
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro i a
        change Finsupp.mapDomain Subtype.val
            (Finsupp.mapDomain (indexMap S mono f.le) (Finsupp.single i a)) =
          Finsupp.mapDomain Subtype.val (Finsupp.single i a)
        rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
        rfl }

variable (exhaustive : ∀ i : I, ∃ r : ℕ, i ∈ S r)

/-- The proposed value of a basis vector in a cocone, at one actual
stage containing that vector. -/
def basisValue (c : Cocone (diagram R S mono)) (i : I) : c.pt :=
  c.ι.app (Classical.choose (exhaustive i))
    (Finsupp.single ⟨i, Classical.choose_spec (exhaustive i)⟩ 1)

/-- Cocone compatibility through a common upper stage proves that the
value is independent of the chosen containing stage. -/
theorem basisValue_stage (c : Cocone (diagram R S mono)) (r : ℕ)
    (i : I) (hi : i ∈ S r) :
    basisValue R S mono exhaustive c i = c.ι.app r (Finsupp.single ⟨i, hi⟩ 1) := by
  let p := Classical.choose (exhaustive i)
  have hp : i ∈ S p := Classical.choose_spec (exhaustive i)
  have first := ConcreteCategory.congr_hom (c.w (homOfLE (le_max_left r p)))
    (Finsupp.single ⟨i, hi⟩ (1 : R))
  have second := ConcreteCategory.congr_hom (c.w (homOfLE (le_max_right r p)))
    (Finsupp.single ⟨i, hp⟩ (1 : R))
  change c.ι.app (max r p)
      (Finsupp.mapDomain (indexMap S mono (le_max_left r p)) (Finsupp.single ⟨i, hi⟩ 1)) =
    c.ι.app r (Finsupp.single ⟨i, hi⟩ 1) at first
  change c.ι.app (max r p)
      (Finsupp.mapDomain (indexMap S mono (le_max_right r p)) (Finsupp.single ⟨i, hp⟩ 1)) =
    c.ι.app p (Finsupp.single ⟨i, hp⟩ 1) at second
  rw [Finsupp.mapDomain_single] at first second
  exact second.symm.trans first

/-- The literal full finite-support module satisfies the colimit
universal property, including its specified extension-by-zero legs. -/
def fullSupportCoconeIsColimit : IsColimit (fullSupportCocone R S mono) where
  desc c := ModuleCat.ofHom (Finsupp.linearCombination R (basisValue R S mono exhaustive c))
  fac c r := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i a
    change Finsupp.linearCombination R (basisValue R S mono exhaustive c)
        (Finsupp.mapDomain Subtype.val (Finsupp.single i a)) = c.ι.app r (Finsupp.single i a)
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      basisValue_stage R S mono exhaustive c r i.val i.property]
    have single : (Finsupp.single i a : S r →₀ R) = a • Finsupp.single i 1 := by simp
    rw [single, map_smul]
  uniq c f compatible := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i a
    let r := Classical.choose (exhaustive i)
    have hi : i ∈ S r := Classical.choose_spec (exhaustive i)
    have value := ConcreteCategory.congr_hom (compatible r) (Finsupp.single ⟨i, hi⟩ a)
    change f (Finsupp.mapDomain Subtype.val (Finsupp.single ⟨i, hi⟩ a)) =
      c.ι.app r (Finsupp.single ⟨i, hi⟩ a) at value
    rw [Finsupp.mapDomain_single] at value
    change f (Finsupp.single i a) =
      Finsupp.linearCombination R (basisValue R S mono exhaustive c) (Finsupp.single i a)
    rw [value, Finsupp.linearCombination_single,
      basisValue_stage R S mono exhaustive c r i hi]
    have single : (Finsupp.single (⟨i, hi⟩ : S r) a) =
        a • Finsupp.single (⟨i, hi⟩ : S r) 1 := by simp
    rw [single, map_smul]

def fullSupportColimitIso :
    colimit (diagram R S mono) ≅ ModuleCat.of R (I →₀ R) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (fullSupportCoconeIsColimit R S mono exhaustive)

@[reassoc]
theorem fullSupportColimitIso_inclusion (r : ℕ) :
    colimit.ι (diagram R S mono) r ≫ (fullSupportColimitIso R S mono exhaustive).hom =
      ModuleCat.ofHom (Finsupp.lmapDomain (R := R) (M := R) (Subtype.val : S r → I)) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ r

end ToricPower.ModuleIncreasingSupport
