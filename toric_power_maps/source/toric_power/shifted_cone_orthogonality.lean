module

public import ToricPower.RelativeBoundedSourceHomotopy
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Orthogonality to all shifts of an actual cone

This is a triangulated condition on the target. It characterizes the
vanishing needed to make the literal Hom precomposition a
quasi-isomorphism, and bounded-source row exactness establishes it.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive CochainComplex

namespace ToricPower

universe u v r
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The right orthogonal to every integral shift of the displayed
actual complex, considered in the homotopy category. -/
def shiftedHomotopyRightOrthogonal (K : CochainComplex C ℤ) :
    ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  ((show ObjectProperty (HomotopyCategory C (.up ℤ)) from
    fun Z => Z = (HomotopyCategory.quotient C (.up ℤ)).obj K).shiftClosure ℤ).rightOrthogonal

instance (K : CochainComplex C ℤ) :
    (shiftedHomotopyRightOrthogonal K).IsTriangulated := by
  unfold shiftedHomotopyRightOrthogonal
  infer_instance

instance (K : CochainComplex C ℤ) :
    (shiftedHomotopyRightOrthogonal K).IsClosedUnderIsomorphisms := by
  unfold shiftedHomotopyRightOrthogonal
  infer_instance

/-- The defining morphism condition, with no ambiguity about shifts. -/
theorem shiftedHomotopyRightOrthogonal_iff
    (K : CochainComplex C ℤ) (Y : HomotopyCategory C (.up ℤ)) :
    shiftedHomotopyRightOrthogonal K Y ↔
      ∀ (n : ℤ) (f : ((HomotopyCategory.quotient C (.up ℤ)).obj K)⟦n⟧ ⟶ Y), f = 0 := by
  constructor
  · intro h n f
    exact h f ⟨_, n, Iso.refl _, rfl⟩
  · intro h Z f hZ
    obtain ⟨W, n, e, rfl⟩ := hZ
    apply (cancel_epi e.inv).mp
    rw [comp_zero]
    exact h n (e.inv ≫ f)

/-- Exact rows and a source bound place every unrestricted coefficient
complex in this genuine triangulated orthogonal. -/
theorem shiftedHomotopyRightOrthogonal_of_boundedSource
    (K L : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyGE d]
    (hrow : ∀ q, RightHomExact K (L.X q)) :
    shiftedHomotopyRightOrthogonal K
      ((HomotopyCategory.quotient C (.up ℤ)).obj L) := by
  rw [shiftedHomotopyRightOrthogonal_iff]
  exact shiftedHomotopyHom_eq_zero_of_boundedSource_rightHomExact K L d hrow

/-- The exact sequence of the actual cone triangle makes the actual
precomposition map bijective on targets in its shifted orthogonal. -/
theorem cone_precomp_bijective_of_shiftedOrthogonal
    {K L : CochainComplex C ℤ} (ε : K ⟶ L)
    (X : HomotopyCategory C (.up ℤ))
    (hX : shiftedHomotopyRightOrthogonal (mappingCone ε) X) :
    Function.Bijective (fun f : (HomotopyCategory.quotient C (.up ℤ)).obj L ⟶ X =>
      (HomotopyCategory.quotient C (.up ℤ)).map ε ≫ f) := by
  let T := mappingCone.triangleh ε
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished ε
  have vanish := (shiftedHomotopyRightOrthogonal_iff (mappingCone ε) X).mp hX
  constructor
  · intro a b hab
    change T.mor₁ ≫ a = T.mor₁ ≫ b at hab
    have closed : T.mor₁ ≫ (a-b) = 0 := by
      simpa only [comp_sub, sub_eq_zero] using hab
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT (a-b) closed
    have gz : g = 0 := by
      apply (cancel_epi ((shiftFunctorZero (HomotopyCategory C (.up ℤ)) ℤ).hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj (mappingCone ε)))).mp
      rw [comp_zero]
      exact vanish 0 _
    apply sub_eq_zero.mp
    rw [hg, gz, comp_zero]
  · intro a
    have closed : T.invRotate.mor₁ ≫ a = 0 := vanish (-1) _
    obtain ⟨g, hg⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a closed
    exact ⟨g, hg.symm⟩

/-- Orthogonality proves a quasi-isomorphism of the complete signed
Hom complexes, preserving the original augmentation map. -/
theorem linearHomComplexPrecomp_quasiIso_of_shiftedOrthogonal
    (R : Type r) [CommRing R] [Linear R C]
    {K L : CochainComplex C ℤ} (ε : K ⟶ L) (X : CochainComplex C ℤ)
    (hX : shiftedHomotopyRightOrthogonal (mappingCone ε)
      ((HomotopyCategory.quotient C (.up ℤ)).obj X)) :
    QuasiIso (linearHomComplexPrecomp R ε X) := by
  apply linearHomComplexPrecomp_quasiIso_of_homotopy_bijective
  intro n
  apply cone_precomp_bijective_of_shiftedOrthogonal ε
  let P := shiftedHomotopyRightOrthogonal (mappingCone ε)
  apply (P.prop_iff_of_iso
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).app X)).mpr
  exact P.le_shift n _ hX

end ToricPower

end
