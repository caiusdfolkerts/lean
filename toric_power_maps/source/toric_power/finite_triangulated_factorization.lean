module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Finite factorization through a triangulated collection

This is the finite-factorization step in the compact-generator argument
(Stacks, Tag 09SP). The two target pieces have the required factorization
property. A morphism into an extension is first approximated using a
morphism of triangles; its difference from the desired morphism is then
factored separately. Including this correction is essential.

The source property is an actual triangulated collection. In the toric
application it can be the essential image of bounded coherent objects.
No compactness or generation assertion is assumed implicitly.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace ToricPower.CompactExtraction

universe u v
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A factorization through a genuine object satisfying the property. -/
def FactorsThrough (Q : ObjectProperty C) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (E : C), Q E ∧ ∃ (i : X ⟶ E) (p : E ⟶ Y), i ≫ p = f

/-- Targets into which every map from the specified source collection
factors through the indicated finite collection. -/
def factorizationTargets (P Q : ObjectProperty C) : ObjectProperty C :=
  fun Y => ∀ (X : C), P X → ∀ f : X ⟶ Y, FactorsThrough Q f

variable (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms]
  (contained : Q ≤ P)

include contained

/-- Factorization through a triangulated collection is preserved when
forming one extension of targets. The source collection must be closed
under the actual cone constructions used in the proof. -/
theorem factorizationTargets_extension (T : Triangle C) (distinguished : T ∈ distTriang C)
    (left : factorizationTargets P Q T.obj₁)
    (right : factorizationTargets P Q T.obj₃) :
    factorizationTargets P Q T.obj₂ := by
  intro X hX f
  obtain ⟨E, hE, a, e, factor⟩ := right X hX (f ≫ T.mor₂)
  obtain ⟨X', hX', d, h, triangle⟩ :=
    P.distinguished_cocone_triangle₁ a hX (contained E hE)
  let S : Triangle C := Triangle.mk d a h
  obtain ⟨g, square, boundary⟩ := complete_distinguished_triangle_morphism₁ S T
    triangle distinguished f e factor
  obtain ⟨F, hF, b, p, factorG⟩ := left X' hX' g
  obtain ⟨E', hE', j, q, newTriangle⟩ :=
    Q.distinguished_cocone_triangle₂ (h ≫ b⟦(1 : ℤ)⟧') hF hE
  let S' : Triangle C := Triangle.mk j q (h ≫ b⟦(1 : ℤ)⟧')
  obtain ⟨lift₀, _, liftSquare₀⟩ := complete_distinguished_triangle_morphism₂ S S'
    triangle newTriangle b (𝟙 E) (by simp [S, S'])
  let lift : X ⟶ E' := lift₀
  have liftSquare : a = lift ≫ q := by
    change a ≫ 𝟙 E = lift ≫ q at liftSquare₀
    simpa only [Category.comp_id] using liftSquare₀
  have newBoundary : S'.mor₃ ≫ p⟦(1 : ℤ)⟧' = e ≫ T.mor₃ := by
    change (h ≫ b⟦(1 : ℤ)⟧') ≫ p⟦(1 : ℤ)⟧' = _
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, factorG]
    exact boundary
  obtain ⟨project₀, _, projectSquare₀⟩ := complete_distinguished_triangle_morphism₂ S' T
    newTriangle distinguished p e newBoundary
  let project : E' ⟶ T.obj₂ := project₀
  have projectSquare : q ≫ e = project ≫ T.mor₂ := projectSquare₀
  have sameQuotient : (lift ≫ project) ≫ T.mor₂ = f ≫ T.mor₂ := by
    rw [Category.assoc, ← projectSquare, ← Category.assoc, ← liftSquare, factor]
  obtain ⟨correction, correctionEq⟩ := T.coyoneda_exact₂ distinguished
    (f - lift ≫ project) (by rw [Preadditive.sub_comp, sameQuotient, sub_self])
  obtain ⟨F', hF', i', p', factorCorrection⟩ := left X hX correction
  have hsum : Q (E' ⊞ F') :=
    Q.ext_of_isTriangulatedClosed₂ _ (binaryBiproductTriangle_distinguished E' F') hE' hF'
  refine ⟨E' ⊞ F', hsum, biprod.lift lift i',
    biprod.desc project (p' ≫ T.mor₁), ?_⟩
  rw [biprod.lift_desc, ← Category.assoc, factorCorrection, ← correctionEq]
  rw [← add_sub_assoc, add_sub_cancel_left]

/-- Iterating the extension step gives the exact finite-stage
factorization used before extracting a compact retract from a telescope. -/
theorem factorizationTargets_extensionProductIter (B : ObjectProperty C)
    (base : B ≤ factorizationTargets P Q) (n : ℕ) :
    B.extensionProductIter n ≤ factorizationTargets P Q := by
  induction n with
  | zero => exact base
  | succ n ih =>
      intro Y hY
      rw [ObjectProperty.extensionProductIter_succ] at hY
      obtain ⟨L, R, a, b, c, triangle, hL, hR⟩ := hY
      exact factorizationTargets_extension P Q contained (Triangle.mk a b c)
        triangle (base L hL) (ih R hR)

omit contained

/-- If a source object is a retract of a finite stage, the finite
factorization turns it into a retract of a genuine object of `Q`. -/
theorem prop_of_retract_of_factorization [Q.IsStableUnderRetracts]
    {X Y : C} (hX : P X) (factor : factorizationTargets P Q Y) (retract : Retract X Y) :
    Q X := by
  obtain ⟨E, hE, i, p, eq⟩ := factor X hX retract.i
  apply Q.prop_of_retract (Y := E) ?_ hE
  exact
    { i := i
      r := p ≫ retract.r
      retract := by rw [← Category.assoc, eq, retract.retract] }

end ToricPower.CompactExtraction

end
