module

public import PaperVerification.ToricTorusAction
public import Mathlib.AlgebraicGeometry.Group.Affine

@[expose] public section

/-!
# Comorphisms of actual affine torus actions

The coaction of an arbitrary affine torus scheme is extracted from its
actual action morphism by the fully faithful affine Spec functor and
the proved tensor-product/fiber-product isomorphism. Equivariance of
actual scheme maps implies the corresponding algebraic coaction equation.
-/

noncomputable section

universe u v

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory MonObj
open scoped TensorProduct

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).Monoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).LaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).OplaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toOplaxMonoidal

variable (k : Type (max u v)) [CommRing k] (M : Type v) [AddCommGroup M]

local notation "F" => (algSpec (CommRingCat.of k) :
  (CommAlgCat k)ᵒᵖ ⥤ Over (Spec (CommRingCat.of k)))
local notation "T" => op (CommAlgCat.of k (AddMonoidAlgebra k M))
local notation "G" => splitTorusOver k M

/-- The actual semigroup action, on the literally bundled affine Spec object. -/
instance semigroupChart_algSpec_torusAction (S : AddSubmonoid M) :
    ModObj G ((F).obj (op (CommAlgCat.of k (AddMonoidAlgebra k S)))) := by
  change ModObj G (semigroupChartOver k S)
  exact semigroupChart_torusAction k S

def affineTorusActionArrow (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] : T⊗op B⟶op B :=
  (algSpec.fullyFaithful (R:=CommRingCat.of k)).preimage
    (Functor.OplaxMonoidal.δ F T (op B)≫γ[G,(F).obj (op B)])

@[simp] theorem affineTorusActionArrow_spec (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] :
    (F).map (affineTorusActionArrow k M B)=
      Functor.OplaxMonoidal.δ F T (op B)≫γ[G,(F).obj (op B)] :=
  (algSpec.fullyFaithful (R:=CommRingCat.of k)).map_preimage _

/-- The literal algebra comorphism of the given action. -/
def affineTorusActionCoaction (B : CommAlgCat.{max u v} k)
    [ModObj G ((F).obj (op B))] :
    B→ₐ[k]AddMonoidAlgebra k M⊗[k]B :=
  (affineTorusActionArrow k M B).unop.hom

theorem affineTorusActionArrow_natural {B C : CommAlgCat.{max u v} k}
    [ModObj G ((F).obj (op B))] [ModObj G ((F).obj (op C))]
    (f : op B⟶op C) [IsModHom G ((F).map f)] :
    affineTorusActionArrow k M B≫f=
      (T◁f)≫affineTorusActionArrow k M C := by
  let a : (F).obj T ⊗ (F).obj (op B) ⟶ (F).obj (op B) := γ[G,(F).obj (op B)]
  let b : (F).obj T ⊗ (F).obj (op C) ⟶ (F).obj (op C) := γ[G,(F).obj (op C)]
  have ha : (F).map (affineTorusActionArrow k M B) =
      Functor.OplaxMonoidal.δ F T (op B) ≫ a := affineTorusActionArrow_spec k M B
  have hb : (F).map (affineTorusActionArrow k M C) =
      Functor.OplaxMonoidal.δ F T (op C) ≫ b := affineTorusActionArrow_spec k M C
  have heq : a ≫ (F).map f = ((F).obj T ◁ (F).map f) ≫ b :=
    IsModHom.smul_hom (A := G) (f := (F).map f)
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  calc
    (F).map (affineTorusActionArrow k M B ≫ f) =
        (F).map (affineTorusActionArrow k M B) ≫ (F).map f := (F).map_comp _ _
    _ = (Functor.OplaxMonoidal.δ F T (op B) ≫ a) ≫ (F).map f :=
      congrArg (fun g : (F).obj (T ⊗ op B) ⟶ (F).obj (op B) => g ≫ (F).map f) ha
    _ = Functor.OplaxMonoidal.δ F T (op B) ≫ (a ≫ (F).map f) := Category.assoc _ _ _
    _ = Functor.OplaxMonoidal.δ F T (op B) ≫ (((F).obj T ◁ (F).map f) ≫ b) :=
      congrArg (fun g : (F).obj T ⊗ (F).obj (op B) ⟶ (F).obj (op C) =>
        Functor.OplaxMonoidal.δ F T (op B) ≫ g) heq
    _ = (Functor.OplaxMonoidal.δ F T (op B) ≫ ((F).obj T ◁ (F).map f)) ≫ b :=
      (Category.assoc _ _ _).symm
    _ = ((F).map (T ◁ f) ≫ Functor.OplaxMonoidal.δ F T (op C)) ≫ b :=
      congrArg (fun g : (F).obj (T ⊗ op B) ⟶ (F).obj T ⊗ (F).obj (op C) => g ≫ b)
        (Functor.OplaxMonoidal.δ_natural_right F T f)
    _ = (F).map (T ◁ f) ≫ (Functor.OplaxMonoidal.δ F T (op C) ≫ b) :=
      Category.assoc _ _ _
    _ = (F).map (T ◁ f) ≫ (F).map (affineTorusActionArrow k M C) :=
      congrArg (fun g : (F).obj (T ⊗ op C) ⟶ (F).obj (op C) => (F).map (T ◁ f) ≫ g) hb.symm
    _ = (F).map ((T ◁ f) ≫ affineTorusActionArrow k M C) := ((F).map_comp _ _).symm

/-- Naturality is obtained from actual equivariance, for arbitrary
affine actions on the source and target. -/
theorem affineTorusActionCoaction_natural {B C : CommAlgCat.{max u v} k}
    [ModObj G ((F).obj (op B))] [ModObj G ((F).obj (op C))]
    (q : C→ₐ[k]B) [IsModHom G ((F).map (CommAlgCat.ofHom q).op)] :
    (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q).comp
        (affineTorusActionCoaction k M C)=
      (affineTorusActionCoaction k M B).comp q := by
  have h := congrArg (fun f : T⊗op B⟶op C=>f.unop.hom)
    (affineTorusActionArrow_natural k M (CommAlgCat.ofHom q).op)
  exact h.symm

theorem affineTorusActionCoaction_semigroup (S : AddSubmonoid M) :
    affineTorusActionCoaction k M (CommAlgCat.of k (AddMonoidAlgebra k S))=
      semigroupChartCoaction k S := by
  have h : affineTorusActionArrow k M (CommAlgCat.of k (AddMonoidAlgebra k S))=
      (CommAlgCat.ofHom (semigroupChartCoaction k S)).op := by
    apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    rw [affineTorusActionArrow_spec]
    apply Over.OverMorphism.ext
    change (pullbackSpecIso (CommRingCat.of k)
        (CommRingCat.of (AddMonoidAlgebra k M))
        (CommRingCat.of (AddMonoidAlgebra k S))).inv≫
      (γ[G,semigroupChartOver k S]).left=
        Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom)
    rw [semigroupChart_action_spec]
    exact (pullbackSpecIso (CommRingCat.of k)
      (CommRingCat.of (AddMonoidAlgebra k M))
      (CommRingCat.of (AddMonoidAlgebra k S))).inv_hom_id_assoc
        (Spec.map (CommRingCat.ofHom (semigroupChartCoaction k S).toRingHom))
  exact congrArg (fun f=>f.unop.hom) h

/-- Vanishing in an actual equivariant affine quotient is preserved by
the true semigroup coaction after applying that quotient in the second
factor. No character-stability hypothesis appears. -/
theorem semigroupCoaction_quotient_zero (S : AddSubmonoid M)
    (B : CommAlgCat.{max u v} k) [ModObj G ((F).obj (op B))]
    (q : AddMonoidAlgebra k S→ₐ[k]B)
    [IsModHom G ((F).map (CommAlgCat.ofHom q).op)]
    {f : AddMonoidAlgebra k S} (hf : q f=0) :
    Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M)) q
      (semigroupChartCoaction k S f)=0 := by
  have h := congrArg
    (fun φ : AddMonoidAlgebra k S →ₐ[k] AddMonoidAlgebra k M ⊗[k] B => φ f)
    (affineTorusActionCoaction_natural k M
      (B := B) (C := CommAlgCat.of k (AddMonoidAlgebra k S)) q)
  rw [affineTorusActionCoaction_semigroup] at h
  simpa only [AlgHom.comp_apply,hf,map_zero] using h

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.semigroupCoaction_quotient_zero
