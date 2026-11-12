module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual coproducts of complexes and their homotopies

The coproduct complex is defined degree by degree using the actual
categorical coproducts. A family of homotopies out of its summands
assembles into one homotopy. Consequently arbitrary coproducts of
K-projective cochain complexes are K-projective.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.CoproductComplex

universe u v w w'
variable {A : Type u} [Category.{v} A] [Preadditive A] [HasCoproducts.{w} A]
  {J : Type w'} {shape : ComplexShape J} {I : Type w}

def obj (K : I → HomologicalComplex A shape) : HomologicalComplex A shape where
  X n := ∐ fun i => (K i).X n
  d n m := Sigma.desc (fun i => (K i).d n m ≫ Sigma.ι (fun i => (K i).X m) i)
  shape n m noRelation := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, (K i).shape n m noRelation, zero_comp, comp_zero]
  d_comp_d' n m l _ _ := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc,
      (K i).d_comp_d_assoc, zero_comp, comp_zero]

def ι (K : I → HomologicalComplex A shape) (i : I) : K i ⟶ obj K where
  f n := Sigma.ι (fun i => (K i).X n) i
  comm' n m _ := by
    simp only [obj, Sigma.ι_comp_desc]

@[simp]
theorem ι_f (K : I → HomologicalComplex A shape) (i : I) (n : J) :
    (ι K i).f n = Sigma.ι (fun i => (K i).X n) i := rfl

@[reassoc (attr := simp)]
theorem ι_d (K : I → HomologicalComplex A shape) (i : I) (n m : J) :
    Sigma.ι (fun i => (K i).X n) i ≫ (obj K).d n m =
      (K i).d n m ≫ Sigma.ι (fun i => (K i).X m) i :=
  Sigma.ι_comp_desc _ _

def desc (K : I → HomologicalComplex A shape) {L : HomologicalComplex A shape}
    (maps : ∀ i, K i ⟶ L) : obj K ⟶ L where
  f n := Sigma.desc (fun i => (maps i).f n)
  comm' n m _ := by
    apply Sigma.hom_ext
    intro i
    simp only [ι_d_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    exact (maps i).comm n m

@[reassoc (attr := simp)]
theorem ι_desc (K : I → HomologicalComplex A shape) {L : HomologicalComplex A shape}
    (maps : ∀ i, K i ⟶ L) (i : I) : ι K i ≫ desc K maps = maps i := by
  ext n
  exact Sigma.ι_comp_desc _ _

theorem hom_ext (K : I → HomologicalComplex A shape) {L : HomologicalComplex A shape}
    {f g : obj K ⟶ L} (same : ∀ i, ι K i ≫ f = ι K i ≫ g) : f = g := by
  ext n
  apply Sigma.hom_ext
  intro i
  exact congrArg (fun h => h.f n) (same i)

/-- Homotopies on all the summands assemble into a genuine homotopy
on the actual coproduct complex. -/
def homotopyDesc (K : I → HomologicalComplex A shape) {L : HomologicalComplex A shape}
    (f g : obj K ⟶ L) (homotopies : ∀ i, Homotopy (ι K i ≫ f) (ι K i ≫ g)) :
    Homotopy f g where
  hom n m := Sigma.desc (fun i => (homotopies i).hom n m)
  zero n m noRelation := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, (homotopies i).zero n m noRelation, comp_zero]
  comm n := by
    apply Sigma.hom_ext
    intro i
    have equation := (homotopies i).comm n
    let H : ∀ n m, (obj K).X n ⟶ L.X m :=
      fun n m => Sigma.desc (fun i => (homotopies i).hom n m)
    change Sigma.ι (fun i => (K i).X n) i ≫ f.f n =
      Sigma.ι (fun i => (K i).X n) i ≫
        ((obj K).d n (shape.next n) ≫ H (shape.next n) n +
        H n (shape.prev n) ≫ L.d (shape.prev n) n + g.f n)
    change Sigma.ι (fun i => (K i).X n) i ≫ f.f n =
      (K i).d n (shape.next n) ≫ (homotopies i).hom (shape.next n) n +
        (homotopies i).hom n (shape.prev n) ≫ L.d (shape.prev n) n +
        Sigma.ι (fun i => (K i).X n) i ≫ g.f n at equation
    simpa only [H, Preadditive.comp_add, Category.assoc, ι_d_assoc,
      Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, HomologicalComplex.comp_f, ι_f]
      using equation

variable {B : Type u} [Category.{v} B] [Abelian B] [HasCoproducts.{w} B]

theorem isKProjective (K : I → CochainComplex B ℤ) [∀ i, (K i).IsKProjective] :
    CochainComplex.IsKProjective (obj K) where
  nonempty_homotopy_zero {L} f acyclic := by
    refine ⟨homotopyDesc K f 0 (fun i => ?_)⟩
    simpa only [comp_zero] using
      CochainComplex.IsKProjective.homotopyZero (ι K i ≫ f) acyclic

end ToricPower.CoproductComplex

end

