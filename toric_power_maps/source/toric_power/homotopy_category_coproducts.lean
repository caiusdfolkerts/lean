module

public import ToricPower.HomologicalCoproductHomotopy

/-!
# Actual coproducts in the homotopy category

Degreewise coproducts of complexes represent coproducts of their homotopy
classes. The uniqueness argument assembles a family of homotopies; it
does not infer equality of chain maps from equality in the quotient.
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

def homotopyCofan (K : I → HomologicalComplex A shape) :
    Cofan (fun i => (HomotopyCategory.quotient A shape).obj (K i)) :=
  Cofan.mk ((HomotopyCategory.quotient A shape).obj (obj K))
    (fun i => (HomotopyCategory.quotient A shape).map (ι K i))

theorem homotopy_hom_ext (K : I → HomologicalComplex A shape)
    {L : HomotopyCategory A shape}
    {f g : (HomotopyCategory.quotient A shape).obj (obj K) ⟶ L}
    (same : ∀ i, (HomotopyCategory.quotient A shape).map (ι K i) ≫ f =
      (HomotopyCategory.quotient A shape).map (ι K i) ≫ g) : f = g := by
  have homotopy : Homotopy f.out g.out := homotopyDesc K f.out g.out (fun i => by
    apply HomotopyCategory.homotopyOfEq
    simpa only [CategoryTheory.Functor.map_comp, HomotopyCategory.quotient_map_out]
      using same i)
  simpa only [HomotopyCategory.quotient_map_out] using
    HomotopyCategory.eq_of_homotopy f.out g.out homotopy

def homotopyIsColimit (K : I → HomologicalComplex A shape) :
    IsColimit (homotopyCofan K) :=
  Cofan.IsColimit.mk _
    (fun s => (HomotopyCategory.quotient A shape).map
      (desc K (fun i => (s.inj i).out)))
    (fun s i => by
      change (HomotopyCategory.quotient A shape).map (ι K i) ≫
        (HomotopyCategory.quotient A shape).map (desc K (fun j => (s.inj j).out)) = _
      rw [← CategoryTheory.Functor.map_comp, ι_desc, HomotopyCategory.quotient_map_out])
    (fun s m same => by
      apply homotopy_hom_ext K
      intro i
      rw [← CategoryTheory.Functor.map_comp, ι_desc, HomotopyCategory.quotient_map_out]
      exact same i)

/-- All actual coproducts of homotopy classes exist whenever the
coefficient category has coproducts of the same indexing size. -/
theorem homotopy_hasCoproducts : HasCoproducts.{w} (HomotopyCategory A shape) := by
  apply hasCoproducts_of_colimit_cofans
    (fun {I : Type w} (family : I → HomotopyCategory A shape) =>
      homotopyCofan (fun i : I => (family i).as))
  intro I family
  exact homotopyIsColimit (fun i : I => (family i).as)

end ToricPower.CoproductComplex

end

