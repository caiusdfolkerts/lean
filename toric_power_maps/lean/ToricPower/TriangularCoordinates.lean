module

public import ToricPower.FiniteTwistedTotal

/-! # Finite triangular coordinates on actual module complexes -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

variable {k : Type} [CommRing k] (width : ℕ)
  (K : CochainComplex (ModuleCat.{0} k) ℤ)

/-- Coordinates retain their original row complexes and the actual
projection/insertion maps. Exactness is a conclusion, not a field. -/
structure TriangularCoordinates where
  row : Fin width → CochainComplex (ModuleCat.{0} k) ℤ
  project : ∀ (a : ℤ) (q : Fin width), K.X a ⟶ (row q).X a
  insert : ∀ (a : ℤ) (q : Fin width), (row q).X a ⟶ K.X a
  diagonal : HasTriangularDifferential K row project
  project_insert : ∀ (a : ℤ) (q : Fin width) (z : (row q).X a),
    project a q (insert a q z) = z
  project_insert_lower : ∀ (a : ℤ) (p q : Fin width), p.val < q.val →
    ∀ z : (row q).X a, project a p (insert a q z) = 0
  jointlyInjective : ∀ a : ℤ,
    Function.Injective (fun z : K.X a => fun q : Fin width => project a q z)

namespace TriangularCoordinates

variable {width K}

theorem acyclic (coordinates : TriangularCoordinates width K)
    (exactRows : ∀ q : Fin width, (coordinates.row q).Acyclic) : K.Acyclic :=
  finiteTriangular_acyclic K coordinates.row coordinates.project coordinates.insert
    coordinates.diagonal coordinates.project_insert coordinates.project_insert_lower
    coordinates.jointlyInjective exactRows

end TriangularCoordinates

namespace FiniteTotal

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {width : ℕ} (row : Fin width → CochainComplex C ℤ)
  (off : ∀ a : ℤ, term row a ⟶ term row (a+1))
  (coherent : Coherent row off) (raises : StrictlyRaises row off)
  (F : C ⥤ ModuleCat.{0} k) [F.Additive]

/-- These are the literal biproduct coordinates of the actual total
complex after the specified additive functor. -/
def mappedCoordinates :
    TriangularCoordinates width
      ((F.mapHomologicalComplex (.up ℤ)).obj (complex row off coherent)) where
  row q := (F.mapHomologicalComplex (.up ℤ)).obj (row q)
  project a q := F.map (biproduct.π (fun q : Fin width => (row q).X a) q)
  insert a q := F.map (biproduct.ι (fun q : Fin width => (row q).X a) q)
  diagonal := by
    intro a q z lower
    change F.map (biproduct.π (fun q : Fin width => (row q).X (a+1)) q)
      (F.map (CochainComplex.of.d (term row) (differential row off) a (a+1)) z) = _
    rw [CochainComplex.of_d]
    have h := congrArg (fun f : term row a ⟶ (row q).X (a+1) => F.map f z)
      (biproduct.map_π (fun q : Fin width => (row q).d a (a+1)) q)
    simp only [F.map_comp,ModuleCat.comp_apply] at h
    simp only [differential,F.map_add,ModuleCat.hom_add,LinearMap.add_apply,map_add]
    rw [mapped_off_zero row off F raises a q z lower,add_zero]
    exact h
  project_insert := mapped_insert_self row F
  project_insert_lower := mapped_insert_lower row F
  jointlyInjective := mapped_projections_injective row F

end FiniteTotal

end ToricPower

end
