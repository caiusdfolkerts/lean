module

public import ToricPower.TriangularCoordinates
public import ToricPower.ComplexCoconeDifferential
public import ToricPower.MappingConeAcyclicCriterion

/-!
# Quasi-isomorphisms of finite triangular systems

The proof uses the actual mapping cone of the original map. Its finite
row coordinates are the mapping cones of the given row maps, with the
original signed cone differential. Thus rowwise quasi-isomorphisms
imply a quasi-isomorphism of the whole unbounded complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
open ToricPower.ComplexCone

namespace ToricPower.TriangularCoordinates

variable {k : Type} [CommRing k] {width : ℕ}
  {K L : CochainComplex (ModuleCat.{0} k) ℤ}
  (source : TriangularCoordinates width K) (target : TriangularCoordinates width L)
  (f : K ⟶ L) (rowMap : ∀ q : Fin width, source.row q ⟶ target.row q)

def coneProject (a : ℤ) (q : Fin width) :
    (mappingCone f).X a ⟶ (mappingCone (rowMap q)).X a :=
  ModuleCat.ofHom ((mappingConeModuleTermEquiv (rowMap q) a).symm.toLinearMap.comp
    (((source.project (a+1) q).hom.prodMap (target.project a q).hom).comp
      (mappingConeModuleTermEquiv f a).toLinearMap))

def coneInsert (a : ℤ) (q : Fin width) :
    (mappingCone (rowMap q)).X a ⟶ (mappingCone f).X a :=
  ModuleCat.ofHom ((mappingConeModuleTermEquiv f a).symm.toLinearMap.comp
    (((source.insert (a+1) q).hom.prodMap (target.insert a q).hom).comp
      (mappingConeModuleTermEquiv (rowMap q) a).toLinearMap))

theorem coneProject_coordinates (a : ℤ) (q : Fin width) (z : (mappingCone f).X a) :
    mappingConeModuleTermEquiv (rowMap q) a (coneProject source target f rowMap a q z) =
      (source.project (a+1) q (mappingConeModuleTermEquiv f a z).1,
        target.project a q (mappingConeModuleTermEquiv f a z).2) := by
  change (mappingConeModuleTermEquiv (rowMap q) a)
    ((mappingConeModuleTermEquiv (rowMap q) a).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem coneInsert_coordinates (a : ℤ) (q : Fin width)
    (z : (mappingCone (rowMap q)).X a) :
    mappingConeModuleTermEquiv f a (coneInsert source target f rowMap a q z) =
      (source.insert (a+1) q (mappingConeModuleTermEquiv (rowMap q) a z).1,
        target.insert a q (mappingConeModuleTermEquiv (rowMap q) a z).2) := by
  change (mappingConeModuleTermEquiv f a) ((mappingConeModuleTermEquiv f a).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

variable (compatible : ∀ (a : ℤ) (q : Fin width) (z : K.X a),
  target.project a q (f.f a z) = (rowMap q).f a (source.project a q z))

/-- The cone keeps every row and both original summands in every
integer degree; there is no bounded-coefficient replacement. -/
def cone : TriangularCoordinates width (mappingCone f) where
  row q := mappingCone (rowMap q)
  project := coneProject source target f rowMap
  insert := coneInsert source target f rowMap
  diagonal := by
    intro a q z lower
    have lowerSource (p : Fin width) (hp : p.val < q.val) :
        source.project (a+1) p (mappingConeModuleTermEquiv f a z).1 = 0 := by
      have h := congrArg (mappingConeModuleTermEquiv (rowMap p) a) (lower p hp)
      rw [coneProject_coordinates,map_zero] at h
      exact congrArg Prod.fst h
    have lowerTarget (p : Fin width) (hp : p.val < q.val) :
        target.project a p (mappingConeModuleTermEquiv f a z).2 = 0 := by
      have h := congrArg (mappingConeModuleTermEquiv (rowMap p) a) (lower p hp)
      rw [coneProject_coordinates,map_zero] at h
      exact congrArg Prod.snd h
    apply (mappingConeModuleTermEquiv (rowMap q) (a+1)).injective
    rw [coneProject_coordinates,mappingConeModuleTermEquiv_d,
      mappingConeModuleTermEquiv_d,coneProject_coordinates]
    apply Prod.ext
    · change source.project (a+1+1) q
        (-(K.d (a+1) (a+1+1) (mappingConeModuleTermEquiv f a z).1)) = _
      rw [map_neg,source.diagonal (a+1) q _ lowerSource]
    · change target.project (a+1) q
        (f.f (a+1) (mappingConeModuleTermEquiv f a z).1 +
          L.d a (a+1) (mappingConeModuleTermEquiv f a z).2) = _
      rw [map_add,compatible,target.diagonal a q _ lowerTarget]
  project_insert := by
    intro a q z
    apply (mappingConeModuleTermEquiv (rowMap q) a).injective
    rw [coneProject_coordinates,coneInsert_coordinates]
    simp only [source.project_insert,target.project_insert]
  project_insert_lower := by
    intro a p q lower z
    apply (mappingConeModuleTermEquiv (rowMap p) a).injective
    rw [coneProject_coordinates,coneInsert_coordinates,map_zero]
    simp only [source.project_insert_lower (a+1) p q lower,
      target.project_insert_lower a p q lower]
    rfl
  jointlyInjective := by
    intro a x y same
    have coordinate (q : Fin width) :=
      congrArg (mappingConeModuleTermEquiv (rowMap q) a) (congrFun same q)
    simp only [coneProject_coordinates] at coordinate
    apply (mappingConeModuleTermEquiv f a).injective
    apply Prod.ext
    · apply source.jointlyInjective (a+1)
      funext q
      exact congrArg Prod.fst (coordinate q)
    · apply target.jointlyInjective a
      funext q
      exact congrArg Prod.snd (coordinate q)

include compatible in
/-- Finitely many genuine row quasi-isomorphisms imply that the
original map is a quasi-isomorphism on the full total complex. -/
theorem quasiIso (rowQuasiIso : ∀ q : Fin width, QuasiIso (rowMap q)) : QuasiIso f := by
  apply (quasiIso_iff_mappingCone_acyclic f).mpr
  apply (cone source target f rowMap compatible).acyclic
  intro q
  exact (quasiIso_iff_mappingCone_acyclic (rowMap q)).mp (rowQuasiIso q)

end ToricPower.TriangularCoordinates

end
