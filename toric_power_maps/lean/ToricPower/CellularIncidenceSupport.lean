module

public import ToricPower.CellularDependency08

/-! # Geometric support of actual cellular incidence coefficients

The coefficient is proved to vanish when the attaching map misses an
interior point of the target cell. The proof uses the actual local-degree
description and the exact sequence of the complement pair. No support
condition on an abstract matrix is assumed.

Candidate until an ordinary successful compiler record is available.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex

universe u

namespace ToricPower

variable {X : Type u} [TopologicalSpace X] [T2Space X] {D : Set X}
  (C : Set X) [RelCWComplex C D] (R : Type u) [Ring R]

/-- An attaching map missing a point contributes zero to the relative
homology at that point. This is the actual map of the actual spaces. -/
theorem attaching_homology_local_zero {n : ℕ}
    (x : TauCeti.skeletonObj C (n + 1))
    (j : cell C (n + 1))
    (hmiss : ∀ z, TauCeti.cellAttachingMap C j z ≠ x) :
    SSet.homologyMap (TopCat.toSSet.map (TauCeti.cellAttachingMap C j))
        (ModuleCat.of R R) n ≫
      (TopPair.ofSubset ({x}ᶜ : Set (TauCeti.skeletonObj C (n + 1)))).singularHomologyπ
        (ModuleCat.of R R) n = 0 := by
  let P := TopPair.ofSubset ({x}ᶜ : Set (TauCeti.skeletonObj C (n + 1)))
  let g : TopCat.diskBoundary.{u} (n + 1) ⟶ P.snd :=
    TopCat.ofHom ⟨fun z => ⟨TauCeti.cellAttachingMap C j z, hmiss z⟩,
      (TauCeti.cellAttachingMap C j).hom.continuous.subtype_mk _⟩
  have hfac : g ≫ P.map = TauCeti.cellAttachingMap C j := by
    ext z
    rfl
  change SSet.homologyMap (TopCat.toSSet.map (TauCeti.cellAttachingMap C j))
    (ModuleCat.of R R) n ≫ P.singularHomologyπ (ModuleCat.of R R) n = 0
  rw [← hfac, Functor.map_comp, SSet.homologyMap_comp, Category.assoc,
    P.homologyMap_comp_singularHomologyπ, comp_zero]

/-- The incidence coefficient is zero whenever the attaching map misses an
actual point in the open target cell. -/
theorem cellularIncidence_eq_zero_of_attaching_misses {n : ℕ} {i : cell C n}
    (x : TauCeti.skeletonObj C (n + 1))
    (hx : (x : X) ∈ openCell n i) (j : cell C (n + 1))
    (hmiss : ∀ z, TauCeti.cellAttachingMap C j z ≠ x) :
    TauCeti.cellularIncidence C R n i j = 0 := by
  rw [TauCeti.cellularIncidence_eq_inv_cellLocalClass C R x hx j]
  have hzero := attaching_homology_local_zero C R x j hmiss
  have h := ConcreteCategory.congr_hom hzero
    (((TauCeti.reducedSingularHomologyι (ModuleCat.of R R) n).app
      (TopCat.diskBoundary.{u} (n + 1)))
      ((TauCeti.reducedSingularHomologyTopCatSphereIso (ModuleCat.of R R) n).inv 1))
  simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at h
  exact (congrArg (fun z => (inv (TauCeti.cellLocalClass C
    (ModuleCat.of R R) x hx)).hom z) h).trans (map_zero _)

end ToricPower
