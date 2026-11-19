module

public import ToricPower.ModuleChainDirectSum
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Single

/-! # Actual maps and single objects in unrestricted chain sums

The exact dependent-finitely-supported sum preserves the original
component maps and their quasi-isomorphisms. No restriction is imposed
on the component index set.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleChainDirectSum

variable (k : Type) [CommRing k] {U : Type}
  {K L : U → ChainComplex (ModuleCat.{0} k) ℕ}

def familyMap (f : ∀ u, K u ⟶ L u) : familyComplex k K ⟶ familyComplex k L where
  f q := Discrete.natTrans (fun u => (f u.as).f q)
  comm' p q rel := by
    apply NatTrans.ext
    funext u
    exact (f u.as).comm p q

def map (f : ∀ u, K u ⟶ L u) : complex k K ⟶ complex k L :=
  ((ModuleDirectSum.sumFunctor k).mapHomologicalComplex (.down ℕ)).map (familyMap k f)

instance map_quasiIso (f : ∀ u, K u ⟶ L u) [∀ u, QuasiIso (f u)] :
    QuasiIso (map k f) := by
  haveI : QuasiIso (familyMap k f) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro u
    change QuasiIso (f u.as)
    infer_instance
  unfold map
  infer_instance

theorem map_single [DecidableEq U] (f : ∀ u, K u ⟶ L u) (q : ℕ) (u : U) (x : (K u).X q) :
    (map k f).f q (DFinsupp.single u x) = DFinsupp.single u ((f u).f q x) := by
  change DFinsupp.mapRange.linearMap (fun v : U => ((f v).f q).hom)
    (DFinsupp.single u x) = _
  simp only [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single]

variable (M : U → ModuleCat.{0} k)

theorem singleSum_isZero_X_succ (q : ℕ) :
    IsZero ((complex k (fun u => (ChainComplex.single₀ (ModuleCat k)).obj (M u))).X (q+1)) := by
  letI (u : U) : Subsingleton (((ChainComplex.single₀ (ModuleCat k)).obj (M u)).X (q+1)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 (M u) (q+1) (by omega))
  change IsZero (ModuleCat.of k
    (Π₀ u : U, (((ChainComplex.single₀ (ModuleCat k)).obj (M u)).X (q+1))))
  exact ModuleCat.isZero_of_subsingleton _

def singleSumTermIso (q : ℕ) :
    (complex k (fun u => (ChainComplex.single₀ (ModuleCat k)).obj (M u))).X q ≅
      ((ChainComplex.single₀ (ModuleCat k)).obj (ModuleCat.of k (Π₀ u : U, M u))).X q := by
  cases q with
  | zero => exact Iso.refl _
  | succ q =>
    exact IsZero.iso (singleSum_isZero_X_succ k M q)
      (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0
        (ModuleCat.of k (Π₀ u : U, M u)) (q+1) (by omega))

def singleSumIso :
    complex k (fun u => (ChainComplex.single₀ (ModuleCat k)).obj (M u)) ≅
      (ChainComplex.single₀ (ModuleCat k)).obj (ModuleCat.of k (Π₀ u : U, M u)) :=
  HomologicalComplex.Hom.isoOfComponents (singleSumTermIso k M)
    (by
      intro p q related
      obtain rfl : q+1=p := related
      exact (singleSum_isZero_X_succ k M q).eq_of_src _ _)

theorem singleSumIso_f_zero : (singleSumIso k M).hom.f 0 = 𝟙 _ := rfl

end ToricPower.ModuleChainDirectSum

end

