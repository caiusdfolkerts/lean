module

public import ToricPower.ModuleDirectSumComplex
public import Mathlib.Data.Finsupp.ToDFinsupp

/-! # Unrestricted direct sums of actual chain complexes

The exact dependent-finitely-supported sum functor is applied to the
literal family of chain complexes. The displayed coordinates retain
all summands and their original differentials.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleChainDirectSum

variable (k : Type) [CommRing k] {U : Type}
  (K : U → ChainComplex (ModuleCat.{0} k) ℕ)

def familyComplex : ChainComplex (Discrete U ⥤ ModuleCat.{0} k) ℕ where
  X q := Discrete.functor (fun u => (K u).X q)
  d p q := Discrete.natTrans (fun u => (K u.as).d p q)
  shape p q unrelated := by
    ext u x
    exact ConcreteCategory.congr_hom ((K u.as).shape p q unrelated) x
  d_comp_d' p q r _ _ := by
    ext u x
    exact ConcreteCategory.congr_hom ((K u.as).d_comp_d p q r) x

def complex : ChainComplex (ModuleCat.{0} k) ℕ :=
  ((ModuleDirectSum.sumFunctor k).mapHomologicalComplex (.down ℕ)).obj
    (familyComplex k K)

def familyEvaluationIso (u : U) :
    ((((evaluation (Discrete U) (ModuleCat k)).obj ⟨u⟩).mapHomologicalComplex
      (.down ℕ)).obj (familyComplex k K)) ≅ K u :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun _ _ _ => by simp [familyComplex])

def familyHomologyIso (q : ℕ) :
    (familyComplex k K).homology q ≅ Discrete.functor (fun u => (K u).homology q) :=
  Discrete.natIso (fun u =>
    (((familyComplex k K).sc q).mapHomologyIso
      ((evaluation (Discrete U) (ModuleCat k)).obj u)).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat k) (.down ℕ) q).mapIso
        (familyEvaluationIso k K u.as))

def homologyIso (q : ℕ) :
    (complex k K).homology q ≅ ModuleCat.of k (Π₀ u : U, (K u).homology q) :=
  ((familyComplex k K).sc q).mapHomologyIso (ModuleDirectSum.sumFunctor k) ≪≫
    (ModuleDirectSum.sumFunctor k).mapIso (familyHomologyIso k K q)

def inclusion (u : U) : K u ⟶ complex k K where
  f q := ModuleCat.ofHom (DFinsupp.lsingle (R := k) (M := fun v : U => ↑((K v).X q)) u)
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DFinsupp.mapRange.linearMap (fun v : U => ((K v).d p q).hom)
      (DFinsupp.single u x) = DFinsupp.single u ((K u).d p q x)
    simp only [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single]

variable (I : U → ℕ → Type) (e : ∀ u q, (K u).X q ≃ₗ[k] (I u q →₀ k))

def coordinates (q : ℕ) :
    (complex k K).X q ≃ₗ[k] ((Σ u : U, I u q) →₀ k) :=
  (DFinsupp.mapRange.linearEquiv (fun u : U => e u q)).trans
    (sigmaFinsuppLequivDFinsupp k).symm

theorem coordinates_apply (q : ℕ) (x : Π₀ v : U, (K v).X q) (u : U) (i : I u q) :
    coordinates k K I e q x ⟨u,i⟩ = e u q (x u) i := rfl

theorem coordinates_symm_single [DecidableEq U] (q : ℕ) (u : U) (i : I u q) (r : k) :
    (coordinates k K I e q).symm (Finsupp.single ⟨u,i⟩ r) =
      DFinsupp.single u ((e u q).symm (Finsupp.single i r)) := by
  change (DFinsupp.mapRange.linearEquiv (fun v => e v q)).symm
    (sigmaFinsuppEquivDFinsupp (Finsupp.single ⟨u,i⟩ r)) = _
  rw [sigmaFinsuppEquivDFinsupp_single,DFinsupp.mapRange.linearEquiv_symm]
  simp only [DFinsupp.mapRange.linearEquiv_apply,DFinsupp.mapRange_single]

omit I e in
theorem differential_single [DecidableEq U] (p q : ℕ) (u : U) (x : (K u).X p) :
    (complex k K).d p q (DFinsupp.single u x) =
      DFinsupp.single u ((K u).d p q x) := by
  change DFinsupp.mapRange.linearMap (fun v : U => ((K v).d p q).hom)
    (DFinsupp.single u x) = _
  simp only [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single]

theorem coordinates_d_single_self (p q : ℕ) (u : U)
    (i : I u p) (j : I u q) (r : k) :
    coordinates k K I e q ((complex k K).d p q
      ((coordinates k K I e p).symm (Finsupp.single ⟨u,i⟩ r))) ⟨u,j⟩ =
        e u q ((K u).d p q ((e u p).symm (Finsupp.single i r))) j := by
  rw [coordinates_symm_single,differential_single,coordinates_apply]
  exact congrArg (fun x => e u q x j) DFinsupp.single_eq_same

theorem coordinates_d_single_ne (p q : ℕ) (u v : U) (different : v ≠ u)
    (i : I u p) (j : I v q) (r : k) :
    coordinates k K I e q ((complex k K).d p q
      ((coordinates k K I e p).symm (Finsupp.single ⟨u,i⟩ r))) ⟨v,j⟩ = 0 := by
  rw [coordinates_symm_single,differential_single,coordinates_apply]
  change e v q
    ((DFinsupp.single u ((K u).d p q ((e u p).symm (Finsupp.single i r))) :
      Π₀ t : U, (K t).X q) v) j = 0
  rw [DFinsupp.single_eq_of_ne different,map_zero,Finsupp.zero_apply]

end ToricPower.ModuleChainDirectSum

namespace ToricPower

def chainIsoOfFreeCoordinates (k : Type) [CommRing k]
    (K L : ChainComplex (ModuleCat.{0} k) ℕ) (I : ℕ → Type)
    (first : ∀ q, K.X q ≃ₗ[k] (I q →₀ k))
    (second : ∀ q, L.X q ≃ₗ[k] (I q →₀ k))
    (same : ∀ (q : ℕ) (i : I (q+1)) (r : k),
      first q (K.d (q+1) q ((first (q+1)).symm (Finsupp.single i r))) =
        second q (L.d (q+1) q ((second (q+1)).symm (Finsupp.single i r)))) : K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => ((first q).trans (second q).symm).toModuleIso) (by
      intro p q relation
      obtain rfl : q+1 = p := relation
      have maps :
          (first q).toLinearMap.comp ((K.d (q+1) q).hom.comp (first (q+1)).symm.toLinearMap) =
        (second q).toLinearMap.comp ((L.d (q+1) q).hom.comp (second (q+1)).symm.toLinearMap) :=
          Finsupp.lhom_ext (same q)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (second q).injective
      change second q (L.d (q+1) q ((second (q+1)).symm (first (q+1) x))) =
        second q ((second q).symm (first q (K.d (q+1) q x)))
      rw [LinearEquiv.apply_symm_apply]
      have value := DFunLike.congr_fun maps (first (q+1) x)
      simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
        using value.symm)

end ToricPower

end
