module

public import ToricPower.OpenClosedScalar
public import ToricPower.ModuleDirectSumComplex
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Every Laurent character as an actual scalar-support summand

For an arbitrary support predicate, its supported Laurent module is the
unrestricted direct sum of the scalar submodules supported at each
character. The isomorphism is the literal monomial insertion map. It is
natural for every inclusion of support predicates.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators

namespace ToricPower.MorseCoefficients

variable (k : Type) [CommRing k] {I : Type} (allowed : I → Prop)

abbrev LaurentSupport := Finsupp.supported k k {m : I | allowed m}

/-- Insertion of one character with its actual scalar support condition. -/
def scalarMonomial (m : I) : openScalar k (¬ allowed m) →ₗ[k]
    LaurentSupport k allowed where
  toFun a := ⟨Finsupp.single m a.val, by
    rw [Finsupp.mem_supported']
    intro w outside
    by_cases same : w = m
    · subst w
      simpa only [Finsupp.single_eq_same] using a.property outside
    · exact Finsupp.single_eq_of_ne same⟩
  map_add' a b := Subtype.ext (Finsupp.single_add _ _ _)
  map_smul' r a := Subtype.ext (Finsupp.smul_single r m a.val).symm

/-- Extraction uses the true support property of the Laurent polynomial. -/
def scalarCoefficient (m : I) : LaurentSupport k allowed →ₗ[k]
    openScalar k (¬ allowed m) where
  toFun p := ⟨p.val m, fun outside =>
    (Finsupp.mem_supported' k p.val).mp p.property m outside⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def scalarSum : (Π₀ m : I, openScalar k (¬ allowed m)) →ₗ[k]
    LaurentSupport k allowed :=
  DFinsupp.lsum k (scalarMonomial k allowed)

@[simp]
theorem scalarSum_single (m : I) (a : openScalar k (¬ allowed m)) :
    scalarSum k allowed (DFinsupp.single m a) = scalarMonomial k allowed m a :=
  DFinsupp.lsum_single (S := k) _ _ _

theorem scalarCoefficient_scalarSum (m : I)
    (p : Π₀ w : I, openScalar k (¬ allowed w)) :
    scalarCoefficient k allowed m (scalarSum k allowed p) = p m := by
  have h : (scalarCoefficient k allowed m).comp (scalarSum k allowed) =
      DFinsupp.lapply m := by
    apply DFinsupp.lhom_ext
    intro w a
    change scalarCoefficient k allowed m
      (scalarSum k allowed (DFinsupp.single w a)) = _
    rw [scalarSum_single]
    by_cases same : w = m
    · subst w
      rw [DFinsupp.lapply_apply, DFinsupp.single_eq_same]
      apply Subtype.ext
      exact Finsupp.single_eq_same
    · rw [DFinsupp.lapply_apply, DFinsupp.single_eq_of_ne (Ne.symm same)]
      apply Subtype.ext
      exact Finsupp.single_eq_of_ne (Ne.symm same)
  exact DFunLike.congr_fun h p

theorem scalarSum_bijective : Function.Bijective (scalarSum k allowed) := by
  constructor
  · intro p q h
    apply DFinsupp.ext
    intro m
    rw [← scalarCoefficient_scalarSum k allowed m p,
      ← scalarCoefficient_scalarSum k allowed m q,h]
  · intro p
    refine ⟨∑ m ∈ p.val.support,
      DFinsupp.single m (scalarCoefficient k allowed m p),?_⟩
    rw [map_sum]
    simp only [scalarSum_single]
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    exact Finsupp.sum_single p.val

/-- No finite character range is chosen: only each polynomial's own
finite support is used to construct the inverse. -/
def scalarSumLinearEquiv : (Π₀ m : I, openScalar k (¬ allowed m)) ≃ₗ[k]
    LaurentSupport k allowed :=
  LinearEquiv.ofBijective (scalarSum k allowed) (scalarSum_bijective k allowed)

section Diagrams

variable {C : Type} [Preorder C] (support : C → I → Prop)
  (upward : ∀ {c d : C}, c ≤ d → ∀ m, support c m → support d m)

/-- The literal character modules, with every actual face map. -/
def scalarSupportFamily : C ⥤ (Discrete I ⥤ ModuleCat k) where
  obj c := Discrete.functor (fun m => ModuleCat.of k (openScalar k (¬ support c m)))
  map f := Discrete.natTrans (fun m => ModuleCat.ofHom
    (openScalarMap k (fun absent present => absent (upward f.le m.as present))))
  map_id c := by
    ext m a
    rfl
  map_comp f g := by
    ext m a
    rfl

/-- Laurent polynomials map by literal inclusion, with their characters
and coefficients unchanged. -/
def laurentSupportDiagram : C ⥤ ModuleCat k where
  obj c := ModuleCat.of k (LaurentSupport k (support c))
  map f := ModuleCat.ofHom
    { toFun := fun p => ⟨p.val,fun m hm => upward f.le m (p.property hm)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id c := rfl
  map_comp f g := rfl

/-- The full character decomposition is natural for all face arrows,
before taking complexes or homology. -/
def scalarSupportSumIso :
    scalarSupportFamily k support upward ⋙ ModuleDirectSum.sumFunctor k ≅
      laurentSupportDiagram k support upward :=
  NatIso.ofComponents (fun c => (scalarSumLinearEquiv k (support c)).toModuleIso)
    (by
      intro c d f
      apply ModuleCat.hom_ext
      apply DFinsupp.lhom_ext
      intro m a
      change openScalar k (¬ support c m) at a
      change scalarSum k (support d)
        (DFinsupp.mapRange.linearMap (fun w : I =>
          openScalarMap k (p := ¬ support c w) (q := ¬ support d w)
            (fun absent present => absent (upward f.le w present)))
            (DFinsupp.single m a)) = _
      rw [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single,scalarSum_single]
      change _ = (laurentSupportDiagram k support upward).map f
        (scalarSum k (support c) (DFinsupp.single m a))
      rw [scalarSum_single]
      apply Subtype.ext
      rfl)

end Diagrams

end ToricPower.MorseCoefficients

end
