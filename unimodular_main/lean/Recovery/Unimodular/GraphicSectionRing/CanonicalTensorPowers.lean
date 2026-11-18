module

public import Recovery.Unimodular.GraphicSectionRing.SectionRingTensorProducts
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal

/-!
# Independent canonical multiplication of ordinary tensor powers

The associator and right unitor are those of the standard monoidal category
of sheaves of modules. The explicit sheafification tensor used by the toric
dictionary is compared with it through the proved tensorUnderlyingIso.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.GraphicSectionRing.CanonicalPowers

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open PaperVerification.ToricSchemes
open scoped TensorProduct

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.Modules :=
  TauCeti.SheafOfModules.monoidalCategory X.sheaf
local instance : (SheafOfModules.forget X.ringCatSheaf).LaxMonoidal :=
  TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf

/-- The canonical sheafification map on an ordinary local pure tensor. -/
def pure (M N : X.Modules) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    Γ(tensorSheaf M N, U) :=
  (tensorSheafUnit M N).app (op U) (s ⊗ₜ[Γ(X, U)] t)

/-- Comparison with the standard monoidal tensor, proved in the pinned library. -/
def ordinaryTensorIso (M N : X.Modules) : M ⊗ N ≅ tensorSheaf M N :=
  SheafOfModules.tensorUnderlyingIso M N

/-- The canonical pure tensor for the standard monoidal category. -/
def monoidalPure (M N : X.Modules) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    Γ(M ⊗ N, U) :=
  (Functor.LaxMonoidal.μ (SheafOfModules.forget X.ringCatSheaf) M N).app (op U)
    (s ⊗ₜ[Γ(X, U)] t)

theorem ordinaryTensorIso_inv_pure (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (ordinaryTensorIso M N).inv.app U (pure M N U s t) = monoidalPure M N U s t := by
  have h := SheafOfModules.sheafificationAdjunction_μ_eq_forget_μ X.sheaf M N
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit] at h
  erw [ordinaryTensorIso, SheafOfModules.tensorUnderlyingIso_inv (R := X.sheaf) M N,
    TauCeti.SheafOfModules.sheafificationIso_hom,
    TauCeti.SheafOfModules.sheafificationIso_hom]
  have h' := congrArg (fun f => f.app (op U) (s ⊗ₜ[Γ(X, U)] t)) h
  exact h'

theorem ordinaryTensorIso_hom_pure (M N : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (ordinaryTensorIso M N).hom.app U (monoidalPure M N U s t) = pure M N U s t := by
  rw [← ordinaryTensorIso_inv_pure]
  have h := congrArg (fun f : tensorSheaf M N ⟶ tensorSheaf M N =>
    f.app U (pure M N U s t)) (ordinaryTensorIso M N).inv_hom_id
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] using h

theorem monoidalTensorIso_pure {M M' N N' : X.Modules}
    (e : M ≅ M') (f : N ≅ N') (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (tensorIso e f).hom.app U (monoidalPure M N U s t) =
      monoidalPure M' N' U (e.hom.app U s) (f.hom.app U t) := by
  have h := congrArg (fun p => p.app (op U) (s ⊗ₜ[Γ(X, U)] t))
    (Functor.LaxMonoidal.μ_natural (SheafOfModules.forget X.ringCatSheaf) e.hom f.hom)
  exact h.symm

theorem monoidalAssociator_pure (M N P : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) (r : Γ(P, U)) :
    (α_ M N P).hom.app U
        (monoidalPure (M ⊗ N) P U (monoidalPure M N U s t) r) =
      monoidalPure M (N ⊗ P) U s (monoidalPure N P U t r) := by
  have h := congrArg (fun p => p.app (op U) ((s ⊗ₜ[Γ(X, U)] t) ⊗ₜ[Γ(X, U)] r))
    (Functor.LaxMonoidal.associativity (SheafOfModules.forget X.ringCatSheaf) M N P)
  exact h

theorem monoidalRightUnitor_pure (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (a : Γ(X, U)) :
    (ρ_ M).hom.app U
        (monoidalPure M (SheafOfModules.unit X.ringCatSheaf) U s a) = a • s := by
  have h := Functor.LaxMonoidal.right_unitality
    (SheafOfModules.forget X.ringCatSheaf) M
  rw [TauCeti.SheafOfModules.forget_ε X.sheaf] at h
  have h' := congrArg (fun p => p.app (op U) (s ⊗ₜ[Γ(X, U)] a)) h
  exact h'.symm

/-- Canonical associativity transported solely through the tensor-construction
comparison, without a Cartier presentation or any multiplication assumption. -/
def associator (M N P : X.Modules) :
    tensorSheaf (tensorSheaf M N) P ≅ tensorSheaf M (tensorSheaf N P) :=
  (ordinaryTensorIso (tensorSheaf M N) P).symm ≪≫
    tensorIso (ordinaryTensorIso M N).symm (Iso.refl P) ≪≫
    (α_ M N P) ≪≫
    tensorIso (Iso.refl M) (ordinaryTensorIso N P) ≪≫
    ordinaryTensorIso M (tensorSheaf N P)

/-- The standard right unitor, with the actual structure sheaf as tensor unit. -/
def rightUnitor (M : X.Modules) :
    tensorSheaf M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (ordinaryTensorIso M (SheafOfModules.unit X.ringCatSheaf)).symm ≪≫ ρ_ M


theorem associator_hom_pure (M N P : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) (r : Γ(P, U)) :
    (associator M N P).hom.app U
      (pure (tensorSheaf M N) P U (pure M N U s t) r) =
      pure M (tensorSheaf N P) U s (pure N P U t r) := by
  simp only [associator, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ordinaryTensorIso_inv_pure, monoidalTensorIso_pure, Iso.refl_hom,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply,
    monoidalAssociator_pure, ordinaryTensorIso_hom_pure]

theorem associator_inv_pure (M N P : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (t : Γ(N, U)) (r : Γ(P, U)) :
    (associator M N P).inv.app U
      (pure M (tensorSheaf N P) U s (pure N P U t r)) =
      pure (tensorSheaf M N) P U (pure M N U s t) r := by
  have h := congrArg (fun z => (associator M N P).inv.app U z)
    (associator_hom_pure M N P U s t r)
  have hc := congrArg (fun f : tensorSheaf (tensorSheaf M N) P ⟶
      tensorSheaf (tensorSheaf M N) P =>
      f.app U (pure (tensorSheaf M N) P U (pure M N U s t) r))
    (associator M N P).hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at hc
  exact h.symm.trans hc

theorem rightUnitor_pure (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (a : Γ(X, U)) :
    (rightUnitor M).hom.app U
      (pure M (SheafOfModules.unit X.ringCatSheaf) U s a) = a • s := by
  change (ρ_ M).hom.app U ((ordinaryTensorIso M _).inv.app U (pure M _ U s a)) = _
  rw [ordinaryTensorIso_inv_pure]
  exact monoidalRightUnitor_pure M U s a

/-- Canonical concatenation of ordinary tensor powers, defined recursively
from the standard associator and unitor, without a fractional presentation. -/
def multiplyIso (M : X.Modules) (i : ℕ) :
    ∀ j : ℕ, tensorSheaf (tensorSheafPower M i) (tensorSheafPower M j) ≅
      tensorSheafPower M (i + j)
  | 0 => rightUnitor (tensorSheafPower M i)
  | j + 1 =>
      (associator (tensorSheafPower M i) (tensorSheafPower M j) M).symm ≪≫
        tensorSheafIso (multiplyIso M i j) (Iso.refl M)

/-- An ordinary local tensor power of a given section. -/
def purePower (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    ∀ n : ℕ, Γ(tensorSheafPower M n, U)
  | 0 => (1 : Γ(X, U))
  | n + 1 => pure (tensorSheafPower M n) M U (purePower M U s n) s

/-- The independently defined canonical map concatenates ordinary pure powers. -/
theorem multiplyIso_purePower (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) (i j : ℕ) :
    (multiplyIso M i j).hom.app U
      (pure (tensorSheafPower M i) (tensorSheafPower M j) U
        (purePower M U s i) (purePower M U s j)) = purePower M U s (i + j) := by
  induction j with
  | zero =>
      change (rightUnitor (tensorSheafPower M i)).hom.app U
        (pure _ _ U (purePower M U s i) (1 : Γ(X, U))) = purePower M U s i
      rw [rightUnitor_pure, one_smul]
  | succ j ih =>
      change (tensorSheafIso (multiplyIso M i j) (Iso.refl M)).hom.app U
        ((associator (tensorSheafPower M i) (tensorSheafPower M j) M).inv.app U
          (pure _ _ U (purePower M U s i)
            (pure _ _ U (purePower M U s j) s))) =
        pure _ _ U (purePower M U s (i + j)) s
      rw [associator_inv_pure]
      change (tensorSheafIso (multiplyIso M i j) (Iso.refl M)).hom.app U
        ((tensorSheafUnit _ _).app (op U)
          ((pure _ _ U (purePower M U s i) (purePower M U s j)) ⊗ₜ[Γ(X, U)] s)) = _
      rw [tensorSheafIso_pure_sections]
      change pure _ _ U ((multiplyIso M i j).hom.app U
        (pure _ _ U (purePower M U s i) (purePower M U s j))) s = _
      rw [ih]

/-- The usual functorial map on tensor powers carries pure powers to pure powers. -/
theorem tensorSheafPowerIso_purePower {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) (n : ℕ) :
    (tensorSheafPowerIso e n).hom.app U (purePower M U s n) =
      purePower N U (e.hom.app U s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (tensorSheafIso (tensorSheafPowerIso e n) e).hom.app U
        ((tensorSheafUnit _ _).app (op U) (purePower M U s n ⊗ₜ[Γ(X, U)] s)) = _
      rw [tensorSheafIso_pure_sections]
      change pure _ _ U ((tensorSheafPowerIso e n).hom.app U (purePower M U s n))
        (e.hom.app U s) =
        pure _ _ U (purePower N U (e.hom.app U s) n) (e.hom.app U s)
      rw [ih]

#print axioms associator_hom_pure
#print axioms rightUnitor_pure
#print axioms multiplyIso
#print axioms multiplyIso_purePower
#print axioms tensorSheafPowerIso_purePower

#print axioms ordinaryTensorIso_inv_pure
#print axioms ordinaryTensorIso_hom_pure
#print axioms monoidalTensorIso_pure
#print axioms monoidalAssociator_pure
#print axioms monoidalRightUnitor_pure
#print axioms associator
#print axioms rightUnitor

end Unimodular.GraphicSectionRing.CanonicalPowers

#check Unimodular.GraphicSectionRing.CanonicalPowers.associator
