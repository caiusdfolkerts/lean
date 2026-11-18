module

public import ToricPower.CellularDualInjective
public import ToricPower.FiniteDiagramSyzygies
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Finite injective resolutions of finite incidence diagrams

The actual projective resolution of the reversed scalar dual gives an
injective resolution after dualizing. Finite-dimensional reflexivity
identifies its augmentation with the original diagram. A strict finite
grading bounds its length, and finite Hom sets keep every coefficient
finite-dimensional.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace ToricPower.Cellular

universe u
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

def scalarDoubleDualLinearEquiv (M : ModuleCat.{u} k) [FiniteDimensional k M] :
    M ≃ₗ[k] (scalarDual k).obj (op ((scalarDual k).obj (op M))) :=
  (Module.evalEquiv k M).trans
    ((ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := M) (N := ModuleCat.of k k)).dualMap.trans
        (ModuleCat.homLinearEquiv (R := k) (S := k)
          (M := (scalarDual k).obj (op M)) (N := ModuleCat.of k k)).symm)

theorem scalarDoubleDualLinearEquiv_apply
    (M : ModuleCat.{u} k) [FiniteDimensional k M] (x : M)
    (f : (scalarDual k).obj (op M)) :
    (show (scalarDual k).obj (op M) ⟶ ModuleCat.of k k from
      scalarDoubleDualLinearEquiv k M x) f =
        (show M ⟶ ModuleCat.of k k from f) x := rfl

def diagramDoubleDualIso (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] :
    F ≅ (diagramScalarDual k C).obj (op (reversedScalarDual k F)) :=
  NatIso.ofComponents (fun c => (scalarDoubleDualLinearEquiv k (F.obj c)).toModuleIso)
    (by
      intro c d a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      rfl)

theorem reversedScalarDual_finite (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] (c : Cᵒᵖ) :
    FiniteDimensional k ((reversedScalarDual k F).obj c) :=
  FiniteDimensional.of_injective
    (ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := F.obj c.unop) (N := ModuleCat.of k k)).toLinearMap
    (ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := F.obj c.unop) (N := ModuleCat.of k k)).injective

def diagramScalarDualSingleZeroIso (F : Cᵒᵖ ⥤ ModuleCat.{u} k) :
    diagramScalarDualComplex k C ((ChainComplex.single₀ _).obj F) ≅
      (CochainComplex.single₀ _).obj ((diagramScalarDual k C).obj (op F)) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) ?_
  · cases n with
    | zero => exact Iso.refl _
    | succ n =>
      exact IsZero.iso
        ((diagramScalarDual k C).map_isZero
          (isZero_single_obj_X (.down ℕ) 0 F (n + 1) (by omega)).op)
        (isZero_single_obj_X (.up ℕ) 0 _ (n + 1) (by omega))
  · intro i j hij
    change _ ≫ 0 = (diagramScalarDual k C).map
      (((ChainComplex.single₀ _).obj F).d j i).op ≫ _
    simp only [ChainComplex.single₀, single_obj_d, op_zero,
      CategoryTheory.Functor.map_zero, comp_zero, zero_comp]

def diagramFiniteInjectiveComplex (F : C ⥤ ModuleCat.{u} k) :
    CochainComplex (C ⥤ ModuleCat.{u} k) ℕ :=
  diagramScalarDualComplex k C (diagramProjectiveComplex k (reversedScalarDual k F))

instance diagramFiniteInjectiveComplex_injective (F : C ⥤ ModuleCat.{u} k) (n : ℕ) :
    Injective ((diagramFiniteInjectiveComplex k F).X n) :=
  diagramScalarDual_injective k (diagramProjectiveTerm k (reversedScalarDual k F) n)

def diagramFiniteInjectiveAugmentation (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] :
    (CochainComplex.single₀ _).obj F ⟶ diagramFiniteInjectiveComplex k F :=
  (CochainComplex.single₀ _).map (diagramDoubleDualIso k F).hom ≫
    (diagramScalarDualSingleZeroIso k (reversedScalarDual k F)).inv ≫
      diagramScalarDualMap k C (diagramProjectiveAugmentation k (reversedScalarDual k F))

instance diagramFiniteInjectiveAugmentation_quasiIso (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] :
    QuasiIso (diagramFiniteInjectiveAugmentation k F) := by
  unfold diagramFiniteInjectiveAugmentation
  infer_instance

def diagramFiniteInjectiveResolution (F : C ⥤ ModuleCat.{u} k)
    [∀ c, FiniteDimensional k (F.obj c)] : InjectiveResolution F where
  cocomplex := diagramFiniteInjectiveComplex k F
  injective := diagramFiniteInjectiveComplex_injective k F
  ι := diagramFiniteInjectiveAugmentation k F

theorem diagramFiniteInjectiveComplex_finite
    [Finite C] [∀ c d : C, Finite (c ⟶ d)]
    (F : C ⥤ ModuleCat.{u} k) [∀ c, FiniteDimensional k (F.obj c)]
    (n : ℕ) (c : C) :
    FiniteDimensional k (((diagramFiniteInjectiveComplex k F).X n).obj c) := by
  letI : Finite Cᵒᵖ := Finite.of_injective (fun c : Cᵒᵖ => c.unop) unop_injective
  letI (c d : Cᵒᵖ) : Finite (c ⟶ d) :=
    Finite.of_injective (fun f : c ⟶ d => f.unop)
      (fun _ _ h => congrArg (fun g : d.unop ⟶ c.unop => g.op) h)
  letI (d : Cᵒᵖ) := reversedScalarDual_finite k F d
  letI := diagramProjectiveTerm_finite k (reversedScalarDual k F) n (op c)
  let M := (diagramProjectiveTerm k (reversedScalarDual k F) n).obj (op c)
  exact FiniteDimensional.of_injective
    (ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := M) (N := ModuleCat.of k k)).toLinearMap
    (ModuleCat.homLinearEquiv (R := k) (S := k)
      (M := M) (N := ModuleCat.of k k)).injective

theorem diagramFiniteInjectiveComplex_isZero_above
    (grade : C → ℕ)
    (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
    (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
    [∀ c : C, Subsingleton (c ⟶ c)]
    (F : C ⥤ ModuleCat.{u} k) (N n : ℕ)
    (bound : ∀ c, grade c ≤ N) (above : N < n) :
    IsZero ((diagramFiniteInjectiveComplex k F).X n) := by
  apply (diagramScalarDual k C).map_isZero
  apply IsZero.op
  apply diagramProjectiveComplex_isZero_above k
    (fun c : Cᵒᵖ => N - grade c.unop)
    (fun {c d} f => by have h := grade_le f.unop; omega)
    (fun {c d} f h => by
      apply unop_injective
      exact (eq_of_grade_eq f.unop (by
        have hc := bound c.unop
        have hd := bound d.unop
        omega)).symm)
    (reversedScalarDual k F) N n (fun _ => Nat.sub_le _ _) above

end ToricPower.Cellular

end
