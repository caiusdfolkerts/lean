module

public import ToricPower.CechMeetInjectiveAssembly
public import ToricPower.LinearHomToSingleExtension
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# The actual scalar-linear intersection-poset Čech comparison

All terms are actual modules of sections over actual intersections.
The comparison is a complete chain isomorphism, natural in every
coefficient map. It uses ordinary tuple generators and the same
alternating restriction differential as the standard Čech complex.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open BondalThomsen.FiniteAffineCechHigherComparison

namespace ToricPower.FiniteCech

variable {B : Type} [SemilatticeInf B] (k : Type) [Field k]
  (X : Scheme) (opens : B ⥤ X.Opens)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    cechIntersection opens.obj q t = opens.obj (tupleMeet t))
  (F : X.Opensᵒᵖ ⥤ ModuleCat.{0} k)

/-- Literal tuple evaluation of the actual module-valued Čech complex. -/
def moduleCechCoordinate (q : ℕ)
    (x : ((cechComplexFunctor opens.obj).obj F).X q) (t : Fin (q+1) → B) :
    F.obj (op (cechIntersection opens.obj q t)) :=
  Limits.Pi.π (fun t : Fin (q+1) → B => F.obj (op (cechIntersection opens.obj q t))) t x

/-- Each degree is linearly identified using the actual equality of
intersection opens and evaluation on the actual free tuple generator. -/
def meetLinearCechDegreeIso (q : ℕ) :
    ((cechComplexFunctor opens.obj).obj F).X q ≅
      (tupleCoefficientComplex k (opens.op ⋙ F)).X q :=
  Limits.Pi.mapIso (fun t : Fin (q+1) → B =>
    F.mapIso (eqToIso (meetEq q t).symm).op) ≪≫
      ModuleCat.piIsoPi (fun t : Fin (q+1) → B => F.obj (op (opens.obj (tupleMeet t)))) ≪≫
        (tupleEvaluation k q (opens.op ⋙ F)).symm.toModuleIso

/-- The comparison retains the literal section at every tuple. -/
theorem meetLinearCechDegreeIso_apply (q : ℕ)
    (x : ((cechComplexFunctor opens.obj).obj F).X q) (t : Fin (q+1) → B) :
    tupleEvaluation k q (opens.op ⋙ F) ((meetLinearCechDegreeIso k X opens meetEq F q).hom x) t =
      F.map (eqToHom (meetEq q t).symm).op (moduleCechCoordinate k X opens F q x t) := by
  change (tupleEvaluation k q (opens.op ⋙ F))
    ((tupleEvaluation k q (opens.op ⋙ F)).symm _) t = _
  rw [LinearEquiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom
    (ModuleCat.piIsoPi_hom_ker_subtype
      (fun t : Fin (q+1) → B => F.obj (op (opens.obj (tupleMeet t)))) t)
      ((Limits.Pi.mapIso (fun t : Fin (q+1) → B =>
        F.mapIso (eqToIso (meetEq q t).symm).op)).hom x)
  exact h.trans (ConcreteCategory.congr_hom
    (Limits.Pi.mapIso_hom_π (fun t : Fin (q+1) → B =>
      F.mapIso (eqToIso (meetEq q t).symm).op) t) x)

/-- Literal module-valued Čech differentials in tuple coordinates. -/
theorem moduleCechDifferential_component (q : ℕ)
    (x : ((cechComplexFunctor opens.obj).obj F).X q) (t : Fin (q+2) → B) :
    moduleCechCoordinate k X opens F (q+1)
      (((cechComplexFunctor opens.obj).obj F).d q (q+1) x) t =
    ∑ a : Fin (q+2), (-1 : ℤ)^a.val •
      F.map (Limits.Pi.lift (fun j : Fin (q+1) =>
        Limits.Pi.π (opens.obj ∘ t) (a.succAbove j))).op
        (moduleCechCoordinate k X opens F q x (t ∘ a.succAbove)) := by
  have differential : ((cechComplexFunctor opens.obj).obj F).d q (q+1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk B opens.obj).cech).obj F) q := by
    dsimp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor, Functor.comp_obj,
      AlgebraicTopology.alternatingCofaceMapComplex_obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d]
  have component : ((cechComplexFunctor opens.obj).obj F).d q (q+1) ≫
      Limits.Pi.π (fun t : Fin (q+2) → B => F.obj (op (cechIntersection opens.obj (q+1) t))) t =
      ∑ a : Fin (q+2), (-1 : ℤ)^a.val •
        (Limits.Pi.π (fun t : Fin (q+1) → B => F.obj (op (cechIntersection opens.obj q t)))
          (t ∘ a.succAbove) ≫
        F.map (Limits.Pi.lift (fun j : Fin (q+1) =>
          Limits.Pi.π (opens.obj ∘ t) (a.succAbove j))).op) := by
    rw [differential]
    dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ a : Fin (q+2), (-1 : ℤ)^a.val •
      Limits.Pi.lift (fun t : Fin (q+2) → B =>
        Limits.Pi.π (fun t : Fin (q+1) → B => F.obj (op (∏ᶜ (opens.obj ∘ t))))
          (t ∘ a.succAbove) ≫
        F.map (Limits.Pi.lift (fun j : Fin (q+1) =>
          Limits.Pi.π (opens.obj ∘ t) (a.succAbove j))).op)) ≫
      Limits.Pi.π (fun t : Fin (q+2) → B => F.obj (op (∏ᶜ (opens.obj ∘ t)))) t = _
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Limits.Pi.lift_comp_π]
    rfl
  let evaluation : (((cechComplexFunctor opens.obj).obj F).X q ⟶
      F.obj (op (cechIntersection opens.obj (q+1) t))) →+
        F.obj (op (cechIntersection opens.obj (q+1) t)) :=
    { toFun := fun f => f x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have eq := congrArg evaluation component
  rw [map_sum] at eq
  simp only [map_zsmul] at eq
  exact eq

/-- Equality of the actual restriction maps, including every tuple selection. -/
theorem moduleMeetCech_restriction {p q : ℕ} (s : Fin (p+1) → Fin (q+1))
    (t : Fin (q+1) → B) (x : F.obj (op (cechIntersection opens.obj p (t ∘ s)))) :
    F.map (eqToHom (meetEq q t).symm).op
      (F.map (Limits.Pi.lift (fun j : Fin (p+1) =>
        Limits.Pi.π (opens.obj ∘ t) (s j))).op x) =
    (opens.op ⋙ F).map (homOfLE (tupleMeet_le_selection s t)).op
      (F.map (eqToHom (meetEq p (t ∘ s)).symm).op x) := by
  have maps : F.map (Limits.Pi.lift (fun j : Fin (p+1) =>
      Limits.Pi.π (opens.obj ∘ t) (s j))).op ≫
        F.map (eqToHom (meetEq q t).symm).op =
      F.map (eqToHom (meetEq p (t ∘ s)).symm).op ≫
        F.map (opens.map (homOfLE (tupleMeet_le_selection s t))).op := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom maps x

/-- A genuine full complex-linear comparison with ordinary projective
coefficients, using every original Čech differential. -/
def meetLinearCechComplexIso :
    (cechComplexFunctor opens.obj).obj F ≅ tupleCoefficientComplex k (opens.op ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (meetLinearCechDegreeIso k X opens meetEq F)
    (fun p q hpq => by
      obtain rfl : p+1=q := hpq
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (tupleEvaluation k (p+1) (opens.op ⋙ F)).injective
      funext t
      change tupleEvaluation k (p+1) (opens.op ⋙ F)
          ((tupleCoefficientComplex k (opens.op ⋙ F)).d p (p+1)
            ((meetLinearCechDegreeIso k X opens meetEq F p).hom x)) t =
        tupleEvaluation k (p+1) (opens.op ⋙ F)
          ((meetLinearCechDegreeIso k X opens meetEq F (p+1)).hom
            (((cechComplexFunctor opens.obj).obj F).d p (p+1) x)) t
      rw [tupleCoefficient_d_apply, meetLinearCechDegreeIso_apply,
        moduleCechDifferential_component, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_zsmul, meetLinearCechDegreeIso_apply,
        moduleMeetCech_restriction k X opens meetEq F])

/-- The complete scalar-linear chain comparison respects every actual
coefficient morphism, hence all Cartier-source incidence maps as well. -/
theorem meetLinearCechComplexIso_naturality
    {F G : X.Opensᵒᵖ ⥤ ModuleCat.{0} k} (f : F ⟶ G) :
    (cechComplexFunctor opens.obj).map f ≫ (meetLinearCechComplexIso k X opens meetEq G).hom =
      (meetLinearCechComplexIso k X opens meetEq F).hom ≫
        ordinaryChainCoefficientsMap k (tupleComplex k) (Functor.whiskerLeft opens.op f) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (tupleEvaluation k q (opens.op ⋙ G)).injective
  funext t
  change tupleEvaluation k q (opens.op ⋙ G)
      ((meetLinearCechDegreeIso k X opens meetEq G q).hom
        (((cechComplexFunctor opens.obj).map f).f q x)) t = _
  rw [meetLinearCechDegreeIso_apply]
  have projection := ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun t : Fin (q+1) → B =>
      f.app (op (cechIntersection opens.obj q t))) t) x
  change moduleCechCoordinate k X opens G q
      (((cechComplexFunctor opens.obj).map f).f q x) t = _ at projection
  rw [projection]
  have natural := ConcreteCategory.congr_hom
    (f.naturality (eqToHom (meetEq q t).symm).op)
      (moduleCechCoordinate k X opens F q x t)
  change f.app (op (opens.obj (tupleMeet t)))
    (F.map (eqToHom (meetEq q t).symm).op (moduleCechCoordinate k X opens F q x t)) =
      G.map (eqToHom (meetEq q t).symm).op
        (f.app (op (cechIntersection opens.obj q t))
          (moduleCechCoordinate k X opens F q x t)) at natural
  change G.map (eqToHom (meetEq q t).symm).op
    (f.app (op (cechIntersection opens.obj q t))
      (moduleCechCoordinate k X opens F q x t)) = _
  rw [← natural]
  change f.app (op (opens.obj (tupleMeet t))) _ =
    f.app (op (opens.obj (tupleMeet t)))
      (tupleEvaluation k q (opens.op ⋙ F)
        ((meetLinearCechDegreeIso k X opens meetEq F q).hom x) t)
  rw [meetLinearCechDegreeIso_apply]

end ToricPower.FiniteCech
