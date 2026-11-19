module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
public import Mathlib.Algebra.Homology.Opposite

/-!
# Internal duals of actual complexes and monoidal pullback

Internal Hom into the tensor unit is a contravariant functor. It sends
zero maps to zero maps, so it applies to the actual differentials of a
complex without any exactness assertion. A strong monoidal functor has a
canonical comparison with this dual; the comparison is invertible on
dualizable objects and is natural for the original maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite

namespace ToricPower

universe v u v' u'

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

def internalDual : Cᵒᵖ ⥤ C :=
  (internalHom (C := C)).flip.obj (𝟙_ C)

@[simp]
theorem internalDual_obj (M : Cᵒᵖ) :
    (internalDual C).obj M = (ihom M.unop).obj (𝟙_ C) := rfl

@[simp]
theorem internalDual_map {M N : Cᵒᵖ} (f : M ⟶ N) :
    (internalDual C).map f = (pre f.unop).app (𝟙_ C) := rfl

variable [Preadditive C] [MonoidalPreadditive C]

instance internalDual_preservesZeroMorphisms : (internalDual C).PreservesZeroMorphisms where
  map_zero M N := by
    change (pre (0 : N.unop ⟶ M.unop)).app (𝟙_ C) = 0
    apply uncurry_injective
    rw [uncurry_pre, uncurry_eq]
    simp

instance internalDual_additive : (internalDual C).Additive where
  map_add {M N} f g := by
    change (pre (f.unop + g.unop)).app (𝟙_ C) =
      (pre f.unop).app (𝟙_ C) + (pre g.unop).app (𝟙_ C)
    apply uncurry_injective
    rw [uncurry_pre, uncurry_eq]
    simp only [MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]
    rw [← uncurry_eq, ← uncurry_eq, uncurry_pre, uncurry_pre]
    simp

/-- The actual internal dual cochain complex; this construction does
not assert preservation of homology by dualization. -/
def internalDualComplex (K : ChainComplex C ℕ) : CochainComplex C ℕ :=
  ((internalDual C).mapHomologicalComplex _).obj K.op

/-- A genuine complex isomorphism gives the corresponding internal
 dual isomorphism, with inverse maps in the intended opposite order. -/
def internalDualComplexIso {K L : ChainComplex C ℕ} (e : K ≅ L) :
    internalDualComplex C K ≅ internalDualComplex C L :=
  ((internalDual C).mapHomologicalComplex _).mapIso
    ((HomologicalComplex.opFunctor C (.down ℕ)).mapIso e.symm.op)

variable {C}
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [MonoidalClosed D]
  (F : C ⥤ D) [F.Monoidal]

/-- The canonical strong-monoidal comparison retains its actual
internal-Hom mate and its actual unit transport. -/
def internalDualComparison : internalDual C ⋙ F ⟶ F.op ⋙ internalDual D where
  app M := (F.ihomComparison M.unop).natTrans.app (𝟙_ C) ≫
    (ihom (F.obj M.unop)).map (Functor.OplaxMonoidal.η F)
  naturality {M N} f := by
    have source := congrArg (fun t => t.natTrans.app (𝟙_ C))
      (F.ihomComparison_whiskerLeft f.unop)
    change (F.ihomComparison M.unop).natTrans.app (𝟙_ C) ≫
        (pre (F.map f.unop)).app (F.obj (𝟙_ C)) =
      F.map ((pre f.unop).app (𝟙_ C)) ≫
        (F.ihomComparison N.unop).natTrans.app (𝟙_ C) at source
    change F.map ((pre f.unop).app (𝟙_ C)) ≫
        ((F.ihomComparison N.unop).natTrans.app (𝟙_ C) ≫
          (ihom (F.obj N.unop)).map (Functor.OplaxMonoidal.η F)) =
      ((F.ihomComparison M.unop).natTrans.app (𝟙_ C) ≫
        (ihom (F.obj M.unop)).map (Functor.OplaxMonoidal.η F)) ≫
          (pre (F.map f.unop)).app (𝟙_ D)
    rw [← Category.assoc, ← source, Category.assoc,
      ← (pre (F.map f.unop)).naturality (Functor.OplaxMonoidal.η F),
      ← Category.assoc]

/-- Pullback commutes with the actual internal dual of a dualizable object. -/
instance internalDualComparison_isIso (M : C) [HasLeftDual M] :
    IsIso ((internalDualComparison F).app (op M)) := by
  letI := F.ihomComparison_isIso_of_exactPairing (ᘁM) M
  change IsIso ((F.ihomComparison M).natTrans.app (𝟙_ C) ≫
    (ihom (F.obj M)).map (Functor.OplaxMonoidal.η F))
  infer_instance

variable [Preadditive D] [MonoidalPreadditive D] [F.PreservesZeroMorphisms]

/-- The canonical comparison of complete complexes is invertible when
each actual term is dualizable. It intertwines every original differential. -/
def internalDualComplexMapIso (K : ChainComplex C ℕ) [duals : ∀ q, HasLeftDual (K.X q)] :
    (F.mapHomologicalComplex (.up ℕ)).obj (internalDualComplex C K) ≅
      internalDualComplex D ((F.mapHomologicalComplex (.down ℕ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => by
      letI := duals q
      exact @asIso _ _ _ _ ((internalDualComparison F).app (op (K.X q)))
        (internalDualComparison_isIso F (K.X q)))
    (fun i j _ => by
      exact ((internalDualComparison F).naturality (K.d j i).op).symm)

end ToricPower
