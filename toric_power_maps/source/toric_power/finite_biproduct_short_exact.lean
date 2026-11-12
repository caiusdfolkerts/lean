module

public import ToricPower.JointExactDetection
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Short exact sequences and actual finite biproduct maps -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe u v w z

variable {C : Type u} [Category.{v} C]
  {B : Type w} [Category.{z} B] [Abelian B]

/-- Exactness in a functor category is detected at every original
object, including the mono and epi assertions. -/
theorem shortExact_of_evaluation (S : ShortComplex (C ⥤ B))
    (exactAt : ∀ c : C, (S.map ((evaluation C B).obj c)).ShortExact) :
    S.ShortExact where
  exact := by
    apply exact_of_jointly_detect_zero (fun c : C => (evaluation C B).obj c) ?_ S
      (fun c => (exactAt c).exact)
    intro M zeroAt
    rw [IsZero.iff_id_eq_zero]
    ext c
    exact (zeroAt c).eq_of_src _ _
  mono_f := by
    letI : ∀ c : C, Mono (S.f.app c) := fun c => (exactAt c).mono_f
    exact NatTrans.mono_of_mono_app S.f
  epi_g := by
    letI : ∀ c : C, Epi (S.g.app c) := fun c => (exactAt c).epi_g
    exact NatTrans.epi_of_epi_app S.g

variable [HasFiniteBiproducts B] {I : Type} [Fintype I]
  {X Y Z : I → B} (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i)
  (zero : ∀ i, f i ≫ g i = 0)

def finiteDiscreteShortComplex : ShortComplex (Discrete I ⥤ B) :=
  ShortComplex.mk
    (show Discrete.functor X ⟶ Discrete.functor Y from
      Discrete.natTrans (fun i => f i.as))
    (show Discrete.functor Y ⟶ Discrete.functor Z from
      Discrete.natTrans (fun i => g i.as)) (by
      ext i
      exact zero i.as)

include zero in
theorem biproduct_map_comp_zero : biproduct.map f ≫ biproduct.map g = 0 := by
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,zero,
    comp_zero,zero_comp]

/-- The actual finite diagonal matrices preserve a pointwise short
exact sequence. This follows from the proved equality of finite
coproducts and finite products, via their canonical colimit comparison. -/
theorem biproduct_shortExact
    (exactAt : ∀ i, (ShortComplex.mk (f i) (g i) (zero i)).ShortExact) :
    (ShortComplex.mk (biproduct.map f) (biproduct.map g)
      (biproduct_map_comp_zero f g zero)).ShortExact := by
  let S := finiteDiscreteShortComplex f g zero
  have hS : S.ShortExact := shortExact_of_evaluation S (fun i => exactAt i.as)
  have hT := hS.map_of_exact (colim (J := Discrete I) (C := B))
  let e : S.map (colim (J := Discrete I) (C := B)) ≅
      ShortComplex.mk (biproduct.map f) (biproduct.map g)
        (biproduct_map_comp_zero f g zero) :=
    ShortComplex.isoMk (biproduct.isoCoproduct X).symm
      (biproduct.isoCoproduct Y).symm (biproduct.isoCoproduct Z).symm (by
        apply colimit.hom_ext
        intro i
        simp [S,finiteDiscreteShortComplex,biproduct.isoCoproduct_inv]) (by
        apply colimit.hom_ext
        intro i
        simp [S,finiteDiscreteShortComplex,biproduct.isoCoproduct_inv])
  exact ShortComplex.shortExact_of_iso e hT

end ToricPower

end
