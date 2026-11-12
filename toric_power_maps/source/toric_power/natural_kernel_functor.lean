module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# The actual functorial kernel of a natural transformation

The construction uses categorical kernels of the original components.
Its additivity and natural inclusion are proved by the universal kernel
identities. It is useful for comparing complex-valued realization
functors without changing their specified augmentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace ToricPower.NaturalKernel

universe u v w z

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Abelian B]
  {Φ Ψ : A ⥤ B} [Φ.Additive] [Ψ.Additive] (τ : Φ ⟶ Ψ)

def functor : A ⥤ B where
  obj X := kernel (τ.app X)
  map {X Y} f := kernel.map (τ.app X) (τ.app Y) (Φ.map f) (Ψ.map f)
    (τ.naturality f).symm
  map_id X := by
    apply (cancel_mono (kernel.ι (τ.app X))).mp
    simp only [kernel.map,kernel.lift_ι,CategoryTheory.Functor.map_id,
      Category.id_comp,Category.comp_id]
  map_comp {X Y Z} f g := by
    apply (cancel_mono (kernel.ι (τ.app Z))).mp
    simp only [Category.assoc,kernel.map,kernel.lift_ι,kernel.lift_ι_assoc,Functor.map_comp]

instance functor_additive : (functor τ).Additive where
  map_add {X Y} f g := by
    apply (cancel_mono (kernel.ι (τ.app Y))).mp
    simp only [functor,kernel.map,kernel.lift_ι,add_comp,Functor.map_add,comp_add]

def inclusion : functor τ ⟶ Φ where
  app X := kernel.ι (τ.app X)
  naturality {X Y} f := by simp only [functor,kernel.map,kernel.lift_ι]

@[reassoc (attr := simp)]
theorem inclusion_comp : inclusion τ ≫ τ = 0 := by
  ext X
  exact kernel.condition (τ.app X)

def sequence (X : A) : ShortComplex B :=
  ShortComplex.mk ((inclusion τ).app X) (τ.app X) (kernel.condition (τ.app X))

theorem sequence_shortExact (X : A) [Epi (τ.app X)] : (sequence τ X).ShortExact where
  exact := ShortComplex.kernelSequence_exact (τ.app X)
  mono_f := by
    change Mono (kernel.ι (τ.app X))
    infer_instance
  epi_g := by
    change Epi (τ.app X)
    infer_instance

end ToricPower.NaturalKernel

namespace ToricPower

variable {B : Type*} [Category* B] [HasZeroMorphisms B]
  {X Y : B}

/-- A genuine subobject of a zero object is zero. -/
theorem isZero_of_mono_to_zero (f : X ⟶ Y) [Mono f] (zero : IsZero Y) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_mono f).mp
  rw [Category.id_comp,zero_comp]
  exact zero.eq_of_tgt _ _

end ToricPower

end
