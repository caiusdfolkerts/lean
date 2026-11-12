module

public import ToricPower.FiniteFunctorTotalHorizontal
public import ToricPower.FiniteFunctorTotalShortExact
public import ToricPower.NaturalKernelFunctor
public import ToricPower.ShortExactQuasiIsoQuotient
public import ToricPower.JointQuasiIsoDetection

/-!
# Unbounded comparison through the actual augmentation kernel

An epimorphic natural quasi-isomorphism of horizontally bounded
complex-valued functors induces a quasi-isomorphism of their actual
finite totals, on an arbitrary unbounded coefficient complex. The
proof totalizes its genuine kernel and its original short exact
sequence. Exact affine module-valued functors may detect the result.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z t

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  {Ω Φ Ψ : A ⥤ CochainComplex B ℕ}
  [Ω.Additive] [Φ.Additive] [Ψ.Additive]
  (σ : Ω ⟶ Φ) (τ : Φ ⟶ Ψ) (zero : σ ≫ τ = 0)
  (width : ℕ) (K : CochainComplex A ℤ)
  {k : Type} [CommRing k] (F : B ⥤ ModuleCat.{0} k) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The comparison uses the original exact sequence and its actual
kernel complexes, before any geometric specialization. -/
theorem mapped_coefficientMap_quasiIso_of_shortExact
    (exactAt : ∀ a : ℤ,
      (ShortComplex.mk (σ.app (K.X a)) (τ.app (K.X a))
        (congrArg (fun η => η.app (K.X a)) zero)).ShortExact)
    (acyclicRows : ∀ a : ℤ,
      ((F.mapHomologicalComplex (.up ℕ)).obj (Ω.obj (K.X a))).Acyclic)
    (lastZero : ∀ a : ℤ, IsZero (F.obj ((Ω.obj (K.X a)).X width))) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (coefficientMap τ width K)) := by
  have exactTotal := shortComplex_shortExact σ τ zero width K exactAt
  have mappedExact := exactTotal.map_of_exact (F.mapHomologicalComplex (.up ℤ))
  exact shortExact_quasiIso_g_of_acyclic_left _ mappedExact
    (mapped_total_acyclic_of_horizontal Ω K F acyclicRows lastZero)

/-- The actual pointwise kernel supplies all the hypotheses above.
Epimorphy and quasi-isomorphism are required only on the actual terms
of the unbounded input complex. -/
theorem mapped_coefficientMap_quasiIso_of_epi
    (epi : ∀ a : ℤ, Epi (τ.app (K.X a)))
    (qiso : ∀ a : ℤ,
      QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (τ.app (K.X a))))
    (lastZero : ∀ a : ℤ, IsZero (F.obj ((Φ.obj (K.X a)).X width))) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (coefficientMap τ width K)) := by
  apply mapped_coefficientMap_quasiIso_of_shortExact
    (NaturalKernel.inclusion τ) τ (NaturalKernel.inclusion_comp τ) width K F
  · intro a
    letI := epi a
    exact NaturalKernel.sequence_shortExact τ (K.X a)
  · intro a
    letI := epi a
    have exactKernel := (NaturalKernel.sequence_shortExact τ (K.X a)).map_of_exact
      (F.mapHomologicalComplex (.up ℕ))
    exact exactKernel.acyclic_X₁ (qiso a)
  · intro a
    let f := ((NaturalKernel.inclusion τ).app (K.X a)).f width
    letI : Mono f := by
      change Mono ((HomologicalComplex.eval B (.up ℕ) width).map (kernel.ι (τ.app (K.X a))))
      infer_instance
    exact isZero_of_mono_to_zero (F.map f) (lastZero a)

/-- An exact family detecting zero objects proves the comparison in
the original abelian category itself. -/
theorem coefficientMap_quasiIso_of_epi_detectors
    {I : Type t} (detectors : I → B ⥤ ModuleCat.{0} k)
    [∀ i, (detectors i).Additive]
    [∀ i, PreservesFiniteLimits (detectors i)]
    [∀ i, PreservesFiniteColimits (detectors i)]
    (detect : ∀ M : B, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
    (epi : ∀ a : ℤ, Epi (τ.app (K.X a)))
    (qiso : ∀ i a,
      QuasiIso (((detectors i).mapHomologicalComplex (.up ℕ)).map (τ.app (K.X a))))
    (lastZero : ∀ a : ℤ, IsZero ((Φ.obj (K.X a)).X width)) :
    QuasiIso (coefficientMap τ width K) := by
  apply quasiIso_of_jointly_detect_zero detectors detect
  intro i
  exact mapped_coefficientMap_quasiIso_of_epi τ width K (detectors i) epi (qiso i)
    (fun a => (detectors i).map_isZero (lastZero a))

end ToricPower.FunctorTotal

end
