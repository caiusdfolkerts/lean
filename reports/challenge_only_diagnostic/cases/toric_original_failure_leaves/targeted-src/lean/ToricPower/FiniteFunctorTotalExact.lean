module

public import ToricPower.FiniteFunctorTotalMap
public import ToricPower.TriangularConeCoordinates
public import ToricPower.JointQuasiIsoDetection
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Quasi-isomorphism preservation of the actual finite total

Every horizontal term of the complex-valued functor is exact. The
input may be unbounded in both directions. Finite triangular cone
coordinates prove quasi-isomorphism preservation after exact module
detectors, and a genuine family detecting zero objects gives the
conclusion in the original abelian category.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

universe u v w z t

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type w} [Category.{z} B] [Abelian B] [HasFiniteBiproducts B]
  (Φ : A ⥤ CochainComplex B ℕ) [Φ.Additive] (width : ℕ)
  {k : Type} [CommRing k] (F : B ⥤ ModuleCat.{0} k) [F.Additive]

/-- The actual row maps control the actual total map, before any
specialization to an exact coefficient functor. -/
theorem mapped_map_quasiIso {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (rows : ∀ q : Fin width,
      QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (rowMap Φ f q))) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (map Φ width f)) := by
  apply TriangularCoordinates.quasiIso
    (FiniteTotal.mappedCoordinates (row Φ K) (off Φ K) (off_coherent Φ K)
      (off_strictlyRaises Φ K) F)
    (FiniteTotal.mappedCoordinates (row Φ L) (off Φ L) (off_coherent Φ L)
      (off_strictlyRaises Φ L) F)
    ((F.mapHomologicalComplex (.up ℤ)).map (map Φ width f))
    (fun q => (F.mapHomologicalComplex (.up ℤ)).map (rowMap Φ f q)) ?_ rows
  intro a q z
  change F.map (biproduct.π (fun q : Fin width => (row Φ L q).X a) q)
    (F.map ((map Φ width f).f a) z) =
      F.map ((rowMap Φ f q).f a)
        (F.map (biproduct.π (fun q : Fin width => (row Φ K q).X a) q) z)
  rw [map_f]
  have h := congrArg (fun h => F.map h z)
    (biproduct.map_π (fun q : Fin width => (rowMap Φ f q).f a) q)
  simp only [F.map_comp,ModuleCat.comp_apply] at h
  exact h

variable [∀ q : ℕ, PreservesFiniteLimits (degree Φ q)]
  [∀ q : ℕ, PreservesFiniteColimits (degree Φ q)]

theorem mapped_map_quasiIso_of_exact [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (map Φ width f)) := by
  apply mapped_map_quasiIso Φ width F f
  intro q
  unfold rowMap
  infer_instance

/-- Exact module-valued detectors, such as the original sections on
an affine open cover, give quasi-isomorphism preservation in `B` itself. -/
theorem map_quasiIso_of_exact_detectors
    {I : Type t} (detectors : I → B ⥤ ModuleCat.{0} k)
    [∀ i, (detectors i).Additive]
    [∀ i, PreservesFiniteLimits (detectors i)]
    [∀ i, PreservesFiniteColimits (detectors i)]
    (detect : ∀ M : B, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((functor Φ width).map f) := by
  apply quasiIso_of_jointly_detect_zero detectors detect
  intro i
  exact mapped_map_quasiIso_of_exact Φ width (detectors i) f

end ToricPower.FunctorTotal

end
