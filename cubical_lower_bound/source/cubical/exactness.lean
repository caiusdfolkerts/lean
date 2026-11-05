import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Stability of exact finite-dimensional complexes

If continuously varying linear maps form a complex at every parameter and
are exact at one parameter, they remain exact nearby. The proof preserves
independence of bases of the two images and then uses rank-nullity.
This avoids any formula for the dimension of a special kernel.
-/

namespace Cubical.Exactness

open Module Filter
open scoped Topology

variable {α X Y Z : Type*} [TopologicalSpace α]
  [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

omit [FiniteDimensional ℝ Y] in
/-- The rank of a continuous matrix family cannot decrease close to a fixed
parameter. Continuity is required only after evaluating at each vector. -/
theorem eventually_finrank_range_ge (f : α → X →ₗ[ℝ] Y) (a₀ : α)
    (hf : ∀ x, ContinuousAt (fun a => f a x) a₀) :
    ∀ᶠ a in 𝓝 a₀, finrank ℝ (LinearMap.range (f a₀)) ≤
      finrank ℝ (LinearMap.range (f a)) := by
  classical
  let r := finrank ℝ (LinearMap.range (f a₀))
  let b := Module.finBasis ℝ (LinearMap.range (f a₀))
  let v : Fin r → X := fun i =>
    Classical.choose (LinearMap.mem_range.mp (b i).property)
  have hv : ∀ i, f a₀ (v i) = (b i).val := fun i =>
    Classical.choose_spec (LinearMap.mem_range.mp (b i).property)
  have hli : LinearIndependent ℝ (fun i => f a₀ (v i)) := by
    have hb := b.linearIndependent.map' (LinearMap.range (f a₀)).subtype
      (Submodule.ker_subtype _)
    convert hb using 1
    funext i
    exact hv i
  have hcont : ContinuousAt (fun a => fun i => f a (v i)) a₀ :=
    continuousAt_pi.mpr fun i => hf (v i)
  have hevent : ∀ᶠ a in 𝓝 a₀, LinearIndependent ℝ (fun i => f a (v i)) :=
    hcont.tendsto.eventually hli.eventually
  filter_upwards [hevent] with a ha
  let u : Fin r → LinearMap.range (f a) := fun i =>
    ⟨f a (v i), LinearMap.mem_range_self _ _⟩
  have hu : LinearIndependent ℝ u :=
    LinearIndependent.of_comp (LinearMap.range (f a)).subtype ha
  simpa only [Fintype.card_fin] using hu.fintype_card_le_finrank

omit [FiniteDimensional ℝ Z] in
/-- Exactness is an open condition among continuously varying complexes. -/
theorem eventually_range_eq_ker
    (f : α → X →ₗ[ℝ] Y) (g : α → Y →ₗ[ℝ] Z) (a₀ : α)
    (hf : ∀ x, ContinuousAt (fun a => f a x) a₀)
    (hg : ∀ y, ContinuousAt (fun a => g a y) a₀)
    (hcomplex : ∀ a, (g a).comp (f a) = 0)
    (hexact : LinearMap.range (f a₀) = LinearMap.ker (g a₀)) :
    ∀ᶠ a in 𝓝 a₀, LinearMap.range (f a) = LinearMap.ker (g a) := by
  filter_upwards [eventually_finrank_range_ge f a₀ hf,
    eventually_finrank_range_ge g a₀ hg] with a hfr hgr
  have hle : LinearMap.range (f a) ≤ LinearMap.ker (g a) := by
    rintro y ⟨x, rfl⟩
    change g a (f a x) = 0
    exact LinearMap.congr_fun (hcomplex a) x
  apply Submodule.eq_of_le_of_finrank_le hle
  have hbase := (g a₀).finrank_range_add_finrank_ker
  have hnew := (g a).finrank_range_add_finrank_ker
  rw [hexact] at hfr
  omega

end Cubical.Exactness
