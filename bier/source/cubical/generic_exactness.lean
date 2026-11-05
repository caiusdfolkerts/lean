import cubical.affine_path
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Generic exactness along an affine path

An affine family of finite-dimensional complexes that is exact at one
parameter is exact except at finitely many parameters. The argument uses
polynomial minors, then rank-nullity. No formula for a specific kernel is
assumed.
-/

namespace Cubical.Exactness

open Module

variable {X Y Z : Type*}
  [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- The rank of an affine family is at least its rank at a fixed parameter,
except at finitely many parameters. -/
theorem finite_setOf_finrank_range_lt (f : ℝ → X →ₗ[ℝ] Y) (t₀ : ℝ)
    (hf : ∀ x, ∃ a b : Y, ∀ t, f t x = a + t • b) :
    {t : ℝ | finrank ℝ (LinearMap.range (f t)) <
      finrank ℝ (LinearMap.range (f t₀))}.Finite := by
  classical
  let r := finrank ℝ (LinearMap.range (f t₀))
  let basis := Module.finBasis ℝ (LinearMap.range (f t₀))
  let v : Fin r → X := fun i =>
    Classical.choose (LinearMap.mem_range.mp (basis i).property)
  have hv : ∀ i, f t₀ (v i) = (basis i).val := fun i =>
    Classical.choose_spec (LinearMap.mem_range.mp (basis i).property)
  have hli : LinearIndependent ℝ (fun i => f t₀ (v i)) := by
    have hb := basis.linearIndependent.map' (LinearMap.range (f t₀)).subtype
      (Submodule.ker_subtype _)
    convert hb using 1
    funext i
    exact hv i
  choose a b hab using fun i => hf (v i)
  have hli' : LinearIndependent ℝ (fun i => a i + t₀ • b i) := by
    convert hli using 1
    funext i
    exact (hab i t₀).symm
  refine hli'.finite_setOf_not_along_affine_path.subset ?_
  intro t ht hgood
  have hgood' : LinearIndependent ℝ (fun i => f t (v i)) := by
    convert hgood using 1
    funext i
    exact hab i t
  let u : Fin r → LinearMap.range (f t) := fun i =>
    ⟨f t (v i), LinearMap.mem_range_self _ _⟩
  have hu : LinearIndependent ℝ u :=
    LinearIndependent.of_comp (LinearMap.range (f t)).subtype hgood'
  have hle := hu.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  exact Nat.not_lt_of_ge hle ht

/-- An affine family of complexes that is exact at one parameter is exact
outside a finite set of real parameters. -/
theorem finite_setOf_range_ne_ker
    (f : ℝ → X →ₗ[ℝ] Y) (g : ℝ → Y →ₗ[ℝ] Z) (t₀ : ℝ)
    (hf : ∀ x, ∃ a b : Y, ∀ t, f t x = a + t • b)
    (hg : ∀ y, ∃ a b : Z, ∀ t, g t y = a + t • b)
    (hcomplex : ∀ t, (g t).comp (f t) = 0)
    (hexact : LinearMap.range (f t₀) = LinearMap.ker (g t₀)) :
    {t : ℝ | LinearMap.range (f t) ≠ LinearMap.ker (g t)}.Finite := by
  refine ((finite_setOf_finrank_range_lt f t₀ hf).union
    (finite_setOf_finrank_range_lt g t₀ hg)).subset ?_
  intro t ht
  by_contra hbad
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hbad
  apply ht
  have hle : LinearMap.range (f t) ≤ LinearMap.ker (g t) := by
    rintro y ⟨x, rfl⟩
    change g t (f t x) = 0
    exact LinearMap.congr_fun (hcomplex t) x
  apply Submodule.eq_of_le_of_finrank_le hle
  have hbase := (g t₀).finrank_range_add_finrank_ker
  have hnew := (g t).finrank_range_add_finrank_ker
  rw [hexact] at hbad
  omega

end Cubical.Exactness
