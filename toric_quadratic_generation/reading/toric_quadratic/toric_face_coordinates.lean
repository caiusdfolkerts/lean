module
public import PaperVerification.ToricNormalFan
public import PaperVerification.ToricIntegralAffine
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Finset.Sort
@[expose] public section
/-!
# Saturated coordinates on a subset of an integral basis

Selecting any subset of a genuine integral basis gives an injective integral
affine coordinate map whose real image has exactly the induced lattice.
These maps will be used as actual coordinates on faces of smooth polytopes.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

section BasisSelection

variable {R E ι κ : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [Fintype κ]

def selectedBasisMap (b : Module.Basis ι R E) (a : κ ↪ ι) : (κ → R) →ₗ[R] E :=
  Fintype.linearCombination R (fun i => b (a i))

@[simp] theorem selectedBasisMap_apply (b : Module.Basis ι R E) (a : κ ↪ ι) (x : κ → R) :
    selectedBasisMap b a x = ∑ i, x i • b (a i) := rfl

@[simp] theorem selectedBasisMap_coordinate (b : Module.Basis ι R E)
    (a : κ ↪ ι) (x : κ → R) (i : κ) :
    b.repr (selectedBasisMap b a x) (a i) = x i := by
  classical
  simp [selectedBasisMap_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, Finsupp.single_apply,
    a.injective.eq_iff, smul_eq_mul]

theorem selectedBasisMap_coordinate_eq_zero (b : Module.Basis ι R E)
    (a : κ ↪ ι) (x : κ → R) (j : ι) (hj : j ∉ Set.range a) :
    b.repr (selectedBasisMap b a x) j = 0 := by
  classical
  have hne (i : κ) : a i ≠ j := fun hi => hj ⟨i, hi⟩
  simp [selectedBasisMap_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, hne, smul_eq_mul]

theorem selectedBasisMap_injective (b : Module.Basis ι R E) (a : κ ↪ ι) :
    Function.Injective (selectedBasisMap b a) := by
  intro x y hxy
  funext i
  have h := congrArg (fun z => b.repr z (a i)) hxy
  simpa only [selectedBasisMap_coordinate] using h

/-- A selected-basis subspace is exactly the locus where all omitted basis
coordinates vanish. -/
theorem mem_range_selectedBasisMap_iff (b : Module.Basis ι R E) (a : κ ↪ ι) (x : E) :
    x ∈ Set.range (selectedBasisMap b a) ↔
      ∀ j ∉ Set.range a, b.repr x j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ j hj
    exact selectedBasisMap_coordinate_eq_zero b a t j hj
  · intro hx
    refine ⟨fun i => b.repr x (a i), ?_⟩
    apply b.ext_elem
    intro j
    by_cases hj : j ∈ Set.range a
    · obtain ⟨i, rfl⟩ := hj
      exact selectedBasisMap_coordinate b a (fun i => b.repr x (a i)) i
    · rw [selectedBasisMap_coordinate_eq_zero b a _ j hj, hx j hj]

theorem selectedBasisMap_repr_restrict (b : Module.Basis ι R E) (a : κ ↪ ι) (x : E)
    (hx : ∀ j ∉ Set.range a, b.repr x j = 0) :
    selectedBasisMap b a (fun i => b.repr x (a i)) = x := by
  obtain ⟨w, hw⟩ := (mem_range_selectedBasisMap_iff b a x).mpr hx
  have hcoord : w = fun i => b.repr x (a i) := by
    funext i
    rw [← hw, selectedBasisMap_coordinate]
  rw [← hcoord]
  exact hw

@[simp] theorem selectedBasisMap_single (b : Module.Basis ι R E) (a : κ ↪ ι)
    [DecidableEq κ] (i : κ) (r : R) :
    selectedBasisMap b a (Pi.single i r) = r • b (a i) :=
  Fintype.linearCombination_apply_single R (fun k => b (a k)) i r

end BasisSelection

/-- An integral selected-basis combination embeds as the identical real combination. -/
theorem embed_selectedBasisMap {d n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (z : Lattice d) :
    embed n (selectedBasisMap b a z) =
      selectedBasisMap (integralBasisReal b) a (embed d z) := by
  ext j
  simp [selectedBasisMap_apply, map_sum, integralBasisReal_apply, embed,
    Finset.sum_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]

/-- Selecting an integral basis subset and an integral origin defines an actual
saturated integral affine coordinate embedding. -/
def selectedBasisChart {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) :
    IntegralAffineEmbedding d n where
  origin := v
  linear := (selectedBasisMap b a).toAddMonoidHom
  realLinear := selectedBasisMap (integralBasisReal b) a
  injective := selectedBasisMap_injective _ _
  compatible := embed_selectedBasisMap b a
  saturated := by
    intro z hz
    have hzero := (mem_range_selectedBasisMap_iff (integralBasisReal b) a (embed n z)).mp hz
    have hzeroZ (j : Fin n) (hj : j ∉ Set.range a) : b.repr z j = 0 := by
      have h := hzero j hj
      rw [integralBasisReal_repr] at h
      exact Int.cast_eq_zero.mp h
    obtain ⟨w, hw⟩ := (mem_range_selectedBasisMap_iff b a z).mpr hzeroZ
    exact ⟨w, hw⟩

@[simp] theorem selectedBasisChart_realMap {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (x : Ambient d) :
    (selectedBasisChart v b a).realMap x =
      embed n v + ∑ i, x i • integralBasisReal b (a i) := rfl

@[simp] theorem selectedBasisChart_latticeMap {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (x : Lattice d) :
    (selectedBasisChart v b a).latticeMap x = v + ∑ i, x i • b (a i) := rfl

end PaperVerification.ToricGeometry
