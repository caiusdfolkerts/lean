module

public import Papers.GraphicalZonotopes.SetFunction

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ElementallyNonnegative.difference_mono {z : SetFunction V}
    (hz : ElementallyNonnegative z) {A B : Finset V} (hAB : A ⊆ B)
    (D : Finset V) (hDB : Disjoint D B) :
    z (A ∪ D) - z A ≤ z (B ∪ D) - z B := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d D hd ih =>
    have hDB' : Disjoint D B := hDB.mono_left (subset_insert d D)
    have hdB : d ∉ B := fun h => Finset.disjoint_left.mp hDB (mem_insert_self _ _) h
    have hdBD : d ∉ B ∪ D := by simp [hd, hdB]
    have h1 := ih hDB'
    have h2 := hz.marginal (show A ∪ D ⊆ B ∪ D from union_subset_union hAB (subset_refl D)) hdBD
    rw [union_insert, union_insert]
    linarith

theorem ElementallyNonnegative.supermodular {z : SetFunction V}
    (hz : ElementallyNonnegative z) : Supermodular z := by
  classical
  intro A B
  have h := hz.difference_mono (inter_subset_left : A ∩ B ⊆ A)
    (B \ A) Finset.disjoint_sdiff.symm
  have he : (A ∩ B) ∪ (B \ A) = B := by
    ext x
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto
  have he' : A ∪ (B \ A) = A ∪ B := union_sdiff_self_eq_union
  rw [he, he'] at h
  linarith

theorem supermodular_iff_elemental (z : SetFunction V) :
    Supermodular z ↔ ElementallyNonnegative z :=
  ⟨Supermodular.elemental, ElementallyNonnegative.supermodular⟩

@[simp] theorem delta_add (z w : SetFunction V) (u v : V) (S : Finset V) :
    delta (z + w) u v S = delta z u v S + delta w u v S := by
  simp only [delta, Pi.add_apply]; ring

@[simp] theorem delta_sub (z w : SetFunction V) (u v : V) (S : Finset V) :
    delta (z - w) u v S = delta z u v S - delta w u v S := by
  simp only [delta, Pi.sub_apply]; ring

@[simp] theorem delta_smul (a : ℝ) (z : SetFunction V) (u v : V) (S : Finset V) :
    delta (a • z) u v S = a * delta z u v S := by
  simp only [delta, Pi.smul_apply, smul_eq_mul]; ring

def deltaLinear (u v : V) (S : Finset V) : SetFunction V →ₗ[ℝ] ℝ where
  toFun z := delta z u v S
  map_add' z w := delta_add z w u v S
  map_smul' a z := delta_smul a z u v S

@[simp] theorem delta_sum {I : Type*} (t : Finset I) (z : I → SetFunction V)
    (u v : V) (S : Finset V) :
    delta (∑ i ∈ t, z i) u v S = ∑ i ∈ t, delta (z i) u v S :=
  map_sum (deltaLinear u v S) z t

def modular (x : V → ℝ) : SetFunction V := subsetSum x

theorem delta_modular (x : V → ℝ) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) : delta (modular x) u v S = 0 := by
  simp only [delta, modular]
  rw [subsetSum_insert (by simp [huv, hu]), subsetSum_insert hu, subsetSum_insert hv]
  ring

theorem modular_supermodular (x : V → ℝ) : Supermodular (modular x) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [delta_modular x huv hu hv]

theorem zero_elemental_modular {z : SetFunction V} (hzero : Normalized z)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0) :
    z = modular (fun v => z {v}) := by
  have hmarg : ∀ S : Finset V, ∀ v, v ∉ S → z (insert v S) = z {v} + z S := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro v hv; simp [Normalized] at hzero; simp [hzero]
    | @insert u S hu ih =>
      intro v hv
      have hvS : v ∉ S := fun h => hv (mem_insert_of_mem h)
      have hvu : v ≠ u := by intro h; subst v; exact hv (mem_insert_self _ _)
      have h := hz v u hvu S hvS hu
      dsimp [delta] at h
      rw [ih v hvS] at h
      linarith
  funext S
  induction S using Finset.induction_on with
  | empty => simpa [modular, Normalized] using hzero
  | @insert v S hv ih =>
    rw [hmarg S v hv]
    change _ = subsetSum (fun w => z {w}) (insert v S)
    rw [subsetSum_insert hv]
    exact congrArg (z {v} + ·) ih

theorem normalized_zero_elemental_eq_zero {z : SetFunction V}
    (hn : TranslationNormalized z)
    (hz : ∀ u v, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0) : z = 0 := by
  rw [zero_elemental_modular hn.1 hz]
  funext S
  simp [modular, subsetSum, hn.2]

end GraphicalZonotopes
