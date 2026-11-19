module

public import Unimodular.RayHyperplanes
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Fintype.Pi

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set

namespace Unimodular.EffectiveDirection

variable {n : ℕ} {K E : Type*} [Fintype K] [Fintype E]

/-- A genuinely finite, decidable test on a natural search parameter. -/
def Avoids (a : K → Fin n → ℤ) (t : ℕ) : Prop :=
  0 < t ∧ ∀ k, (∃ i, a k i ≠ 0) → ∑ i, a k i * (t : ℤ) ^ i.val ≠ 0

instance (a : K → Fin n → ℤ) (t : ℕ) : Decidable (Avoids a t) := by
  unfold Avoids
  infer_instance

theorem exists_parameter (a : K → Fin n → ℤ) : ∃ t, Avoids a t := by
  let J := {k : K // ∃ i, a k i ≠ 0}
  obtain ⟨t, ht, ha⟩ := GenericWeights.exists_geometric_progression
    (fun k : J => a k.val) (fun k => k.property)
  refine ⟨t.toNat, ?_, ?_⟩
  · omega
  · intro k hk
    simpa only [Int.toNat_of_nonneg ht.le] using ha ⟨k, hk⟩

/-- Terminating unbounded natural search. Its existence proof is erased from
execution; the predicate contains only finite integer arithmetic. -/
def parameter (a : K → Fin n → ℤ) : ℕ := Nat.find (exists_parameter a)

def vector (a : K → Fin n → ℤ) : Fin n → ℤ :=
  fun i => (parameter a : ℤ) ^ i.val

theorem vector_avoids (a : K → Fin n → ℤ) (k : K)
    (hk : ∃ i, a k i ≠ 0) : ∑ i, a k i * vector a i ≠ 0 :=
  (Nat.find_spec (exists_parameter a)).2 k hk

/-- Determinant with one varying row, as an executable integer linear form. -/
def rowForm (b : Fin n → Fin n → ℤ) (i : Fin n) :
    (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  Matrix.detRowAlternating.toMultilinearMap.toLinearMap b i

@[simp] theorem rowForm_apply (b : Fin n → Fin n → ℤ) (i : Fin n)
    (x : Fin n → ℤ) : rowForm b i x = Matrix.det (Function.update b i x) := rfl

def coefficients (u : E → Fin n → ℤ) :
    ((Fin n → E) × Fin n) → Fin n → ℤ :=
  fun p j => rowForm (u ∘ p.1) p.2 (Pi.single j 1)

/-- An executable integer direction from raw finite integral ray coordinates.
No basis, generic direction, or geometric-decision oracle is an input. -/
def direction (u : E → Fin n → ℤ) : Fin n → ℤ := vector (coefficients u)

theorem rowForm_eq_sum (b : Fin n → Fin n → ℤ) (i : Fin n)
    (x : Fin n → ℤ) :
    rowForm b i x = ∑ j, rowForm b i (Pi.single j 1) * x j := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem rowForm_coefficients_nonzero (b : Fin n → Fin n → ℤ) (i : Fin n)
    (hb : Matrix.det b ≠ 0) : ∃ j, rowForm b i (Pi.single j 1) ≠ 0 := by
  by_contra! h
  have he : rowForm b i (b i) = 0 := by
    rw [rowForm_eq_sum]
    exact Finset.sum_eq_zero (fun j _ => by rw [h j, zero_mul])
  exact hb (by simpa only [rowForm_apply, Function.update_eq_self] using he)

/-- Every coordinate hyperplane of every nonsingular ray tuple is avoided. -/
theorem direction_avoids_rows (u : E → Fin n → ℤ) (a : Fin n → E) (i : Fin n)
    (ha : Matrix.det (u ∘ a) ≠ 0) : rowForm (u ∘ a) i (direction u) ≠ 0 := by
  rw [rowForm_eq_sum]
  exact vector_avoids (coefficients u) (a, i)
    (rowForm_coefficients_nonzero (u ∘ a) i ha)

noncomputable section

/-- The real extension of the same explicitly computed determinant form. -/
def realRowForm (b : Fin n → Fin n → ℤ) (i : Fin n) :
    Ambient n →ₗ[ℝ] ℝ :=
  Matrix.detRowAlternating.toMultilinearMap.toLinearMap (fun j => embed (b j)) i

theorem realRowForm_embed (b : Fin n → Fin n → ℤ) (i : Fin n) (x : Lattice n) :
    realRowForm b i (embed x) = (rowForm b i x : ℝ) := by
  change Matrix.det (Function.update (fun j => embed (b j)) i (embed x)) =
    ((Matrix.det (Function.update b i x) : ℤ) : ℝ)
  rw [Int.cast_det]
  congr 1
  ext j k
  by_cases hj : j = i
  · subst j
    simp [embed]
  · simp [Function.update_of_ne hj, embed]

/-- A basis of the real space selected from the original integer vectors can
be taken to contain an independent spanning subset of any prescribed ray span. -/
theorem exists_tuple_and_missing_row (u : E → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (s : Finset E) (hs : RayHyperplanes.raySpan (fun e => embed (u e)) s ≠ ⊤) :
    ∃ (a : Fin n → E) (i : Fin n), Matrix.det (u ∘ a) ≠ 0 ∧
      RayHyperplanes.raySpan (fun e => embed (u e)) s ≤ LinearMap.ker (realRowForm (u ∘ a) i) := by
  classical
  let S := (fun e => embed (u e)) '' (s : Set E)
  obtain ⟨T, hTS, hsp, hLI⟩ := exists_linearIndependent ℝ S
  have hT : Set.range (fun x : T => (x : Ambient n)) ⊆
      Set.range (fun e => embed (u e)) := by
    rintro x ⟨t, rfl⟩
    obtain ⟨e, he, hx⟩ := hTS t.property
    exact ⟨e, hx⟩
  let B := Module.Basis.extendLe hLI.linearIndepOn_id hT hspan.ge
  let B' := B.reindex (B.indexEquiv (Pi.basisFun ℝ (Fin n)))
  have hBU : Set.range B' ⊆ Set.range (fun e => embed (u e)) := by
    rw [show Set.range B' = Set.range B from B.range_reindex _]
    exact Module.Basis.extendLe_subset hLI.linearIndepOn_id hT hspan.ge
  have hTB : T ⊆ Set.range B' := by
    rw [show Set.range B' = Set.range B from B.range_reindex _]
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      Module.Basis.subset_extendLe hLI.linearIndepOn_id hT hspan.ge
  have hcol : ∀ i : Fin n, ∃ e : E, embed (u e) = B' i := fun i => hBU ⟨i, rfl⟩
  choose a ha using hcol
  have hb : (fun i => embed (u (a i))) = B' := funext ha
  have hdetR : Matrix.det (fun i => embed (u (a i))) ≠ 0 := by
    rw [hb]
    simpa only [Pi.basisFun_det, Matrix.det] using (Pi.basisFun ℝ (Fin n)).isUnit_det B' |>.ne_zero
  have hdet : Matrix.det (u ∘ a) ≠ 0 := by
    intro hz
    apply hdetR
    have he : ((Matrix.det (u ∘ a) : ℤ) : ℝ) = Matrix.det (fun i => embed (u (a i))) := by
      rw [Int.cast_det]
      rfl
    rw [← he, hz, Int.cast_zero]
  have himissing : ∃ i, B' i ∉ Submodule.span ℝ S := by
    by_contra! h
    apply hs
    apply top_unique
    change (⊤ : Submodule ℝ (Ambient n)) ≤ Submodule.span ℝ S
    rw [← B'.span_eq]
    apply Submodule.span_le.2
    rintro x ⟨i, hi⟩
    rw [← hi]
    exact h i
  obtain ⟨i, hi⟩ := himissing
  refine ⟨a, i, hdet, ?_⟩
  change Submodule.span ℝ S ≤ _
  rw [← hsp]
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨j, hj⟩ := hTB hx
  have hij : i ≠ j := by
    intro he
    apply hi
    rw [he, hj]
    exact Submodule.subset_span (hTS hx)
  change realRowForm (u ∘ a) i x = 0
  change Matrix.det (Function.update (fun j => embed (u (a j))) i x) = 0
  rw [hb, ← hj]
  exact Matrix.detRowAlternating.map_update_self B' hij

/-- The raw-coordinate algorithm avoids every proper ray-generated span,
so in particular it meets the exact generic-direction condition in §3. -/
theorem direction_not_mem_proper_span (u : E → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤)
    (s : Finset E) (hs : RayHyperplanes.raySpan (fun e => embed (u e)) s ≠ ⊤) :
    embed (direction u) ∉ RayHyperplanes.raySpan (fun e => embed (u e)) s := by
  obtain ⟨a, i, ha, hker⟩ := exists_tuple_and_missing_row u hspan s hs
  intro hx
  have hz : realRowForm (u ∘ a) i (embed (direction u)) = 0 := hker hx
  rw [realRowForm_embed] at hz
  exact direction_avoids_rows u a i ha (Int.cast_eq_zero.mp hz)

theorem direction_generic (u : E → Lattice n)
    (hspan : Submodule.span ℝ (Set.range (fun e => embed (u e))) = ⊤) :
    RayHyperplanes.GenericDirection (fun e => embed (u e)) (embed (direction u)) := by
  intro s hs
  apply direction_not_mem_proper_span u hspan s
  intro ht
  rw [ht, finrank_top] at hs
  omega

end
end Unimodular.EffectiveDirection

#print axioms Unimodular.EffectiveDirection.direction
#print axioms Unimodular.EffectiveDirection.direction_not_mem_proper_span
#print axioms Unimodular.EffectiveDirection.direction_generic
#check Unimodular.EffectiveDirection.direction_generic
