module

public import ToricPower.LatticeShrinking

/-!
# Shrinking onto an integral translate of a rational subspace

The center of an arrangement cell need not belong to its direction
space. The integral affine-slice lemma puts it in an integral translate
of that space. This version of the lattice shrinking theorem keeps the
translate in the formula, for every sufficiently large integer power.
-/

@[expose] public noncomputable section

open Set Module

namespace ToricPower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An arbitrary bounded test shrinks to a prescribed point of an
integral affine translate, while the inverse image of that affine
translate stays the prescribed integral translate of the test slice. -/
theorem bounded_test_shrinks_for_every_integer_of_affine_span
    (V : Submodule ℝ E) (L : AddSubgroup E)
    (hspan : Submodule.span ℝ
      (L.comap V.subtype.toAddMonoidHom : Set V) = ⊤)
    (x v₀ : E) (hv₀ : v₀ ∈ L) (hx : x - v₀ ∈ V)
    (m : E) (hm : m ∈ L) (K : Set E) (hK : Bornology.IsBounded K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ ℓ : ℕ, N ≤ ℓ →
      ∃ u ∈ L, u + m - (ℓ : ℝ) • v₀ ∈ V ∧
        (fun z : E => (ℓ : ℝ)⁻¹ • (u + z)) '' K ⊆ Metric.ball x ε := by
  obtain ⟨N,positive,shrink⟩ := bounded_test_shrinks_for_every_integer_of_span
    V L hspan ⟨x - v₀,hx⟩ m hm K hK ε hε
  refine ⟨N,positive,fun ℓ large => ?_⟩
  obtain ⟨u,hu,compatible,small⟩ := shrink ℓ large
  have powerPositive : (0 : ℝ) < ℓ := by exact_mod_cast positive.trans_le large
  have translateIntegral : (ℓ : ℝ) • v₀ ∈ L := by
    rw [Nat.cast_smul_eq_nsmul]
    exact L.nsmul_mem hv₀ ℓ
  refine ⟨u + (ℓ : ℝ) • v₀,L.add_mem hu translateIntegral,?_,?_⟩
  · convert compatible using 1 <;> abel
  · rintro _ ⟨z,hz,rfl⟩
    have near := small (Set.mem_image_of_mem _ hz)
    rw [Metric.mem_ball,dist_eq_norm] at near ⊢
    convert near using 1
    congr 1
    have scale : (ℓ : ℝ)⁻¹ • ((u + (ℓ : ℝ) • v₀) + z) =
        (ℓ : ℝ)⁻¹ • (u + z) + v₀ := by
      rw [show (u + (ℓ : ℝ) • v₀) + z = (u + z) + (ℓ : ℝ) • v₀ by abel,
        smul_add,smul_smul,inv_mul_cancel₀ powerPositive.ne',one_smul]
    change (ℓ : ℝ)⁻¹ • ((u + (ℓ : ℝ) • v₀) + z) - x =
      (ℓ : ℝ)⁻¹ • (u + z) - (x - v₀)
    rw [scale]
    change (ℓ : ℝ)⁻¹ • (u + z) + v₀ - x =
      (ℓ : ℝ)⁻¹ • (u + z) - (x - v₀)
    abel

end ToricPower

end
