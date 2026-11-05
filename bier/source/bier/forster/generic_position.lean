import bier.forster.gram_determinant
import bier.sign_rank
import cubical.generic_rigidity

/-! # Sign-preserving perturbation to general linear position

Strict signs define an open set.  The finite intersection of the dense open
sets of independent maximal tuples therefore meets that same sign cell.
-/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix

variable {k n : ℕ} {C : Type*} [Fintype C]

theorem exists_generic_sign_factor (H : Matrix (Fin n) C ℝ)
    (U : Matrix (Fin k) (Fin n) ℝ) (V : Matrix (Fin k) C ℝ)
    (hUV : Bier.SignRealizes H (Uᵀ * V)) :
    ∃ U' : Matrix (Fin k) (Fin n) ℝ,
      Bier.SignRealizes H (U'ᵀ * V) ∧
      ∀ S : KSubset (Fin n) k, 0 < minorSquare U' S := by
  let E := EuclideanSpace ℝ (Fin k)
  let emb (S : KSubset (Fin n) k) : Fin k ↪ Fin n :=
    (S.val.orderEmbOfFin (mem_powersetCard.mp S.property).2).toEmbedding
  let good (S : KSubset (Fin n) k) : Set (Fin n → E) :=
    {p | LinearIndependent ℝ (p ∘ emb S)}
  have hd : Dense (⋂ S, good S) :=
    Cubical.dense_iInter_finite good
      (fun S => Cubical.Rigidity.isOpen_setOf_linearIndependent_precomp (emb S))
      (fun S => Cubical.Rigidity.dense_setOf_linearIndependent_precomp (emb S)
        (by simp [E]))
  let signs : Set (Fin n → E) :=
    {p | ∀ r c, 0 < H r c * ∑ a, (p r) a * V a c}
  have hopen : IsOpen signs := by
    simp only [signs, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro r
    apply isOpen_iInter_of_finite
    intro c
    apply isOpen_lt continuous_const
    change Continuous (fun p : Fin n → EuclideanSpace ℝ (Fin k) =>
      H r c * ∑ a, (p r) a * V a c)
    fun_prop
  have hne : signs.Nonempty := by
    refine ⟨fun r => WithLp.toLp 2 (fun a => U a r), ?_⟩
    intro r c
    exact hUV r c
  obtain ⟨p, hps, hp⟩ := hd.inter_open_nonempty signs hopen hne
  refine ⟨fun a r => (p r) a, ?_, ?_⟩
  · intro r c
    exact hps r c
  · intro S
    have hi : LinearIndependent ℝ (p ∘ emb S) := Set.mem_iInter.mp hp S
    have hic := hi.map' (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective)
    have hu : IsUnit (CauchyBinet.colsSubmatrix (fun a r => (p r) a) S.val
        (mem_powersetCard.mp S.property).2) := by
      apply Matrix.linearIndependent_col_iff_isUnit.mp
      exact hic
    exact sq_pos_of_ne_zero (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu))

end Bier.Forster
