import bier.ghost_schur_signs
import bier.schur_core

/-!
# Theorem 2: the geometric sign-rank obstruction

The hypothesis is genuine polytopality, using actual convex hulls and their
entire simplicial boundaries. The Schur signs and all matrix-rank bounds
are derived from this hypothesis.
-/

noncomputable section

namespace Bier

open Classical Finset Matrix

variable {U C R : Type*} [Fintype U] [Fintype C] [Fintype R]
  [DecidableEq U] [DecidableEq C]

theorem exists_core_schur_realization (K : Complex (U ⊕ C)) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (S : R → Finset U)
    (hSface : ∀ r, K.face ((S r).disjSum ∅))
    (H : Matrix R C ℝ) (hH : IsSignMatrix H)
    (hsign : ∀ r c, H r c = 1 ↔ K.face ((S r).disjSum {c}))
    (hP : Polytopal (ghostBier K)) :
    ∃ (G : Matrix U U ℝ) (d : C → ℝ) (u v : C → U → ℝ),
      (∀ r, IsUnit (principalMatrix G (S r)).det) ∧
        SignRealizes H (schurFeatureMatrix G S d u v) := by
  obtain ⟨X, hX⟩ := ghost_schur_signs K hK hv hP
  let G := X.submatrix Sum.inl Sum.inl
  let d : C → ℝ := fun c => -X (Sum.inr c) (Sum.inr c)
  let u : C → U → ℝ := fun c i => -X (Sum.inr c) (Sum.inl i)
  let v : C → U → ℝ := fun c i => X (Sum.inl i) (Sum.inr c)
  have hA (r : R) : K.face ((S r).map Function.Embedding.inl) := by
    have he : (S r).map Function.Embedding.inl = (S r).disjSum (∅ : Finset C) := by
      ext x
      cases x <;> simp
    rw [he]
    exact hSface r
  refine ⟨G, d, u, v, ?_, ?_⟩
  · intro r
    exact principalMatrix_map_isUnit X Function.Embedding.inl (S r) (hX _ (hA r)).1
  · intro r c
    change 0 < H r c * (-X (Sum.inr c) (Sum.inr c) -
      quadraticEvaluation (fun i => -X (Sum.inr c) (Sum.inl i))
        (fun i => X (Sum.inl i) (Sum.inr c))
        (paddedPrincipalInverse (X.submatrix Sum.inl Sum.inl) (S r)))
    rw [← neg_schurValue_core]
    have hsigns := (hX _ (hA r)).2 (Sum.inr c) (by simp)
    have he : insert (Sum.inr c) ((S r).map Function.Embedding.inl) = (S r).disjSum {c} := by
      ext x
      cases x <;> simp
    rcases hH r c with hp | hn
    · have hface : K.face (insert (Sum.inr c) ((S r).map Function.Embedding.inl)) := by
        rw [he]
        exact (hsign r c).mp hp
      have hh := hsigns.1 hface
      rw [hp]
      linarith
    · have hface : ¬ K.face (insert (Sum.inr c) ((S r).map Function.Embedding.inl)) := by
        intro hf
        rw [he] at hf
        have h1 := (hsign r c).mpr hf
        rw [hn] at h1
        norm_num at h1
      have hh := hsigns.2 hface
      rw [hn]
      nlinarith

/-- The fixed-positive-cardinality assertion of Theorem 2, with all
quantifiers over selected faces and anchors retained. -/
theorem ghost_signRank_bound_fixedCard (K : Complex (U ⊕ C)) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (S : R → Finset U) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ r, (S r).card = k) (hSface : ∀ r, K.face ((S r).disjSum ∅))
    (H : Matrix R C ℝ) (hH : IsSignMatrix H)
    (hsign : ∀ r c, H r c = 1 ↔ K.face ((S r).disjSum {c}))
    (hP : Polytopal (ghostBier K)) :
    signRank H ≤ Fintype.card U ^ 2 - Fintype.card U + 1 := by
  obtain ⟨G, d, u, v, hG, hreal⟩ :=
    exists_core_schur_realization K hK hv S hSface H hH hsign hP
  exact (signRank_le_rank hreal).trans
    (schurFeatureMatrix_rank_fixedCard G S hG k hk hcard d u v)

/-- The arbitrary-cardinality assertion of Theorem 2. The empty selected
face is allowed, and the sole extra feature is the constant coordinate. -/
theorem ghost_signRank_bound_arbitrary (K : Complex (U ⊕ C)) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (S : R → Finset U)
    (hSface : ∀ r, K.face ((S r).disjSum ∅))
    (H : Matrix R C ℝ) (hH : IsSignMatrix H)
    (hsign : ∀ r c, H r c = 1 ↔ K.face ((S r).disjSum {c}))
    (hP : Polytopal (ghostBier K)) :
    signRank H ≤ Fintype.card U ^ 2 - Fintype.card U + 2 := by
  obtain ⟨G, d, u, v, hG, hreal⟩ :=
    exists_core_schur_realization K hK hv S hSface H hH hsign hP
  exact (signRank_le_rank hreal).trans
    (schurFeatureMatrix_rank_arbitrary G S hG d u v)

end Bier
