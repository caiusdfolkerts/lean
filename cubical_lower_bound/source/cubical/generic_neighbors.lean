import cubical.generic_rank

/-!
# Generic independence of neighbor parameters

Any at most `d` distinct white vertices can be assigned independent vectors
in `ℝ^d`. The corresponding polynomial column matrix can therefore be added
to the finite family of full-rank conditions used for local propagation.
-/

namespace Cubical

open Matrix

noncomputable def neighborPolynomialMatrix {W I : Type*} (d : ℕ) (w : I → W) :
    Matrix (Fin d) I (MvPolynomial (W × Fin d) ℝ) :=
  fun i a ↦ MvPolynomial.X (w a, i)

theorem neighborMatrix_injective_iff {W I : Type*} [Fintype I]
    (d : ℕ) (w : I → W) (p : W × Fin d → ℝ) :
    Function.Injective (evalMatrix (neighborPolynomialMatrix d w) p).mulVec ↔
      LinearIndependent ℝ (fun a i ↦ p (w a, i)) := by
  rw [Matrix.mulVec_injective_iff]
  have heq : (evalMatrix (neighborPolynomialMatrix d w) p).col =
      (fun a i ↦ p (w a, i)) := by
    funext a i
    simp [evalMatrix, neighborPolynomialMatrix, Matrix.col]
  rw [heq]

theorem neighborMatrix_has_injective_specialization {W I : Type*} [Fintype I]
    (d : ℕ) (w : I → W) (hw : Function.Injective w) (hc : Fintype.card I ≤ d) :
    ∃ p : W × Fin d → ℝ,
      Function.Injective (evalMatrix (neighborPolynomialMatrix d w) p).mulVec := by
  classical
  let f : I → Fin d := fun a ↦ Fin.castLE hc ((Fintype.equivFin I) a)
  have hf : Function.Injective f :=
    (Fin.castLE_injective hc).comp (Fintype.equivFin I).injective
  let q : I → Fin d → ℝ := fun a ↦ (Pi.basisFun ℝ (Fin d)) (f a)
  have hq : LinearIndependent ℝ q := (Pi.basisFun ℝ (Fin d)).linearIndependent.comp f hf
  let p : W × Fin d → ℝ := fun wi ↦ Function.extend w q (fun _ _ ↦ 0) wi.1 wi.2
  refine ⟨p, (neighborMatrix_injective_iff d w p).mpr ?_⟩
  have heq : (fun a i ↦ p (w a, i)) = q := by
    funext a i
    simp [p, hw.extend_apply]
  rw [heq]
  exact hq

end Cubical
