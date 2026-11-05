import bier.sign_rank

/-! # A factorization through the actual matrix rank -/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix Module

variable {R C : Type*} [Fintype R] [Fintype C]

theorem exists_rank_factorization (M : Matrix R C ℝ) :
    ∃ U : Matrix (Fin M.rank) R ℝ, ∃ V : Matrix (Fin M.rank) C ℝ,
      Uᵀ * V = M := by
  let W := LinearMap.range M.mulVecLin
  let b : Basis (Fin M.rank) ℝ W := Module.finBasis ℝ W
  let col (c : C) : W := ⟨fun r => M r c, by
    refine ⟨Pi.single c 1, ?_⟩
    change M *ᵥ Pi.single c 1 = fun r => M r c
    exact Matrix.mulVec_single_one M c⟩
  refine ⟨fun a r => (b a).val r, fun a c => b.repr (col c) a, ?_⟩
  ext r c
  change (∑ a, (b a).val r * b.repr (col c) a) = M r c
  have he := congrArg (fun x : W => x.val r) (b.sum_repr (col c))
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Submodule.coe_sum,
    Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using he

end Bier.Forster
