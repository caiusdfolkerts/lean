import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Lean.Elab.Tactic.Omega

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions

noncomputable section

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

def cochainDegreeShiftEmbedding (k : ℕ) : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => k+n) (fun _ _ h => Nat.add_left_cancel h)
    (by intro i j; change (i+1=j) ↔ (k+i+1=k+j); omega)

instance cochainDegreeShiftEmbedding_isRelIff (k : ℕ) : (cochainDegreeShiftEmbedding k).IsRelIff := by
  unfold cochainDegreeShiftEmbedding
  infer_instance

instance cochainDegreeShiftEmbedding_isTruncGE (k : ℕ) : (cochainDegreeShiftEmbedding k).IsTruncGE where
  mem_next {j l} h := by
    refine ⟨j+1,?_⟩
    change k+j+1=l at h
    change k+(j+1)=l
    omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions
