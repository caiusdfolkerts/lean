module
public import graph_foundation.part013
public import shared_results.part019_finite_rees_koszul_equiv

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.AssociatedCommutativeRing -/
section

/-!
# The commutative ring structure on the actual associated coefficient algebra

The ring parent is the same canonical quotient ring used by the filtration
and its symbol maps. This makes the commutative coefficient Koszul complex
use exactly that ring structure, with no alternate quotient dictionary.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  (F : MultiplicativeFiltration K A)

/-- Commutativity is proved through the actual surjective symbol map; the
underlying ring remains `associatedGradedRing`. -/
instance (priority := 1300) associatedGradedCommRing : CommRing F.AssociatedGraded where
  __ := associatedGradedRing F
  mul_comm a b := by
    obtain ⟨x, rfl⟩ := F.leadingMap_surjective a
    obtain ⟨y, rfl⟩ := F.leadingMap_surjective b
    calc
      F.leadingMap x * F.leadingMap y = F.leadingMap (x * y) :=
        (map_mul F.leadingMap x y).symm
      _ = F.leadingMap (y * x) := congrArg F.leadingMap (Subtype.ext (mul_comm x.val y.val))
      _ = F.leadingMap y * F.leadingMap x := map_mul F.leadingMap y x

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
