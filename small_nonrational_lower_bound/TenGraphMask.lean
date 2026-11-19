module
prelude
public import TenGraphEdges

@[expose] public section

namespace Papers.RationalityTen.TenGraphEdges

/-- The same unordered pair in the ten-bit vertex-mask convention used by
literal facet cells. -/
def edgeMask (edge : Fin 45) : Nat :=
  2 ^ (first edge).val + 2 ^ (second edge).val

theorem edgeMask_lt (edge : Fin 45) : edgeMask edge < 1024 := by
  have checked : (List.finRange 45).all (fun edge => decide (edgeMask edge < 1024)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked edge (List.mem_finRange edge))

end Papers.RationalityTen.TenGraphEdges
