module
prelude
import GraphLargeRow29Case01592Cases
import GraphLargeRow29Case01934Cases
import GraphLargeRow29Case03359Cases
import GraphLargeRow29Case03786Cases
import GraphLargeRow29Case04142Cases
import GraphLargeRow29Case04162Cases
import GraphLargeRow29Case04211Cases
import GraphLargeRow31Case00844Cases
public import GraphCaseCertificate
public import GraphRouteCasesData

noncomputable section
namespace Papers.RationalityTen.GraphFiniteDispatch
open ConcreteGrowth GraphCaseCertificate

private def largeResults : Table {key : GraphRouteSelector.Key // Result key} :=
(.branch 4 (.branch 2 (.branch 1 (.leaf ⟨(29, 14302797434912), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01934.record000_result⟩) (.leaf ⟨(29, 32780335513600), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04162.record000_result⟩)) (.branch 3 (.leaf ⟨(31, 13890478416128), Papers.RationalityTen.CompactReplay.GraphLargeRow31Case00844.record000_result⟩) (.leaf ⟨(29, 32530116968448), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04142.record000_result⟩))) (.branch 6 (.branch 5 (.leaf ⟨(29, 12133574119680), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case01592.record000_result⟩) (.leaf ⟨(29, 25771970199552), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case03359.record000_result⟩)) (.branch 7 (.leaf ⟨(29, 29414369280128), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case03786.record000_result⟩) (.leaf ⟨(29, 33751002251264), Papers.RationalityTen.CompactReplay.GraphLargeRow29Case04211.record000_result⟩))))
private theorem large_keys_checked (i : Fin 8) :
    (largeResults.get i.val).val = GraphRoutes.largeKeys.entry i.val := by
  revert i
  decide +kernel

public theorem large_resolved (i : Nat) (hi : i < GraphRoutes.largeKeys.count) :
    Result (GraphRoutes.largeKeys.entry i) := by
  have hkey := large_keys_checked ⟨i, hi⟩
  exact hkey ▸ (largeResults.get i).property
#print axioms large_resolved
end Papers.RationalityTen.GraphFiniteDispatch
