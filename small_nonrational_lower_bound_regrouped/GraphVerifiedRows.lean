module
prelude
public import GraphCompactDispatch
public import GraphLargeDispatch
public import GraphEmptyDispatch
public import GraphRoutesVerified

@[expose] public section
namespace Papers.RationalityTen.GraphFiniteDispatch
open GraphCaseCertificate GraphRowSpecifications GraphRouteSelector

theorem cases_resolved : Resolved Result GraphRoutes.cases :=
  ⟨empty_resolved, compact_resolved, large_resolved⟩

theorem verified16 (i : Fin (rowOfCode 16).graphCount) :
    Result ((rowOfCode 16).key i.val) :=
  GraphRoutes.Row16.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row16.row rfl complement h) i

theorem verified19 (i : Fin (rowOfCode 19).graphCount) :
    Result ((rowOfCode 19).key i.val) :=
  GraphRoutes.Row19.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row19.row rfl complement h) i

theorem verified23 (i : Fin (rowOfCode 23).graphCount) :
    Result ((rowOfCode 23).key i.val) :=
  GraphRoutes.Row23.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row23.row rfl complement h) i

theorem verified24 (i : Fin (rowOfCode 24).graphCount) :
    Result ((rowOfCode 24).key i.val) :=
  GraphRoutes.Row24.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row24.row rfl complement h) i

theorem verified25 (i : Fin (rowOfCode 25).graphCount) :
    Result ((rowOfCode 25).key i.val) :=
  GraphRoutes.Row25.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row25.row rfl complement h) i

theorem verified26 (i : Fin (rowOfCode 26).graphCount) :
    Result ((rowOfCode 26).key i.val) :=
  GraphRoutes.Row26.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row26.row rfl complement h) i

theorem verified27 (i : Fin (rowOfCode 27).graphCount) :
    Result ((rowOfCode 27).key i.val) :=
  GraphRoutes.Row27.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row27.row rfl complement h) i

theorem verified28 (i : Fin (rowOfCode 28).graphCount) :
    Result ((rowOfCode 28).key i.val) :=
  GraphRoutes.Row28.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row28.row rfl complement h) i

theorem verified29 (i : Fin (rowOfCode 29).graphCount) :
    Result ((rowOfCode 29).key i.val) :=
  GraphRoutes.Row29.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row29.row rfl complement h) i

theorem verified30 (i : Fin (rowOfCode 30).graphCount) :
    Result ((rowOfCode 30).key i.val) :=
  GraphRoutes.Row30.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row30.row rfl complement h) i

theorem verified31 (i : Fin (rowOfCode 31).graphCount) :
    Result ((rowOfCode 31).key i.val) :=
  GraphRoutes.Row31.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row31.row rfl complement h) i

theorem verified32 (i : Fin (rowOfCode 32).graphCount) :
    Result ((rowOfCode 32).key i.val) :=
  GraphRoutes.Row32.complete Result cases_resolved
    (fun complement h => of_triangle GraphRoutes.Row32.row rfl complement h) i

theorem small_verified (code : Nat)
    (h : code ∈ ([16,19,23,24,25,26,27,28,29,30,31] : List Nat))
    (i : Fin (rowOfCode code).graphCount) : Result ((rowOfCode code).key i.val) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact verified16 i
  · exact verified19 i
  · exact verified23 i
  · exact verified24 i
  · exact verified25 i
  · exact verified26 i
  · exact verified27 i
  · exact verified28 i
  · exact verified29 i
  · exact verified30 i
  · exact verified31 i

#print axioms cases_resolved
#print axioms verified32
#print axioms small_verified
end Papers.RationalityTen.GraphFiniteDispatch
