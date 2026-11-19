module
public import applications_verification

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace FourPapers.Symmetric.Schur
open TauCeti Inflation

/-- The actual finite-alphabet tableau, written with natural-number labels. -/
def pairedTableauNat {n : ℕ} (m : Entry n →₀ ℕ) : List (List ℕ) :=
  (pairedTableau m).map (List.map Fin.val)

/-- Ordinary semistandard tableaux on the alphabet `0,...,n-1` with even rows. -/
def EvenSemistandardTableaux (n : ℕ) :=
  {rows : List (List ℕ) // rows.IsTableauRows ∧ EvenRows rows ∧
    ∀ x ∈ rows.flatten, x < n}

def pairedTableauMap {n : ℕ} (m : Entry n →₀ ℕ) : EvenSemistandardTableaux n := by
  refine ⟨pairedTableauNat m, ?_, ?_, ?_⟩
  · exact (isTableauRows_map_iff_strictMono (fun x : Fin n => x.val)
      (fun _ _ h => h) _).mpr (pairedTableau_isTableauRows m)
  · exact (evenRows_iff_map _ _).mpr (pairedTableau_evenRows m)
  · intro x hx
    change x ∈ ((pairedTableau m).map (List.map Fin.val)).flatten at hx
    rw [←List.map_flatten] at hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact y.isLt

theorem pairedTableauMap_bijective {n : ℕ} : Function.Bijective (@pairedTableauMap n) := by
  constructor
  · intro m m' h
    apply pairedTableau_injective
    apply Fin.val_injective.list_map.list_map
    exact congrArg Subtype.val h
  · intro T
    obtain ⟨w,hw,hout⟩ := exists_orderedPairs_of_evenTableau T.property.1 T.property.2.1
    have hb : ∀ p ∈ w, p.2 < n := by
      intro p hp
      apply T.property.2.2
      rw [←hout]
      apply (flatten_pairInsertList_perm w []).mem_iff.mpr
      simpa only [List.flatten_nil,List.append_nil] using
        (mem_endpointWord.mpr ⟨p,hp,Or.inr rfl⟩)
    let m := monomialOfOrderedPairs w hw hb
    refine ⟨m,Subtype.ext ?_⟩
    change pairedTableauNat m = T.val
    rw [pairedTableauNat,←pairInsertList_natMonomialPairs,
      natMonomialPairs_monomialOfOrderedPairs]
    exact hout

theorem rowsCellEntry_mem {μ : YoungDiagram} {rows : List (List ℕ)}
    (hshape : rows.map List.length = μ.rowLens) (c : ↥μ.cells) :
    rowsCellEntry hshape c ∈ rows.flatten :=
  List.mem_flatten.mpr ⟨_,List.getElem_mem (rows_cell_row_bound hshape c.property),
    List.getElem_mem (rows_cell_col_bound hshape c.property)⟩

theorem weakFillingOfRows_bound {μ : YoungDiagram} {rows : List (List ℕ)}
    (hrows : rows.IsTableauRows) (hshape : rows.map List.length = μ.rowLens)
    {n : ℕ} (hb : ∀ x ∈ rows.flatten, x < n) :
    ∀ c : ↥μ.cells, weakFillingOfRows hrows hshape c < n :=
  fun c => hb _ (rowsCellEntry_mem hshape c)

end FourPapers.Symmetric.Schur
