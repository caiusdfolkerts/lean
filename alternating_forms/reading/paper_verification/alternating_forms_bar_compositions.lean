module

public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.List.Chain
public import Lean.Elab.Tactic.Omega

/-!
# Actual bar factorizations and their full boundary sets

A factorization is a list of nonempty lists whose literal concatenation is
the original word. The equivalence with compositions records the actual
block lengths and is inverse to splitting the original word. Endpoints
are retained as mandatory boundaries: r bar factors give r+1 boundaries.
This convention makes the exterior contraction sign agree with the
negative normalized bar differential after tensoring the free resolution.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BarCompositions

variable {α : Type*}

def Factorization (W : List α) :=
  {L : List (List α) // L.flatten=W ∧ ∀ T∈L,0<T.length}

def factorizationComposition (W : List α) (L : Factorization W) :
    Composition W.length where
  blocks := L.val.map List.length
  blocks_pos := by
    intro n hn
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hn
    exact L.property.2 T hT
  blocks_sum := by
    rw [←List.length_flatten,L.property.1]

def splitFactorization (W : List α) (c : Composition W.length) : Factorization W :=
  ⟨W.splitWrtComposition c,List.flatten_splitWrtComposition W c,
    fun T hT ↦ List.length_pos_of_mem_splitWrtComposition hT⟩

@[simp] theorem composition_splitFactorization (W : List α) (c : Composition W.length) :
    factorizationComposition W (splitFactorization W c)=c := by
  apply Composition.ext
  exact List.map_length_splitWrtComposition W c

@[simp] theorem split_compositionFactorization (W : List α) (L : Factorization W) :
    splitFactorization W (factorizationComposition W L)=L := by
  rcases L with ⟨L,hL,hpos⟩
  subst W
  apply Subtype.ext
  exact List.splitWrtComposition_flatten L
    (factorizationComposition L.flatten ⟨L,rfl,hpos⟩) rfl

def factorizationCompositionEquiv (W : List α) :
    Factorization W ≃ Composition W.length where
  toFun := factorizationComposition W
  invFun := splitFactorization W
  left_inv := split_compositionFactorization W
  right_inv := composition_splitFactorization W

def factorizationBoundaryEquiv (W : List α) :
    Factorization W ≃ CompositionAsSet W.length :=
  (factorizationCompositionEquiv W).trans (compositionEquiv W.length)

def boundaries (W : List α) (L : Factorization W) : Finset (Fin (W.length+1)) :=
  (factorizationComposition W L).boundaries

@[simp] theorem boundaries_card (W : List α) (L : Factorization W) :
    (boundaries W L).card=L.val.length+1 := by
  simpa only [boundaries,Composition.length,factorizationComposition,List.length_map] using
    (factorizationComposition W L).card_boundaries_eq_succ_length

theorem zero_mem_boundaries (W : List α) (L : Factorization W) :
    (0 : Fin (W.length+1))∈boundaries W L :=
  (factorizationComposition W L).toCompositionAsSet.zero_mem

theorem last_mem_boundaries (W : List α) (L : Factorization W) :
    Fin.last W.length∈boundaries W L :=
  (factorizationComposition W L).toCompositionAsSet.getLast_mem

theorem boundaries_injective (W : List α) :
    Function.Injective (boundaries W) := by
  intro L M h
  apply (factorizationBoundaryEquiv W).injective
  apply CompositionAsSet.ext
  exact h

/-- Every cut set with both endpoints is realized by a unique actual
factorization of the original word. -/
theorem exists_unique_factorization (W : List α) (S : Finset (Fin (W.length+1)))
    (h0 : (0 : Fin (W.length+1))∈S) (hN : Fin.last W.length∈S) :
    ∃! L : Factorization W,boundaries W L=S := by
  let c : CompositionAsSet W.length := ⟨S,h0,hN⟩
  refine ⟨(factorizationBoundaryEquiv W).symm c,?_,?_⟩
  · have h := (factorizationBoundaryEquiv W).apply_symm_apply c
    exact congrArg CompositionAsSet.boundaries h
  · intro L hL
    apply boundaries_injective W
    rw [hL]
    exact (congrArg CompositionAsSet.boundaries
      ((factorizationBoundaryEquiv W).apply_symm_apply c)).symm

/-- An interior position fails to be a boundary precisely when it lies
strictly inside one of the actual blocks. -/
theorem not_mem_boundaries_iff {n : ℕ} (c : Composition n) (j : Fin (n+1))
    (hj0 : 0<j.val) (hjn : j.val<n) :
    j∉c.boundaries ↔ ∃ i : Fin c.length,
      c.sizeUpTo i.val<j.val ∧ j.val<c.sizeUpTo (i.val+1) := by
  constructor
  · intro hj
    let k : Fin n := ⟨j.val,hjn⟩
    refine ⟨c.index k,?_,c.lt_sizeUpTo_index_succ k⟩
    have hle := c.sizeUpTo_index_le k
    apply lt_of_le_of_ne hle
    intro he
    apply hj
    apply Finset.mem_map.mpr
    refine ⟨(c.index k).castSucc,Finset.mem_univ _,?_⟩
    apply Fin.ext
    exact he
  · rintro ⟨i,hi₀,hi₁⟩ hj
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hj
    have hea : c.sizeUpTo a.val=j.val := congrArg Fin.val he
    by_cases hai : a.val ≤ i.val
    · have hm := c.monotone_sizeUpTo hai
      omega
    · have hai' : i.val+1≤a.val := by omega
      have hm := c.monotone_sizeUpTo hai'
      omega

/-- The internal degree is the actual sum of lengths of the tensor factors. -/
theorem total_length (W : List α) (L : Factorization W) :
    (L.val.map List.length).sum=W.length :=
  (factorizationComposition W L).blocks_sum

theorem number_of_blocks_le (W : List α) (L : Factorization W) :
    L.val.length≤W.length := by
  simpa only [Composition.length,factorizationComposition,List.length_map] using
    (factorizationComposition W L).length_le

/-- The diagonal bar degree consists exactly of the factorization into
single generators. -/
theorem diagonal_iff_singletons (W : List α) (L : Factorization W) :
    L.val.length=W.length ↔ ∀ T∈L.val,T.length=1 := by
  constructor
  · intro h T hT
    have hc : factorizationComposition W L=Composition.ones W.length :=
      Composition.eq_ones_iff_length.mpr (by
        simpa only [Composition.length,factorizationComposition,List.length_map] using h)
    exact (Composition.eq_ones_iff.mp hc) T.length (List.mem_map.mpr ⟨T,hT,rfl⟩)
  · intro h
    have hc : factorizationComposition W L=Composition.ones W.length :=
      Composition.eq_ones_iff.mpr (by
        intro n hn
        obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hn
        exact h T hT)
    simpa only [Composition.length,factorizationComposition,List.length_map] using
      Composition.eq_ones_iff_length.mp hc

end PaperVerification.AlternatingForms.BarCompositions

