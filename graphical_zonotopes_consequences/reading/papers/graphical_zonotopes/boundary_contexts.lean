module

public import Papers.GraphicalZonotopes.CliqueCoordinates
public import Papers.GraphicalZonotopes.PolyhedralCone

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
section Unordered
variable {V : Type*} [Fintype V] [DecidableEq V]

def commonNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact univ.filter (fun w => G.Adj u w ∧ G.Adj v w)

@[simp] theorem mem_commonNeighbors (G : SimpleGraph V) (u v w : V) :
    w ∈ commonNeighbors G u v ↔ G.Adj u w ∧ G.Adj v w := by
  classical
  simp [commonNeighbors]

@[simp] theorem not_mem_commonNeighbors_left (G : SimpleGraph V) (u v : V) :
    u ∉ commonNeighbors G u v := by simp

@[simp] theorem not_mem_commonNeighbors_right (G : SimpleGraph V) (u v : V) :
    v ∉ commonNeighbors G u v := by simp

theorem commonNeighbors_comm (G : SimpleGraph V) (u v : V) :
    commonNeighbors G u v=commonNeighbors G v u := by
  ext w
  simp [and_comm]

theorem clique_pair_subset_iff {G : SimpleGraph V} {C S : Finset V}
    (hcl : G.IsClique C) {u v : V} (huC : u ∈ C) (hvC : v ∈ C) :
    C ⊆ insert u (insert v S) ↔ C ⊆ insert u (insert v (S ∩ commonNeighbors G u v)) := by
  constructor
  · intro h w hw
    have hm := h hw
    simp only [mem_insert] at hm ⊢
    rcases hm with hwu | hwv | hwS
    · exact Or.inl hwu
    · exact Or.inr (Or.inl hwv)
    · by_cases hwu : w=u
      · exact Or.inl hwu
      · by_cases hwv : w=v
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,(mem_commonNeighbors G u v w).mpr
            ⟨hcl huC hw (Ne.symm hwu),hcl hvC hw (Ne.symm hwv)⟩⟩))
  · intro h
    exact h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))

/-- Elemental differences of a graphical function depend only on the
conditioning bits of common neighbors. This is proved from all Möbius slots. -/
theorem delta_zeta_commonNeighbors {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) {u v : V} (huv : u ≠ v) {S : Finset V}
    (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S=delta (zeta y) u v (S ∩ commonNeighbors G u v) := by
  classical
  have hu' : u ∉ S ∩ commonNeighbors G u v := by simp
  have hv' : v ∉ S ∩ commonNeighbors G u v := by simp
  rw [zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,
    delta_setMonomial huv hu' hv']
  by_cases hyC : y C=0
  · simp [hyC]
  · have hcl : G.IsClique C := by
      by_contra hn
      exact hyC (coefficient_zero_of_not_clique hy C (by rintro ⟨_,h⟩; exact hn h))
    by_cases huC : u ∈ C
    · by_cases hvC : v ∈ C
      · have he := clique_pair_subset_iff (S := S) hcl huC hvC
        simp only [he]
      · simp [hvC]
    · simp [huC]

theorem delta_commonNeighbors {G : SimpleGraph V} {z : SetFunction V}
    (hn : TranslationNormalized z) (hG : Graphical G z)
    {u v : V} (huv : u ≠ v) {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta z u v S=delta z u v (S ∩ commonNeighbors G u v) := by
  have h := delta_zeta_commonNeighbors ((mobius_cliqueSupported_iff G z).mpr ⟨hn,hG⟩) huv hu hv
  simpa using h

theorem delta_comm {z : SetFunction V} (u v : V) (S : Finset V) :
    delta z u v S=delta z v u S := by
  unfold delta
  rw [insert_comm]
  ring

end Unordered

section Ordered
variable {V : Type*} [Fintype V] [LinearOrder V]

abbrev OrientedEdge (G : SimpleGraph V) := {e : V × V // e.1<e.2 ∧ G.Adj e.1 e.2}

noncomputable instance orientedEdgeFintype (G : SimpleGraph V) : Fintype (OrientedEdge G) := by
  classical
  infer_instance

abbrev BoundaryContext (G : SimpleGraph V) :=
  Σ e : OrientedEdge G, ↥(commonNeighbors G e.1.1 e.1.2).powerset

noncomputable instance boundaryContextFintype (G : SimpleGraph V) : Fintype (BoundaryContext G) := by
  classical
  infer_instance

/-- The exact boundary slack map, using each unordered graph edge once and all
common-neighbor contexts once. -/
def boundarySlackMap (G : SimpleGraph V) :
    graphicalFunctionSpace G →ₗ[ℝ] (BoundaryContext G → ℝ) where
  toFun z r := delta z.1 r.1.1.1 r.1.1.2 r.2.1
  map_add' z w := by ext r; exact delta_add z.1 w.1 _ _ _
  map_smul' a z := by ext r; exact delta_smul a z.1 _ _ _

theorem boundarySlackMap_eq_zero (G : SimpleGraph V) (z : graphicalFunctionSpace G)
    (hz : boundarySlackMap G z=0) : z=0 := by
  apply graphical_function_eq_zero_of_elemental_zero G z
  intro u v huv S hu hv
  by_cases hedge : G.Adj u v
  · rcases lt_or_gt_of_ne huv with hlt | hgt
    · let e : OrientedEdge G := ⟨(u,v),hlt,hedge⟩
      let T := S ∩ commonNeighbors G u v
      let r : BoundaryContext G := ⟨e,⟨T,mem_powerset.mpr inter_subset_right⟩⟩
      have h := congrFun hz r
      rw [delta_commonNeighbors z.2.1 z.2.2 huv hu hv]
      exact h
    · let e : OrientedEdge G := ⟨(v,u),hgt,G.adj_symm hedge⟩
      let T := S ∩ commonNeighbors G v u
      let r : BoundaryContext G := ⟨e,⟨T,mem_powerset.mpr inter_subset_right⟩⟩
      have h := congrFun hz r
      rw [delta_comm u v,delta_commonNeighbors z.2.1 z.2.2 (Ne.symm huv) hv hu]
      exact h
  · exact z.2.2 u v huv hedge S hu hv

theorem boundarySlackMap_injective (G : SimpleGraph V) :
    Function.Injective (boundarySlackMap G) := by
  intro z w he
  have hz : boundarySlackMap G (z-w)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp (boundarySlackMap_eq_zero G (z-w) hz)

theorem supermodular_iff_boundarySlacks_nonnegative (G : SimpleGraph V)
    (z : graphicalFunctionSpace G) :
    Supermodular z.1 ↔ ∀ r,0 ≤ boundarySlackMap G z r := by
  constructor
  · intro hs r
    have hu : r.1.1.1 ∉ r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_left G _ _ ((mem_powerset.mp r.2.2) hm)
    have hv : r.1.1.2 ∉ r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_right G _ _ ((mem_powerset.mp r.2.2) hm)
    exact hs.elemental _ _ (ne_of_lt r.1.2.1) _ hu hv
  · intro hrows
    apply ElementallyNonnegative.supermodular
    intro u v huv S hu hv
    by_cases hedge : G.Adj u v
    · rcases lt_or_gt_of_ne huv with hlt | hgt
      · let e : OrientedEdge G := ⟨(u,v),hlt,hedge⟩
        let r : BoundaryContext G := ⟨e,⟨S ∩ commonNeighbors G u v,mem_powerset.mpr inter_subset_right⟩⟩
        rw [delta_commonNeighbors z.2.1 z.2.2 huv hu hv]
        exact hrows r
      · let e : OrientedEdge G := ⟨(v,u),hgt,G.adj_symm hedge⟩
        let r : BoundaryContext G := ⟨e,⟨S ∩ commonNeighbors G v u,mem_powerset.mpr inter_subset_right⟩⟩
        rw [delta_comm u v,delta_commonNeighbors z.2.1 z.2.2 (Ne.symm huv) hv hu]
        exact hrows r
    · rw [z.2.2 u v huv hedge S hu hv]

theorem boundaryContext_card (G : SimpleGraph V) :
    Fintype.card (BoundaryContext G)=
      ∑ e : OrientedEdge G,2 ^ (commonNeighbors G e.1.1 e.1.2).card := by
  simp only [BoundaryContext,Fintype.card_sigma,Fintype.card_coe,card_powerset]

theorem clique_count_le_boundary_context_count (G : SimpleGraph V) :
    Fintype.card (CliqueIndex G) ≤ Fintype.card (BoundaryContext G) := by
  have h := LinearMap.finrank_le_finrank_of_injective (boundarySlackMap_injective G)
  simpa [graphicalFunctionSpace_finrank,Module.finrank_fintype_fun_eq_card] using h

/-- The row family used by the finite homogeneous inequality cone. -/
def contextRow (G : SimpleGraph V) (r : BoundaryContext G) :
    graphicalFunctionSpace G →ₗ[ℝ] ℝ where
  toFun z := boundarySlackMap G z r
  map_add' z w := congrFun ((boundarySlackMap G).map_add z w) r
  map_smul' a z := congrFun ((boundarySlackMap G).map_smul a z) r

theorem contextRows_pointed (G : SimpleGraph V) : Polyhedral.Pointed (contextRow G) := by
  intro z hz
  apply boundarySlackMap_eq_zero G z
  funext r
  exact hz r

/-- The normalized graphical finite-inequality model and the genuine
supermodular-function cone have exactly the same extreme rays. -/
theorem extremeSupermodular_iff_contextRows (G : SimpleGraph V)
    (z : graphicalFunctionSpace G) :
    ExtremeSupermodular z.1 ↔ Polyhedral.ExtremeRay (contextRow G) z := by
  constructor
  · intro hz
    refine ⟨(supermodular_iff_boundarySlacks_nonnegative G z).mp hz.2.1,?_,?_⟩
    · intro he
      exact hz.2.2.1 (congrArg Subtype.val he)
    · intro f g hf hg he
      have hfs := (supermodular_iff_boundarySlacks_nonnegative G f).mpr hf
      have hgs := (supermodular_iff_boundarySlacks_nonnegative G g).mpr hg
      have hsum : f.1+g.1=z.1 := congrArg Subtype.val he
      obtain ⟨a,ha,hscale⟩ := hz.2.2.2 f.1 g.1 f.2.1 g.2.1 hfs hgs hsum
      exact ⟨a,ha,Subtype.ext hscale⟩
  · intro hz
    have hzs := (supermodular_iff_boundarySlacks_nonnegative G z).mpr hz.1
    refine ⟨z.2.1,hzs,?_,?_⟩
    · intro he
      exact hz.2.1 (Subtype.ext he)
    · intro f g hfn hgn hfs hgs he
      obtain ⟨hfG,hgG⟩ := z.2.2.summands hfs hgs he
      let f' : graphicalFunctionSpace G := ⟨f,hfn,hfG⟩
      let g' : graphicalFunctionSpace G := ⟨g,hgn,hgG⟩
      have hf' : Polyhedral.Nonnegative (contextRow G) f' :=
        (supermodular_iff_boundarySlacks_nonnegative G f').mp hfs
      have hg' : Polyhedral.Nonnegative (contextRow G) g' :=
        (supermodular_iff_boundarySlacks_nonnegative G g').mp hgs
      have he' : f'+g'=z := Subtype.ext he
      obtain ⟨a,ha,hscale⟩ := hz.2.2 f' g' hf' hg' he'
      exact ⟨a,ha,congrArg Subtype.val hscale⟩


end Ordered
end GraphicalZonotopes
