module

public import Papers.GraphicalZonotopes.Zonotope

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Geometric indecomposability also implies extremality of the correctly
normalized function cone. Both directions of the dictionary are proved. -/
theorem MinkowskiIndecomposable.extremeSupermodular {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hne : z ≠ 0)
    (hi : MinkowskiIndecomposable (basePolytope z)) : ExtremeSupermodular z := by
  refine ⟨hn,hs,hne,?_⟩
  intro f g hfn hgn hfs hgs hfg
  have hsum : basePolytope f + basePolytope g = basePolytope z := by
    rw [← basePolytope_add hfn.1 hgn.1 hfs hgs,hfg]
  obtain ⟨a,t,ha,he⟩ := hi.2 (basePolytope f) (basePolytope g)
    (basePolytope_compact hfn.1 hfs) (basePolytope_compact hgn.1 hgs)
    (basePolytope_convex f) (basePolytope_convex g) hsum
  rw [← basePolytope_smul hn.1 hs ha,← basePolytope_translate] at he
  have hzn : Normalized (a • z+modular t) := by
    change a*z ∅+subsetSum t ∅=0
    rw [hn.1]
    simp [subsetSum]
  have hzs : Supermodular (a • z+modular t) := (hs.smul ha).add (modular_supermodular t)
  have hfun := congrArg lowerSupport he
  rw [lowerSupport_basePolytope hfn.1 hfs,lowerSupport_basePolytope hzn hzs] at hfun
  have ht : t = 0 := by
    funext v
    have h := congrFun hfun {v}
    simpa [hfn.2 v,hn.2 v,modular,subsetSum] using h.symm
  refine ⟨a,ha,?_⟩
  have htmod : modular t = 0 := by
    rw [ht]
    funext S
    simp [modular,subsetSum]
  rw [htmod,add_zero] at hfun
  exact hfun

theorem extremeSupermodular_iff_minkowskiIndecomposable {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hne : z ≠ 0) :
    ExtremeSupermodular z ↔ MinkowskiIndecomposable (basePolytope z) :=
  ⟨ExtremeSupermodular.minkowskiIndecomposable,
    MinkowskiIndecomposable.extremeSupermodular hn hs hne⟩

/-- Restricting the ambient cone to graphical functions introduces no spurious
extreme rays: every supermodular summand inherits the nonedge zero equations. -/
theorem extremeSupermodular_iff_graphical_decompositions {G : SimpleGraph V}
    {z : SetFunction V} (hn : TranslationNormalized z) (hs : Supermodular z)
    (hne : z ≠ 0) (hG : Graphical G z) :
    ExtremeSupermodular z ↔
      ∀ f g : SetFunction V, TranslationNormalized f → TranslationNormalized g →
        Supermodular f → Supermodular g → Graphical G f → Graphical G g →
        f+g=z → ∃ a : ℝ, 0 ≤ a ∧ f=a • z := by
  constructor
  · intro he f g hfn hgn hfs hgs _ _ hfg
    exact he.2.2.2 f g hfn hgn hfs hgs hfg
  · intro he
    refine ⟨hn,hs,hne,?_⟩
    intro f g hfn hgn hfs hgs hfg
    obtain ⟨hfG,hgG⟩ := hG.summands hfs hgs hfg
    exact he f g hfn hgn hfs hgs hfG hgG hfg

theorem basePolytope_is_singleton_iff {z : SetFunction V}
    (hn : TranslationNormalized z) (hs : Supermodular z) :
    (∃ p,basePolytope z={p}) ↔ z=0 := by
  constructor
  · rintro ⟨p,hp⟩
    have hmem : p ∈ basePolytope z := by rw [hp]; simp
    have hz : ∀ S,z S=subsetSum p S := by
      intro S
      obtain ⟨e,j,hj,he⟩ := exists_prefix_enumeration S
      have hg := greedyPoint_mem_basePolytope hn.1 hs e
      have hgp : greedyPoint z e=p := by simpa [hp] using hg
      have h := greedyPoint_prefix z hn.1 e j hj
      simpa [hgp,he] using h.symm
    have hp0 : p=0 := by
      funext v
      have h := hz {v}
      simpa [hn.2 v,subsetSum] using h.symm
    funext S
    simp [hz S,hp0,subsetSum]
  · rintro rfl
    exact ⟨0,basePolytope_zero⟩

end GraphicalZonotopes
