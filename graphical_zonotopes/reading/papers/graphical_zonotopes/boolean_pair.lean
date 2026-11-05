module

public import Papers.GraphicalZonotopes.GraphDefinitions

public import Papers.GraphicalZonotopes.GraphFunctionRestriction
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.SummandEdges

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Actual normalized integer set functions, with their entire real cone
extremality and with every graph direction occurring in each member. -/
structure BooleanPairData (G : SimpleGraph V) where
  left : SetFunction V
  right : SetFunction V
  left_extreme : ExtremeSupermodular left
  right_extreme : ExtremeSupermodular right
  left_integer : IntegerValued left
  right_integer : IntegerValued right
  pair_sum : left+right=graphFunction G
  left_boolean : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
    delta left u v S=0 ∨ delta left u v S=1
  right_boolean : ∀ u v,u≠v → ∀ S : Finset V,u∉S → v∉S →
    delta right u v S=0 ∨ delta right u v S=1
  left_direction : ∀ u v,G.Adj u v → ∃ S : Finset V,u∉S ∧ v∉S ∧ delta left u v S≠0
  right_direction : ∀ u v,G.Adj u v → ∃ S : Finset V,u∉S ∧ v∉S ∧ delta right u v S≠0

namespace SetFunctionEmbedding

@[simp] theorem restrict_equiv_inverse (e : W ≃ V) (f : SetFunction V) :
    restrict e.symm.toEmbedding (restrict e.toEmbedding f)=f := by
  funext S
  change f ((S.map e.symm.toEmbedding).map e.toEmbedding)=f S
  congr 1
  ext v
  simp

theorem extreme_restrict_equiv (e : W ≃ V) {f : SetFunction V}
    (hf : ExtremeSupermodular f) : ExtremeSupermodular (restrict e.toEmbedding f) := by
  refine ⟨restrict_translationNormalized e.toEmbedding hf.1,
    restrict_supermodular e.toEmbedding hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    have h := congrArg (restrict e.symm.toEmbedding) he
    rw [restrict_equiv_inverse] at h
    exact h.trans (by rfl)
  · intro g h hgn hhn hgs hhs he
    have he' : restrict e.symm.toEmbedding g+restrict e.symm.toEmbedding h=f := by
      rw [← restrict_add,he,restrict_equiv_inverse]
    obtain ⟨a,ha,hag⟩ := hf.2.2.2 (restrict e.symm.toEmbedding g)
      (restrict e.symm.toEmbedding h) (restrict_translationNormalized _ hgn)
      (restrict_translationNormalized _ hhn) (restrict_supermodular _ hgs)
      (restrict_supermodular _ hhs) he'
    refine ⟨a,ha,?_⟩
    have h := congrArg (restrict e.toEmbedding) hag
    rw [restrict_smul] at h
    have hi : restrict e.toEmbedding (restrict e.symm.toEmbedding g)=g := by
      simpa only [Equiv.symm_symm] using restrict_equiv_inverse e.symm g
    exact hi.symm.trans h

end SetFunctionEmbedding

namespace BooleanPairData

/-- Relabelling is an equivalence of the full real set-function cones. -/
def relabel {G : SimpleGraph V} (D : BooleanPairData G) (e : W ≃ V) :
    BooleanPairData (G.comap e) where
  left := SetFunctionEmbedding.restrict e.toEmbedding D.left
  right := SetFunctionEmbedding.restrict e.toEmbedding D.right
  left_extreme := SetFunctionEmbedding.extreme_restrict_equiv e D.left_extreme
  right_extreme := SetFunctionEmbedding.extreme_restrict_equiv e D.right_extreme
  left_integer := SetFunctionEmbedding.integerValued_restrict _ D.left_integer
  right_integer := SetFunctionEmbedding.integerValued_restrict _ D.right_integer
  pair_sum := by
    rw [← SetFunctionEmbedding.restrict_add,D.pair_sum]
    exact SetFunctionEmbedding.graphFunction_restrict e.toEmbedding G
  left_boolean := by
    intro u v huv S hu hv
    rw [SetFunctionEmbedding.delta_restrict]
    exact D.left_boolean _ _ (fun he => huv (e.injective he)) _
      (by simpa using hu) (by simpa using hv)
  right_boolean := by
    intro u v huv S hu hv
    rw [SetFunctionEmbedding.delta_restrict]
    exact D.right_boolean _ _ (fun he => huv (e.injective he)) _
      (by simpa using hu) (by simpa using hv)
  left_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := D.left_direction (e u) (e v) huv
    refine ⟨S.map e.symm.toEmbedding,by simpa using hu,by simpa using hv,?_⟩
    rw [SetFunctionEmbedding.delta_restrict]
    have hS : (S.map e.symm.toEmbedding).map e.toEmbedding=S := by ext x; simp
    rwa [hS]
  right_direction := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := D.right_direction (e u) (e v) huv
    refine ⟨S.map e.symm.toEmbedding,by simpa using hu,by simpa using hv,?_⟩
    rw [SetFunctionEmbedding.delta_restrict]
    have hS : (S.map e.symm.toEmbedding).map e.toEmbedding=S := by ext x; simp
    rwa [hS]

theorem geometric_pair {G : SimpleGraph V} (D : BooleanPairData G) (hG : G.Connected) :
    LatticePolytope (basePolytope D.left) ∧ LatticePolytope (basePolytope D.right) ∧
    MinkowskiIndecomposable (basePolytope D.left) ∧
    MinkowskiIndecomposable (basePolytope D.right) ∧
    FullDimension (basePolytope D.left) ∧ FullDimension (basePolytope D.right) ∧
    basePolytope D.left+basePolytope D.right=graphicalZonotope G ∧
    actualDirectionGraph (basePolytope D.left)=G ∧
    actualDirectionGraph (basePolytope D.right)=G ∧
    BooleanElemental (basePolytope D.left) ∧ BooleanElemental (basePolytope D.right) := by
  have hln := D.left_extreme.1
  have hrn := D.right_extreme.1
  have hls := D.left_extreme.2.1
  have hrs := D.right_extreme.2.1
  have hsum : basePolytope D.left+basePolytope D.right=graphicalZonotope G := by
    rw [← basePolytope_add hln.1 hrn.1 hls hrs,D.pair_sum,baseGraphFunction_eq_graphicalZonotope]
  refine ⟨D.left_integer.basePolytope hln.1 hls,D.right_integer.basePolytope hrn.1 hrs,
    D.left_extreme.minkowskiIndecomposable,D.right_extreme.minkowskiIndecomposable,
    finrank_vectorSpan_eq_of_connected_slacks hln.1 hls hG D.left_direction,
    finrank_vectorSpan_eq_of_connected_slacks hrn.1 hrs hG D.right_direction,hsum,?_,?_,?_,?_⟩
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hln.1 hls G
        (by norm_num : (0 : ℝ)≤1) (basePolytope D.right)
      simpa only [one_smul] using hsum
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := D.left_direction u v huv
      exact exposedSegment_of_positive_delta hln.1 hls (G.ne_of_adj huv) hu hv
        (lt_of_le_of_ne (hls.elemental u v (G.ne_of_adj huv) S hu hv) (Ne.symm hd))
  · ext u v
    constructor
    · apply basePolytope_summand_actualRootEdge hrn.1 hrs G
        (by norm_num : (0 : ℝ)≤1) (basePolytope D.left)
      simpa only [one_smul,add_comm] using hsum
    · intro huv
      obtain ⟨S,hu,hv,hd⟩ := D.right_direction u v huv
      exact exposedSegment_of_positive_delta hrn.1 hrs (G.ne_of_adj huv) hu hv
        (lt_of_le_of_ne (hrs.elemental u v (G.ne_of_adj huv) S hu hv) (Ne.symm hd))
  · intro u v huv S hu hv
    rw [lowerSupport_basePolytope hln.1 hls]
    exact D.left_boolean u v huv S hu hv
  · intro u v huv S hu hv
    rw [lowerSupport_basePolytope hrn.1 hrs]
    exact D.right_boolean u v huv S hu hv

end BooleanPairData
end GraphicalZonotopes
