module

public import Papers.GraphicalZonotopes.ThreeTreeFactorization
public import Papers.GraphicalZonotopes.ThreeTreeSharedEdges
public import Papers.GraphicalZonotopes.ForestFactorKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A good edge is one contained in at least two actual tetrahedra. -/
def GoodPair (G : SimpleGraph V) (E : Finset V) : Prop :=
  2≤Fintype.card (IncidentPairClique G E)

theorem goodPair_faces_agree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (E : Finset V) (hE : E.card=2)
    (hg : GoodPair G E) (C : IncidentPairClique G E) :
    let p:=complementPair G C.1 E hE C.2
    (s.clique C.1).row p.first p.second=(s.clique C.1).row p.second p.first := by
  classical
  let p:=complementPair G C.1 E hE C.2
  have hc : 1<(univ : Finset (IncidentPairClique G E)).card := by
    simpa only [card_univ] using (show 1<Fintype.card (IncidentPairClique G E) by
      exact lt_of_lt_of_le (by decide : 1<2) hg)
  obtain ⟨D,hD,hDC⟩:=exists_mem_ne hc C
  have hCD : C.1.1≠D.1.1 := by
    intro he
    exact hDC (Subtype.ext (Subtype.ext he.symm))
  obtain ⟨T,hT,hET,hTC⟩:=h.shared_face_containing C.1.2 D.1.2 hCD C.2 D.2
  have ht3:=(mem_triangles.mp (mem_internalTriangles.mp hT).1).1
  obtain ⟨r,hr⟩:=exists_opposite (mem_filter.mp C.1.2).2.1 ht3 hTC
  have hrT : r.1∉T := by rw [← hr]; exact notMem_erase _ _
  have hrE : r.1∉E:=fun he => hrT (hET he)
  have hi : C.1.1.erase p.first.1∈internalTriangles G ∨
      C.1.1.erase p.second.1∈internalTriangles G := by
    rcases (p.mem_complement_iff r.1).mp ⟨r.2,hrE⟩ with he | he
    · left
      rw [← he,hr]
      exact hT
    · right
      rw [← he,hr]
      exact hT
  exact (s.clique C.1).agree p.first p.second p.ne hi

def linkBit (G : SimpleGraph V) (s : CompatibleRows G) {u v : V}
    (huv : G.Adj u v) (e : Sym2 V) : Bool :=
  if he : e∈(edgeLink G u v).edgeFinset then
    let C:=(pairLinkEquiv G huv).symm ⟨e,he⟩
    let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
    (s.clique C.1).row p.first p.second
  else false

theorem linkBit_at_clique (G : SimpleGraph V) (s : CompatibleRows G) {u v : V}
    (huv : G.Adj u v) (C : IncidentPairClique G {u,v}) :
    linkBit G s huv (pairLinkEquiv G huv C).1=
      let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
      (s.clique C.1).row p.first p.second := by
  simp only [linkBit,dif_pos (pairLinkEquiv G huv C).2]
  let F : IncidentPairClique G {u,v} → Bool := fun D =>
    let p:=complementPair G D.1 {u,v} (by simp [huv.ne]) D.2
    (s.clique D.1).row p.first p.second
  change F ((pairLinkEquiv G huv).symm ((pairLinkEquiv G huv) C)) = F C
  rw [Equiv.symm_apply_apply]

theorem pairFactor_eq_edgeFactor {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (C : IncidentPairClique G {u,v}) (x : V → Bool) :
    pairFactor G s {u,v} (by simp [huv.ne]) C (fun w => realBit (x w))=
      ForestZeros.edgeFactor (linkBit G s huv) x (pairLinkEquiv G huv C).1 := by
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have he:=goodPair_faces_agree h s {u,v} (by simp [huv.ne]) hg C
  have hb:=linkBit_at_clique G s huv C
  rw [pairLinkEquiv_eq] at hb ⊢
  rw [ForestZeros.edgeFactor_pair,hb]
  change ((p.maximum (s.clique C.1).row : ℤ) : ℝ)-
      realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
      realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
      realBit (x p.first.1)*realBit (x p.second.1)=
      if (s.clique C.1).row p.first p.second then
        (1-realBit (x p.first.1))*(1-realBit (x p.second.1))
      else realBit (x p.first.1)*realBit (x p.second.1)
  unfold ComplementPair.maximum
  rw [← he]
  cases (s.clique C.1).row p.first p.second <;>
    cases x p.first.1 <;> cases x p.second.1 <;> norm_num [realBit,RootedResponse.integerBit]

/-- For a good edge the constructed elemental row is exactly the
positive unit-weight forest polynomial. This identifies its entire zero
locus, including every ambient Boolean coordinate. -/
theorem elemental_good_factorization {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (x : V → Bool) :
    delta (setFunction h s) u v
      (((booleanSupport (fun w => realBit (x w))).erase u).erase v)=
      ForestZeros.totalFactor (edgeLink G u v) (linkBit G s huv) x := by
  rw [elemental_factorization h s huv x]
  simp_rw [pairFactor_eq_edgeFactor h s huv hg]
  unfold ForestZeros.totalFactor
  conv_rhs => rw [← sum_coe_sort]
  exact (pairLinkEquiv G huv).sum_comp
    (fun e => ForestZeros.edgeFactor (linkBit G s huv) x e.1)

def TightVariation (z f : SetFunction V) : Prop :=
  ∀ u v,u≠v → ∀ A,u∉A → v∉A → delta z u v A=0 → delta f u v A=0

theorem tightVariation_cliqueSupported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f) :
    CliqueSupported G (mobius f) := by
  apply (mobius_cliqueSupported_iff G f).mpr
  refine ⟨hn,?_⟩
  intro u v huv hnon A hu hv
  exact hf u v huv A hu hv ((setFunction_normalized_graphical h s).2 u v huv hnon A hu hv)

/-- A complete ordinary-coefficient kernel equation for each good edge.
No scalar relation is assumed for the tetrahedral coefficients of the
variation; they remain arbitrary real numbers in the displayed sums. -/
theorem good_edge_tight_kernel {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    {u v : V} (huv : G.Adj u v) (hg : GoodPair G {u,v}) :
    edgeCoefficients (mobius f) u v ∅=
      ForestZeros.constantWeight (edgeLink G u v) (linkBit G s huv)
        (fun e => edgeCoefficients (mobius f) u v e.toFinset) ∧
    ∀ w,edgeCoefficients (mobius f) u v {w}=
      -ForestZeros.incidentWeight (edgeLink G u v) (linkBit G s huv)
        (fun e => edgeCoefficients (mobius f) u v e.toFinset) w := by
  apply (ForestZeros.ordinary_quadratic_tight_kernel (edgeLink G u v)
    (h.edgeLink_acyclic huv) (linkBit G s huv) _ _ _).mp
  intro x hx
  rw [edgeCoefficients_boolean_quadratic (tightVariation_cliqueSupported h s hn hf)
    (fun C hC => h.clique_card_le_four hC) huv.ne _
      (fun w => by cases x w <;> simp [realBit]),zeta_mobius]
  apply hf u v huv.ne _ (by simp) (by simp)
  rw [elemental_good_factorization h s huv hg x]
  exact hx

end ThreeTreeStates
end GraphicalZonotopes
