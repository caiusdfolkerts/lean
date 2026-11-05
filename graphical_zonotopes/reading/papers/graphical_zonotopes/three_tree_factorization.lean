module

public import Papers.GraphicalZonotopes.ThreeTreeEdgeCoordinates
public import Mathlib.Tactic.Ring

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

def edgeFinsetFamilyEquiv (G : SimpleGraph V) : ↥G.edgeFinset ≃ ↥(edgeFamily G) :=
  Equiv.ofBijective (fun e => ⟨e.1.toFinset,by
    rw [edgeFamily_eq_image_edgeFinset]
    exact mem_image.mpr ⟨e.1,e.2,rfl⟩⟩) (by
    constructor
    · intro e f hef
      exact Subtype.ext (sym2_toFinset_injective (congrArg Subtype.val hef))
    · intro E
      have hE:=E.2
      simp only [edgeFamily_eq_image_edgeFinset] at hE
      obtain ⟨e,he,heE⟩:=mem_image.mp hE
      exact ⟨⟨e,he⟩,Subtype.ext heE⟩)

def incidentPairContainingEquiv (G : SimpleGraph V) (u v : V) :
    IncidentPairClique G {u,v} ≃ ↥(tetrahedraContaining G u v) where
  toFun C:=⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2 (by simp),C.2 (by simp)⟩⟩
  invFun C:=⟨⟨C.1,(mem_filter.mp C.2).1⟩,by
    simpa only [insert_subset_iff,singleton_subset_iff] using (mem_filter.mp C.2).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

/-- The summation over actual incident tetrahedra is exactly the summation
over actual edges of the common-neighbor graph. -/
def pairLinkEquiv (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    IncidentPairClique G {u,v} ≃ ↥(edgeLink G u v).edgeFinset :=
  ((incidentPairContainingEquiv G u v).trans (tetrahedronLinkEquiv G huv)).trans
    (edgeFinsetFamilyEquiv (edgeLink G u v)).symm

theorem pairLinkEquiv_toFinset (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (C : IncidentPairClique G {u,v}) :
    ((pairLinkEquiv G huv C).1).toFinset=(C.1.1.erase u).erase v := by
  exact congrArg Subtype.val
    ((edgeFinsetFamilyEquiv (edgeLink G u v)).apply_symm_apply
      ((tetrahedronLinkEquiv G huv) ((incidentPairContainingEquiv G u v) C)))

theorem pairLinkEquiv_eq (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (C : IncidentPairClique G {u,v}) :
    (pairLinkEquiv G huv C).1=
      let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
      s(p.first.1,p.second.1) := by
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  apply sym2_toFinset_injective
  rw [pairLinkEquiv_toFinset,Sym2.toFinset_mk_eq,p.pair_eq_complement]
  ext w
  simp only [mem_erase,mem_sdiff,mem_insert,mem_singleton,not_or]
  tauto

theorem edgeCoefficients_constant {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v) :
    edgeCoefficients (coefficients h s) u v ∅=
      ∑ C : IncidentPairClique G {u,v},
        ((complementPair G C.1 {u,v} (by simp [huv.ne]) C.2).maximum
          (s.clique C.1).row : ℝ) := by
  rw [edgeCoefficients,if_pos (by simp)]
  simp only [insert_empty_eq]
  rw [coefficients_pair h s ((pair_mem_edgeFamily G huv.ne).mpr huv)]
  simp only [pairWeight,Int.cast_sum]

theorem edgeCoefficients_linear {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (w : V) :
    edgeCoefficients (coefficients h s) u v {w}=
      -(∑ C : IncidentPairClique G {u,v},
        pairLinear G s {u,v} (by simp [huv.ne]) C w) := by
  classical
  by_cases hw : w∈({u,v} : Finset V)
  · have hs : ∑ C : IncidentPairClique G {u,v},
        pairLinear G s {u,v} (by simp [huv.ne]) C w=0 := by
      exact sum_eq_zero (fun C _ => pairLinear_eq_zero_of_mem G s _ _ C w hw)
    rw [hs,neg_zero]
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl <;> simp [edgeCoefficients]
  · have hwu : w≠u := fun he => hw (by simp [he])
    have hwv : w≠v := fun he => hw (by simp [he])
    rw [edgeCoefficients,if_pos (by simp [hwu.symm,hwv.symm])]
    have he : insert u (insert v ({w} : Finset V))=insert w {u,v} := by
      ext a
      simp only [mem_insert,mem_singleton]
      tauto
    rw [he]
    exact coefficients_insert_pair h s _ (by simp [huv.ne]) w hw

theorem edgeCoefficients_quadratic {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (e : ↥(edgeLink G u v).edgeFinset) :
    edgeCoefficients (coefficients h s) u v e.1.toFinset=1 := by
  have hE : e.1.toFinset∈edgeFamily (edgeLink G u v):=
    ((edgeFinsetFamilyEquiv (edgeLink G u v)) e).2
  obtain ⟨hu,hv⟩:=linkPair_excludes_endpoints hE
  rw [edgeCoefficients,if_pos ⟨hu,hv⟩]
  exact coefficients_tetrahedron h s (tetrahedron_of_linkPair huv hE)

def pairFactor (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → ℝ) : ℝ :=
  let p:=complementPair G C.1 E hE C.2
  (p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*x p.second.1-
    realBit ((s.clique C.1).row p.second p.first)*x p.first.1+
    x p.first.1*x p.second.1

/-- The exact polynomial identity, before restricting coordinates to the
Boolean cube. Its constant, every ambient linear coefficient, and every
quadratic interaction are proved from the actual Möbius vector. -/
theorem quadratic_eq_sum_pairFactor {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (x : V → ℝ) :
    ForestSigns.quadratic (edgeLink G u v)
      (edgeCoefficients (coefficients h s) u v ∅)
      (fun w => edgeCoefficients (coefficients h s) u v {w})
      (fun e => edgeCoefficients (coefficients h s) u v e.toFinset) x=
      ∑ C : IncidentPairClique G {u,v},pairFactor G s {u,v} (by simp [huv.ne]) C x := by
  classical
  let pc : (C : IncidentPairClique G {u,v}) → ComplementPair C.1.1 {u,v}:=
    fun C => complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have hlin : (∑ w,edgeCoefficients (coefficients h s) u v {w}*x w)=
      -(∑ C : IncidentPairClique G {u,v},
        (realBit ((s.clique C.1).row (pc C).second (pc C).first)*x (pc C).first.1+
        realBit ((s.clique C.1).row (pc C).first (pc C).second)*x (pc C).second.1)) := by
    simp_rw [edgeCoefficients_linear h s huv,neg_mul,sum_mul]
    rw [sum_neg_distrib,sum_comm]
    simp_rw [pairLinear_sum]
    rfl
  have hquad :
      (∑ e∈(edgeLink G u v).edgeFinset,
        edgeCoefficients (coefficients h s) u v e.toFinset*ForestSigns.edgeProduct x e)=
      ∑ C : IncidentPairClique G {u,v},x (pc C).first.1*x (pc C).second.1 := by
    rw [← sum_coe_sort]
    have hw : ∀ e : ↥(edgeLink G u v).edgeFinset,
        edgeCoefficients (coefficients h s) u v e.1.toFinset=1:=
      edgeCoefficients_quadratic h s huv
    simp_rw [hw,one_mul]
    symm
    apply Fintype.sum_equiv (pairLinkEquiv G huv)
    intro C
    rw [pairLinkEquiv_eq,ForestSigns.edgeProduct_pair]
  unfold ForestSigns.quadratic
  rw [edgeCoefficients_constant h s huv,hlin,hquad]
  simp only [pairFactor]
  rw [← sub_eq_add_neg,← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro C hC
  dsimp only [pc]
  ring

theorem pairFactor_zero_or_one (G : SimpleGraph V) (s : CompatibleRows G)
    (E : Finset V) (hE : E.card=2) (C : IncidentPairClique G E) (x : V → Bool) :
    pairFactor G s E hE C (fun w => realBit (x w))=0 ∨
      pairFactor G s E hE C (fun w => realBit (x w))=1 := by
  let p:=complementPair G C.1 E hE C.2
  change ((p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
    realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=0) ∨
    ((p.maximum (s.clique C.1).row : ℝ)-
    realBit ((s.clique C.1).row p.first p.second)*realBit (x p.second.1)-
    realBit ((s.clique C.1).row p.second p.first)*realBit (x p.first.1)+
    realBit (x p.first.1)*realBit (x p.second.1)=1)
  unfold ComplementPair.maximum
  cases (s.clique C.1).row p.first p.second <;>
    cases (s.clique C.1).row p.second p.first <;>
    cases x p.first.1 <;> cases x p.second.1 <;>
    norm_num [realBit,RootedResponse.integerBit]

/-- Every elemental slack is the literal sum of the Boolean local factors.
Endpoint erasure only expresses that a conditioning set omits those endpoints. -/
theorem elemental_factorization {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (x : V → Bool) :
    delta (setFunction h s) u v
      (((booleanSupport (fun w => realBit (x w))).erase u).erase v)=
      ∑ C : IncidentPairClique G {u,v},
        pairFactor G s {u,v} (by simp [huv.ne]) C (fun w => realBit (x w)) := by
  unfold setFunction
  rw [← edgeCoefficients_boolean_quadratic (coefficients_cliqueSupported h s)
    (fun C hC => h.clique_card_le_four hC) huv.ne _
      (fun w => by cases x w <;> simp [realBit])]
  exact quadratic_eq_sum_pairFactor h s huv _

end ThreeTreeStates
end GraphicalZonotopes
