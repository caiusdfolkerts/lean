module

public import Papers.GraphicalZonotopes.ThreeTreeGoodEdges

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

theorem weighted_column_eq_sum_pairLinear (G : SimpleGraph V) (s : CompatibleRows G)
    (lam : ↥(tetrahedra G) → ℝ) (E : Finset V) (hE : E.card=2)
    (w : V) (hw : w∉E) (T : Finset V) (hT : T∈triangles G)
    (he : T=insert w E) (hwT : w∈T) :
    (∑ C : AllIncidentClique G ⟨T,hT⟩,
      lam C.1*realBit (faceRow G s ⟨T,hT⟩ C ⟨w,hwT⟩))=
      ∑ C : IncidentPairClique G E,lam C.1*pairLinear G s E hE C w := by
  classical
  subst T
  calc
    _=∑ C : {C : IncidentPairClique G E // w∈C.1.1},
        lam C.1.1*pairLinear G s E hE C.1 w := by
      apply Fintype.sum_equiv (pairTriangleIncidenceEquiv G E w hT)
      intro C
      rw [faceRow_eq_pairLinear G s E hE w hw hT C]
      rfl
    _=∑ C∈(univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1),
        lam C.1*pairLinear G s E hE C w :=
      (sum_subtype ((univ : Finset (IncidentPairClique G E)).filter (fun C => w∈C.1.1))
        (by intro C; simp) (fun C => lam C.1*pairLinear G s E hE C w)).symm
    _=_ := by
      apply sum_subset (filter_subset _ _)
      intro C hC hnot
      rw [pairLinear_eq_zero_of_notMem G s E hE C w
        (fun hwC => hnot (mem_filter.mpr ⟨hC,hwC⟩)),mul_zero]

theorem edgeCoefficients_at_clique (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    (y : SetFunction V) (C : IncidentPairClique G {u,v}) :
    edgeCoefficients y u v ((pairLinkEquiv G huv C).1).toFinset=y C.1.1 := by
  rw [pairLinkEquiv_toFinset,edgeCoefficients,if_pos (by simp)]
  have hu : u∈C.1.1:=C.2 (by simp)
  have hv : v∈C.1.1:=C.2 (by simp)
  have he : insert u (insert v ((C.1.1.erase u).erase v))=C.1.1 := by
    ext w
    by_cases hwu : w=u <;> by_cases hwv : w=v <;> simp [hwu,hwv,hu,hv]
  rw [he]

/-- The forest-kernel linear coefficient is the actual weighted sum of
the incident tetrahedron face bits, with arbitrary real tetrahedron weights. -/
theorem incidentWeight_eq_pairLinear {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {u v : V} (huv : G.Adj u v)
    (hg : GoodPair G {u,v}) (y : SetFunction V) (w : V) :
    ForestZeros.incidentWeight (edgeLink G u v) (linkBit G s huv)
      (fun e => edgeCoefficients y u v e.toFinset) w=
      ∑ C : IncidentPairClique G {u,v},y C.1.1*
        pairLinear G s {u,v} (by simp [huv.ne]) C w := by
  classical
  unfold ForestZeros.incidentWeight
  rw [← sum_coe_sort]
  symm
  apply Fintype.sum_equiv (pairLinkEquiv G huv)
  intro C
  let p:=complementPair G C.1 {u,v} (by simp [huv.ne]) C.2
  have hagree:=goodPair_faces_agree h s {u,v} (by simp [huv.ne]) hg C
  have hbit:=linkBit_at_clique G s huv C
  dsimp only
  rw [edgeCoefficients_at_clique G huv y C,hbit,pairLinkEquiv_eq,Sym2.toFinset_mk_eq]
  change y C.1.1*(if w=p.first.1 then realBit ((s.clique C.1).row p.second p.first)
    else if w=p.second.1 then realBit ((s.clique C.1).row p.first p.second) else 0)=
      if (s.clique C.1).row p.first p.second = true ∧ w ∈ ({p.first.1,p.second.1} : Finset V)
      then y C.1.1 else 0
  change (s.clique C.1).row p.first p.second = (s.clique C.1).row p.second p.first at hagree
  rw [← hagree]
  by_cases hwa : w=p.first.1 <;> by_cases hwb : w=p.second.1 <;>
    cases (s.clique C.1).row p.first p.second <;>
    simp [hwa,hwb,realBit]

theorem good_pair_linear_relation {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (E : Finset V) (hE : E∈edgeFamily G) (hg : GoodPair G E)
    (w : V) (hw : w∉E) :
    mobius f (insert w E)=
      -(∑ C : IncidentPairClique G E,mobius f C.1.1*
        pairLinear G s E ((mem_edgeFamily G E).mp hE).1 C w) := by
  obtain ⟨u,v,huv,rfl⟩:=card_eq_two.mp ((mem_edgeFamily G E).mp hE).1
  have hedge:=(pair_mem_edgeFamily G huv).mp hE
  have hlin:=(good_edge_tight_kernel h s hn hf hedge hg).2 w
  rw [incidentWeight_eq_pairLinear h s hedge hg] at hlin
  have hwu : w≠u:=fun he => hw (by simp [he])
  have hwv : w≠v:=fun he => hw (by simp [he])
  rw [edgeCoefficients,if_pos (by simp [hwu.symm,hwv.symm])] at hlin
  have he : insert u (insert v ({w} : Finset V))=insert w {u,v} := by
    ext a
    simp only [mem_insert,mem_singleton]
    tauto
  simpa only [he] using hlin

theorem goodPair_of_internalTriangle (G : SimpleGraph V) (T : ↥(internalTriangles G))
    (E : Finset V) (hET : E⊆T.1) : GoodPair G E := by
  have hlow:=(mem_internalTriangles.mp T.2).2
  rw [← incidentClique_card G T] at hlow
  apply hlow.trans
  apply Fintype.card_le_of_injective
    (fun C : IncidentClique G T => (⟨C.1,hET.trans C.2⟩ : IncidentPairClique G E))
  intro C D he
  apply Subtype.ext
  simpa only using congrArg (fun x : IncidentPairClique G E => x.1) he

/-- Each internal triangle sees a constant weighted response across all
three of its edge coordinates. The equation is derived from the complete
zero rows of the actual constructed polytope. -/
theorem internal_triangle_relation {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (T : ↥(internalTriangles G)) (j : ↥T.1) :
    (∑ C : IncidentClique G T,mobius f C.1.1*realBit ((s.triangle T).row C j))=
      -mobius f T.1 := by
  classical
  let E:=T.1.erase j.1
  have hEcard : E.card=2 := by
    dsimp only [E]
    rw [card_erase_of_mem j.2,(mem_triangles.mp (mem_internalTriangles.mp T.2).1).1]
  have hE : E∈edgeFamily G:= (mem_edgeFamily G E).mpr ⟨hEcard,
    fun u hu v hv huv => (mem_triangles.mp (mem_internalTriangles.mp T.2).1).2
      (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv⟩
  have hjE : j.1∉E:=notMem_erase _ _
  have hlin:=good_pair_linear_relation h s hn hf E hE
    (goodPair_of_internalTriangle G T E (erase_subset _ _)) j.1 hjE
  have he : T.1=insert j.1 E := (insert_erase j.2).symm
  rw [← he] at hlin
  have hcol:=weighted_column_eq_sum_pairLinear G s (fun C => mobius f C.1)
    E hEcard j.1 hjE T.1 (mem_internalTriangles.mp T.2).1 he j.2
  have hport : ∀ C : IncidentClique G T,
      faceRow G s ⟨T.1,(mem_internalTriangles.mp T.2).1⟩ C j=(s.triangle T).row C j := by
    intro C
    exact congrArg (fun r : ↥T.1 → Bool => r j) (s.port_eq C.1 T C.2)
  simp_rw [hport] at hcol
  rw [← hcol] at hlin
  linarith

theorem incident_clique_scales_equal {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) {f : SetFunction V}
    (hn : TranslationNormalized f) (hf : TightVariation (setFunction h s) f)
    (T : ↥(internalTriangles G)) (C D : IncidentClique G T) :
    mobius f C.1.1=mobius f D.1.1 :=
  (s.triangle T).kernel (fun C => mobius f C.1.1) (-mobius f T.1)
    (internal_triangle_relation h s hn hf T) C D

end ThreeTreeStates
end GraphicalZonotopes
