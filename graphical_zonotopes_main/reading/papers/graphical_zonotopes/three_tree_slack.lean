module

public import Papers.GraphicalZonotopes.ConditionalQuadratic
public import Papers.GraphicalZonotopes.IntegralForestOscillation
public import Papers.GraphicalZonotopes.LatticeCoefficients

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeLink_pair_vertices {G : SimpleGraph V} {u v : V} {C : Finset V}
    (hC : C∈edgeFamily (edgeLink G u v)) :
    u∉C ∧ v∉C ∧ ∀ a∈C,G.Adj u a ∧ G.Adj v a := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  have h := (pair_mem_edgeFamily (edgeLink G u v) hab).mp hC
  have hall : ∀ w∈({a,b} : Finset V),G.Adj u w ∧ G.Adj v w := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact ⟨h.2.1,h.2.2.1⟩
    · have hw' := mem_singleton.mp hw
      subst w
      exact ⟨h.2.2.2.1,h.2.2.2.2⟩
  exact ⟨fun hu => G.irrefl (hall u hu).1,
    fun hv => G.irrefl (hall v hv).2,hall⟩

/-- Link edges and tetrahedra containing the original edge are in exact
bijection. The equality applies to arbitrary real weights. -/
theorem sum_edgeLink_tetrahedra {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (f : Finset V → ℝ) :
    (∑ e∈(edgeLink G u v).edgeFinset,f (insert u (insert v e.toFinset)))=
      ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset V)⊆C),f C := by
  classical
  rw [← sum_edgeFamily_eq (edgeLink G u v) (fun e => f (insert u (insert v e)))]
  apply sum_bij (fun C _ => insert u (insert v C))
  · intro C hC
    obtain ⟨huC,hvC,hverts⟩ := edgeLink_pair_vertices hC
    obtain ⟨hcard,hcl⟩ := (mem_edgeFamily _ C).mp hC
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_,?_⟩,by simp⟩
    · rw [card_insert_of_notMem (by simp [G.ne_of_adj huv,huC]),
        card_insert_of_notMem hvC,hcard]
    · have hc : G.IsClique C := fun a ha b hb hab => (hcl a ha b hb hab).1
      have hvcl : G.IsClique (insert v C : Finset V) := by
        simpa only [Finset.coe_insert] using hc.insert (fun a ha _ => (hverts a ha).2)
      simpa only [Finset.coe_insert] using hvcl.insert (by
        intro a ha hna
        rcases mem_insert.mp ha with rfl | ha
        · exact huv
        · exact (hverts a ha).1)
  · intro C hC D hD he
    obtain ⟨huC,hvC,_⟩ := edgeLink_pair_vertices hC
    obtain ⟨huD,hvD,_⟩ := edgeLink_pair_vertices hD
    have hh:=congrArg (fun E : Finset V => (E.erase u).erase v) he
    simpa [G.ne_of_adj huv,huC,hvC,huD,hvD] using hh
  · intro C hC
    obtain ⟨hC,hpair⟩ := mem_filter.mp hC
    obtain ⟨hcard,hcl⟩ := (mem_filter.mp hC).2
    have huC : u∈C := hpair (by simp)
    have hvC : v∈C := hpair (by simp)
    let D:=(C.erase u).erase v
    have hDcard : D.card=2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm (G.ne_of_adj huv),hvC⟩),
        card_erase_of_mem huC,hcard]
    have hDcl : (edgeLink G u v).IsClique D := by
      intro a ha b hb hab
      have haC := mem_of_mem_erase (mem_of_mem_erase ha)
      have hbC := mem_of_mem_erase (mem_of_mem_erase hb)
      have hau := ne_of_mem_erase (mem_of_mem_erase ha)
      have hav := ne_of_mem_erase ha
      have hbu := ne_of_mem_erase (mem_of_mem_erase hb)
      have hbv := ne_of_mem_erase hb
      exact ⟨hcl haC hbC hab,hcl huC haC (Ne.symm hau),hcl hvC haC (Ne.symm hav),
        hcl huC hbC (Ne.symm hbu),hcl hvC hbC (Ne.symm hbv)⟩
    refine ⟨D,(mem_edgeFamily _ D).mpr ⟨hDcard,hDcl⟩,?_⟩
    ext a
    by_cases hau : a=u <;> by_cases hav : a=v <;> simp [D,hau,hav,huC,hvC]
  · intro C hC
    rfl

theorem sum_edgeCoefficients_abs {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (y : SetFunction V) :
    (∑ e∈(edgeLink G u v).edgeFinset,|edgeCoefficients y u v e.toFinset|)=
      ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset V)⊆C),|y C| := by
  classical
  rw [← sum_edgeLink_tetrahedra huv (fun C => |y C|)]
  apply sum_congr rfl
  intro e he
  have hmem : e.toFinset∈edgeFamily (edgeLink G u v) := by
    rw [edgeFamily_eq_image_edgeFinset]
    exact mem_image.mpr ⟨e,he,rfl⟩
  obtain ⟨hu,hv,_⟩ := edgeLink_pair_vertices hmem
  simp [edgeCoefficients,hu,hv]

/-- The exact integer-ceiling edge bound in Theorem9.1, with arbitrary
constant and triangle coefficients retained in the actual elemental row. -/
theorem threeTree_integral_slack_bound {S : Finset V} {G : SimpleGraph V}
    (hG : ThreeTreeOn S G) {z : SetFunction V}
    (hz : Supermodular z) (hint : IntegerValued z)
    (hy : CliqueSupported G (mobius z)) {a : ℝ}
    (hbound : ∀ u v,u≠v → G.Adj u v → ∀ T,u∉T → v∉T → delta z u v T≤a)
    {u v : V} (huv : G.Adj u v) :
    (Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset V)⊆C),|mobius z C|) : ℝ)≤a := by
  classical
  have hne := G.ne_of_adj huv
  let g:=edgeCoefficients (mobius z) u v
  have heval (x : V → ℝ) (hx : ∀ w,x w=0 ∨ x w=1) :
      ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x=
        delta z u v (((booleanSupport x).erase u).erase v) := by
    simpa only [zeta_mobius] using edgeCoefficients_boolean_quadratic hy
      (fun C hc => hG.clique_card_le_four hc) hne x hx
  have hinterval : ∀ x : V → ℝ,(∀ w,x w=0 ∨ x w=1) →
      0≤ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x ∧
      ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x≤a := by
    intro x hx
    rw [heval x hx]
    exact ⟨hz.elemental u v hne _ (by simp) (by simp),
      hbound u v hne huv _ (by simp) (by simp)⟩
  have hinteger : ∀ x : V → ℝ,(∀ w,x w=0 ∨ x w=1) →
      ∃ k : ℤ,ForestSigns.quadratic (edgeLink G u v) (g ∅)
        (fun w => g {w}) (fun e => g e.toFinset) x=k := by
    intro x hx
    rw [heval x hx]
    exact hint.delta u v _
  have hosc := ForestSigns.integral_quadratic_oscillation_lower (edgeLink G u v)
    (hG.edgeLink_acyclic huv) (g ∅) (fun w => g {w}) (fun e => g e.toFinset)
    0 a hinterval hinteger
  simpa only [g,sum_edgeCoefficients_abs huv (mobius z),sub_zero] using hosc

end GraphicalZonotopes
