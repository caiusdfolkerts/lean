module
public import shared_results.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialColumnPrefixGraph -/
section

/-! # Literal initial-column subgraphs

The graph is kept on the original vertex set. Vertices outside the prefix
are isolated, so all ideals remain in the same polynomial ring.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial
universe u
variable {N r : ℕ}

/-- The induced initial-column subgraph, with the other vertices isolated. -/
def initialColumnGraph (G : SimpleGraph (Fin N)) (c : ℕ) : SimpleGraph (Fin N) where
  Adj i j := G.Adj i j ∧ i.val<c ∧ j.val<c
  symm := ⟨by intro i j h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro i h; exact G.irrefl h.1⟩

@[simp] theorem initialColumnGraph_adj (G : SimpleGraph (Fin N)) (c : ℕ) (i j : Fin N) :
    (initialColumnGraph G c).Adj i j ↔ G.Adj i j ∧ i.val<c ∧ j.val<c := Iff.rfl

theorem initialColumnGraph_interval (G : SimpleGraph (Fin N))
    (hG : IntervalLabeling G) (c : ℕ) : IntervalLabeling (initialColumnGraph G c) := by
  intro i j k hij hjk hik
  obtain ⟨hijG,hjkG⟩ := hG i j k hij hjk hik.1
  have hjc : j.val<c := lt_trans hjk hik.2.2
  exact ⟨⟨hijG,hik.2.1,hjc⟩,⟨hjkG,hjc,hik.2.2⟩⟩

theorem initialColumnGraph_lattice (G : SimpleGraph (Fin N)) (c : ℕ) :
    graphEdgeLattice (initialColumnGraph G c)=initialColumnPrefix (graphEdgeLattice G) c := by
  ext a
  simp only [mem_graphEdgeLattice,initialColumnGraph_adj,mem_initialColumnPrefix]
  rw [mem_graphEdgeLattice G a]
  change (a 0<a 1 ∧ G.Adj (a 0) (a 1) ∧ (a 0).val<c ∧ (a 1).val<c) ↔
    (a 0<a 1 ∧ G.Adj (a 0) (a 1)) ∧ (a 1).val<c
  constructor
  · rintro ⟨ha,hG,_,hc⟩; exact ⟨⟨ha,hG⟩,hc⟩
  · rintro ⟨⟨ha,hG⟩,hc⟩; exact ⟨ha,hG,lt_trans ha hc,hc⟩

variable {K : Type u} [CommRing K]

theorem initialColumnGraph_binomial_mono (G : SimpleGraph (Fin N)) :
    Monotone (fun c => graphBinomialIdeal (k := K) (initialColumnGraph G c)) := by
  intro c e hce
  apply Ideal.span_mono
  rintro f ⟨i,j,hij,hG,rfl⟩
  exact ⟨i,j,hij,⟨hG.1,hG.2.1.trans_le hce,hG.2.2.trans_le hce⟩,rfl⟩

end FourPapers.Sublattice

end
end
end

end
