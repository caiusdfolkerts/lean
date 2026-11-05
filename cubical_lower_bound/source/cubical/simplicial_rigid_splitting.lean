import cubical.simplicial_fogelsanger_decomposition
import cubical.generic_vertex_splitting

/-! # Rigidity of the completed parts under vertex splitting -/

namespace Cubical.Simplicial

open Module
open Cubical.Rigidity

variable {V E : Type*} [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The completed part is obtained from its contracted family by a
genuine Whiteley vertex split. All support and fiber claims are proved
from the explicit finite simplicial chains. -/
theorem EdgeCircuitPartition.lifted_genericallyRigid {u v : V} (huv : u ≠ v)
    {s : Finset (Finset V)} (p : EdgeCircuitPartition u v s)
    {n : ℕ} (hn : 3 ≤ n) (hpure : Pure n id s)
    (hs : IsFacetCircuit id s) (he : (oneSkeleton id s).Adj u v)
    {a : Finset (Finset V)} (ha : a ∈ p.parts)
    (hG : GenericallyRigid (supportGraph (contractedSimplex u v) a) E)
    (hdim : finrank ℝ E = n) :
    GenericallyRigid (supportGraph id (liftedPart u v a)) E := by
  classical
  let L := liftedPart u v a
  let X := {x // x ∈ vertices id L}
  let Y := {x // x ∈ vertices (contractedSimplex u v) a}
  have hvertices : vertices id L = vertices id a :=
    EdgeCircuitPartition.lifted_vertices_eq huv p hpure ha
  have hEdge : (oneSkeleton id L).Adj u v := p.lifted_has_edge huv hs he ha
  have hmem := oneSkeleton_adj_vertices hEdge
  have humem : u ∈ vertices id a := hvertices ▸ hmem.1
  have hvL : v ∈ vertices id L := hmem.2
  have hcontract : vertices (contractedSimplex u v) a = (vertices id L).erase v := by
    rw [contracted_vertices huv a humem, hvertices]
  let uL : X := ⟨u, hmem.1⟩
  let vL : X := ⟨v, hvL⟩
  let f : X → Y := fun x => ⟨collapse u v x.val, by
    rw [hcontract]
    by_cases hxv : x.val = v
    · simpa [collapse, hxv, huv] using hmem.1
    · simpa [collapse, hxv] using x.property⟩
  have hsurj : Function.Surjective f := by
    intro y
    have hymem : y.val ∈ (vertices id L).erase v := by
      rw [← hcontract]
      exact y.property
    have hy := Finset.mem_erase.mp hymem
    refine ⟨⟨y.val, hy.2⟩, ?_⟩
    apply Subtype.ext
    simp only [f]
    exact ite_eq_right hy.1
  have hfiber : ∀ x y : X, f x = f y ↔
      x = uL ∧ y = vL ∨ x = vL ∧ y = uL ∨ x = y := by
    intro x y
    constructor
    · intro h
      have hv : collapse u v x.val = collapse u v y.val :=
        congrArg (fun z : Y => z.val) h
      rcases (collapse_eq_iff huv x.val y.val).mp hv with hxy | hxy | hxy
      · exact Or.inr (Or.inr (Subtype.ext hxy))
      · exact Or.inl ⟨Subtype.ext hxy.1, Subtype.ext hxy.2⟩
      · exact Or.inr (Or.inl ⟨Subtype.ext hxy.1, Subtype.ext hxy.2⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl)
      · apply Subtype.ext
        simp [f, uL, vL, collapse, huv]
      · apply Subtype.ext
        simp [f, uL, vL, collapse, huv]
      · rfl
  have hcover : ∀ w z : Y, (supportGraph (contractedSimplex u v) a).Adj w z →
      ∃ x y : X, f x = w ∧ f y = z ∧ (supportGraph id L).Adj x y := by
    intro w z hwz
    obtain ⟨hwz, t, ht, hwt, hzt⟩ := hwz
    rw [contractedSimplex_eq_image] at hwt hzt
    obtain ⟨x, hxt, hxw⟩ := Finset.mem_image.mp hwt
    obtain ⟨y, hyt, hyz⟩ := Finset.mem_image.mp hzt
    have htL : t ∈ L := (mem_offEdge u v L t).mp
      ((p.lifted_offEdge huv ha).symm ▸ ht) |>.1
    have hxL : x ∈ vertices id L := (mem_vertices id L x).mpr ⟨t, htL, hxt⟩
    have hyL : y ∈ vertices id L := (mem_vertices id L y).mpr ⟨t, htL, hyt⟩
    refine ⟨⟨x, hxL⟩, ⟨y, hyL⟩, Subtype.ext hxw, Subtype.ext hyz, ?_⟩
    refine ⟨?_, t, htL, hxt, hyt⟩
    intro hxy
    change x = y at hxy
    apply hwz
    exact hxw.symm.trans (hxy ▸ hyz)
  obtain ⟨c, hc, hcommon⟩ := cycle_common_neighbors hn (p.lifted_pure huv hpure ha)
    (p.lifted_cycle huv ha) hEdge
  let inc : c ↪ X := ⟨fun x => ⟨x.val,
    (oneSkeleton_adj_vertices (hcommon x.val x.property).1).2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : X => z.val) hxy⟩
  let common : Finset X := Finset.univ.map inc
  have hcommonX : ∀ x ∈ common, (supportGraph id L).Adj uL x ∧
      (supportGraph id L).Adj vL x := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    exact hcommon y.val y.property
  apply hG.of_vertex_collapse_finset f uL vL
    (fun h => huv (congrArg Subtype.val h)) hsurj
    (fun x y => by simpa only [or_comm, or_left_comm, or_assoc] using hfiber x y)
    hEdge hcover common hcommonX
  · omega
  · have hcard : common.card = c.card := by simp [common]
    omega

end Cubical.Simplicial
