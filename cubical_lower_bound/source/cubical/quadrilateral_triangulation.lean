import cubical.indexed_pseudomanifold
import cubical.fogelsanger
import cubical.labeled_rigidity_count
import Mathlib.Data.Finset.Prod

/-!
# Triangulating a two-colored quadrilateral surface

Each facet has two black and two white vertices. The two triangles are
its black diagonal together with either white corner. Every original
edge has two incident facets, and every new diagonal has two incident
triangles. These facts give a genuine minimal simplicial `𝔽₂` 2-cycle.
-/

namespace Cubical.Quadrilateral

open Cubical.Simplicial
open scoped BigOperators

variable {B W F : Type*} [DecidableEq B] [DecidableEq W]

/-- Ridge adjacency of quadrilaterals, expressed by a common black-white
edge. Self-steps are harmless in its reflexive-transitive closure. -/
def FacetStep (black : F → Finset B) (white : F → Finset W) (f g : F) : Prop :=
  ∃ b, b ∈ black f ∧ b ∈ black g ∧ ∃ w, w ∈ white f ∧ w ∈ white g

/-- Explicit finite square-incidence data, separate from any rigidity
or face-number conclusion. -/
structure Surface (adj : B → W → Prop) (F : Type*) [Fintype F] where
  black : F → Finset B
  white : F → Finset W
  black_card : ∀ f, (black f).card = 2
  white_card : ∀ f, (white f).card = 2
  black_injective : Function.Injective black
  complete : ∀ f b, b ∈ black f → ∀ w, w ∈ white f → adj b w
  edge_facets : ∀ b w, adj b w →
    (Finset.univ.filter (fun f => b ∈ black f ∧ w ∈ white f)).card = 2
  cover_black : ∀ b, ∃ f, b ∈ black f
  cover_white : ∀ w, ∃ f, w ∈ white f
  connected : ∀ f g, Relation.ReflTransGen (FacetStep black white) f g

namespace Surface

variable [Fintype F] {adj : B → W → Prop} (S : Surface adj F)

/-- The two triangles in a square are indexed by their white corner. -/
abbrev Triangle := Σ f : F, {w // w ∈ S.white f}

/-- A triangle consists of the black diagonal and one white corner. -/
def triangle (i : S.Triangle) : Finset (B ⊕ W) :=
  insert (Sum.inr i.2.val) ((S.black i.1).image Sum.inl)

@[simp]
theorem mem_triangle_black (i : S.Triangle) (b : B) :
    Sum.inl b ∈ S.triangle i ↔ b ∈ S.black i.1 := by
  simp [triangle]

@[simp]
theorem mem_triangle_white (i : S.Triangle) (w : W) :
    Sum.inr w ∈ S.triangle i ↔ w = i.2.val := by
  simp [triangle]

/-- Each triangle has exactly three vertices. -/
theorem triangle_card (i : S.Triangle) : (S.triangle i).card = 3 := by
  classical
  simp [triangle, Finset.card_image_of_injective _ Sum.inl_injective, S.black_card]

/-- The three ridges of a triangle: its black diagonal and its two
black-white edges. -/
theorem triangle_boundary (i : S.Triangle) (r : Finset (B ⊕ W)) :
    r ∈ simplexBoundary (S.triangle i) ↔
      r = (S.black i.1).image Sum.inl ∨
        ∃ b ∈ S.black i.1, r = {Sum.inl b, Sum.inr i.2.val} := by
  classical
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp (S.black_card i.1)
  simp only [triangle, hp, simplexBoundary, Finset.image_insert, Finset.image_singleton]
  simp [Finset.erase_insert_of_ne, Finset.erase_insert, hab, hab.symm,
    Finset.pair_comm, or_assoc, or_left_comm, or_comm]

/-- A pair of black vertices cannot be a mixed black-white edge. -/
theorem black_diagonal_ne_mixed (s : Finset B) (b : B) (w : W) :
    s.image Sum.inl ≠ ({Sum.inl b, Sum.inr w} : Finset (B ⊕ W)) := by
  intro h
  have hm : Sum.inr w ∈ s.image Sum.inl := by rw [h]; simp
  simpa using hm

@[simp]
theorem mixed_pair_eq (b b' : B) (w w' : W) :
    ({Sum.inl b, Sum.inr w} : Finset (B ⊕ W)) = {Sum.inl b', Sum.inr w'} ↔
      b = b' ∧ w = w' := by
  constructor
  · intro h
    have hb : Sum.inl b ∈ ({Sum.inl b', Sum.inr w'} : Finset (B ⊕ W)) := by rw [← h]; simp
    have hw : Sum.inr w ∈ ({Sum.inl b', Sum.inr w'} : Finset (B ⊕ W)) := by rw [← h]; simp
    exact ⟨by simpa using hb, by simpa using hw⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A black diagonal is incident precisely to the triangles of its own
quadrilateral, by uniqueness of the diagonal. -/
theorem diagonal_ridge_iff (f : F) (i : S.Triangle) :
    (S.black f).image Sum.inl ∈ simplexBoundary (S.triangle i) ↔ i.1 = f := by
  rw [S.triangle_boundary]
  constructor
  · rintro (h | ⟨b, hb, h⟩)
    · exact (S.black_injective ((Finset.image_injective Sum.inl_injective) h)).symm
    · exact (black_diagonal_ne_mixed _ b i.2.val h).elim
  · intro h
    exact Or.inl (by rw [h])

/-- A mixed edge belongs to a triangle exactly when that triangle has
the specified white corner and contains the specified black vertex. -/
theorem mixed_ridge_iff (b : B) (w : W) (i : S.Triangle) :
    ({Sum.inl b, Sum.inr w} : Finset (B ⊕ W)) ∈ simplexBoundary (S.triangle i) ↔
      b ∈ S.black i.1 ∧ i.2.val = w := by
  rw [S.triangle_boundary]
  constructor
  · rintro (h | ⟨b', hb', h⟩)
    · exact (black_diagonal_ne_mixed _ b w h.symm).elim
    · obtain ⟨rfl, hw⟩ := (mixed_pair_eq b b' w i.2.val).mp h
      exact ⟨hb', hw.symm⟩
  · rintro ⟨hb, hw⟩
    exact Or.inr ⟨b, hb, by rw [hw]⟩

/-- In a two-element set, a specified element has one distinct partner. -/
private theorem pair_other {A : Type*} [DecidableEq A] {s : Finset A}
    (hs : s.card = 2) (x : A) (hx : x ∈ s) :
    ∃ y, y ∈ s ∧ x ≠ y ∧ s = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨b, by simp, hab, rfl⟩
  · have hxb : x = b := Finset.mem_singleton.mp hx
    subst x
    exact ⟨a, by simp, hab.symm, Finset.pair_comm a b⟩

/-- Equality of triangle indices is equality of their facet and white
corner, regardless of membership proof choices. -/
theorem triangle_ext {i j : S.Triangle} (hf : i.1 = j.1)
    (hw : i.2.val = j.2.val) : i = j := by
  rcases i with ⟨f, w⟩
  rcases j with ⟨g, z⟩
  dsimp only at hf hw
  subst g
  exact congrArg (Sigma.mk f) (Subtype.ext hw)

/-- Each triangle ridge has precisely one partner triangle. -/
theorem ridgePairing : RidgePairing S.triangle := by
  classical
  intro i r hr
  rcases (S.triangle_boundary i r).mp hr with rfl | ⟨b, hb, rfl⟩
  · obtain ⟨w, hw, hwi, hpair⟩ := pair_other (S.white_card i.1) i.2.val i.2.property
    let j : S.Triangle := ⟨i.1, ⟨w, hw⟩⟩
    refine ⟨j, ?_, ?_⟩
    · intro hij
      exact hwi (congrArg (fun t : S.Triangle => t.2.val) hij)
    · intro k
      rw [S.diagonal_ridge_iff]
      constructor
      · intro hk
        have hkw : k.2.val ∈ S.white i.1 := hk ▸ k.2.property
        rw [hpair] at hkw
        rcases Finset.mem_insert.mp hkw with hkw | hkw
        · exact Or.inl (S.triangle_ext hk hkw)
        · exact Or.inr (S.triangle_ext hk (Finset.mem_singleton.mp hkw))
      · rintro (rfl | rfl) <;> rfl
  · have he := S.complete i.1 b hb i.2.val i.2.property
    let facets := Finset.univ.filter (fun f => b ∈ S.black f ∧ i.2.val ∈ S.white f)
    have hif : i.1 ∈ facets := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hb, i.2.property⟩
    obtain ⟨g, hg, hfg, hpair⟩ := pair_other (S.edge_facets b i.2.val he) i.1 hif
    change facets = {i.1, g} at hpair
    have hg' : b ∈ S.black g ∧ i.2.val ∈ S.white g := (Finset.mem_filter.mp hg).2
    let j : S.Triangle := ⟨g, ⟨i.2.val, hg'.2⟩⟩
    refine ⟨j, ?_, ?_⟩
    · intro hij
      exact hfg (congrArg Sigma.fst hij)
    · intro k
      rw [S.mixed_ridge_iff]
      constructor
      · rintro ⟨hbk, hwk⟩
        have hkf : k.1 ∈ facets := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hbk, by rw [← hwk]; exact k.2.property⟩
        rw [hpair] at hkf
        rcases Finset.mem_insert.mp hkf with hkf | hkf
        · exact Or.inl (S.triangle_ext hkf hwk)
        · exact Or.inr (S.triangle_ext (Finset.mem_singleton.mp hkf) hwk)
      · rintro (rfl | rfl)
        · exact ⟨hb, rfl⟩
        · exact ⟨hg'.1, rfl⟩

/-- The two triangles of one facet are connected across its black diagonal. -/
theorem reachable_same_facet (i j : S.Triangle) (hf : i.1 = j.1) :
    (indexedFacetGraph S.triangle).Reachable i j := by
  by_cases hij : i = j
  · subst j
    exact SimpleGraph.Reachable.refl i
  · apply SimpleGraph.Adj.reachable
    exact ⟨hij, (S.black i.1).image Sum.inl,
      (S.diagonal_ridge_iff i.1 i).mpr rfl, (S.diagonal_ridge_iff i.1 j).mpr hf.symm⟩

/-- A common original edge connects the two triangulated facets. -/
theorem reachable_of_facet_step (i j : S.Triangle)
    (hstep : FacetStep S.black S.white i.1 j.1) :
    (indexedFacetGraph S.triangle).Reachable i j := by
  obtain ⟨b, hbi, hbj, w, hwi, hwj⟩ := hstep
  let a : S.Triangle := ⟨i.1, ⟨w, hwi⟩⟩
  let z : S.Triangle := ⟨j.1, ⟨w, hwj⟩⟩
  have haz : (indexedFacetGraph S.triangle).Reachable a z := by
    by_cases h : a = z
    · rw [h]
    · apply SimpleGraph.Adj.reachable
      exact ⟨h, {Sum.inl b, Sum.inr w},
        (S.mixed_ridge_iff b w a).mpr ⟨hbi, rfl⟩,
        (S.mixed_ridge_iff b w z).mpr ⟨hbj, rfl⟩⟩
  exact (S.reachable_same_facet i a rfl).trans
    (haz.trans (S.reachable_same_facet z j rfl))

/-- Connected square facets give a connected triangulated dual graph. -/
theorem triangulation_connected [Nonempty F] : (indexedFacetGraph S.triangle).Connected := by
  classical
  have hwhite : ∀ f, ∃ w, w ∈ S.white f := by
    intro f
    have hn : (S.white f).Nonempty := Finset.card_pos.mp (by rw [S.white_card]; decide)
    exact hn
  choose w hw using hwhite
  let rep : F → S.Triangle := fun f => ⟨f, ⟨w f, hw f⟩⟩
  have hrep : ∀ f g, (indexedFacetGraph S.triangle).Reachable (rep f) (rep g) := by
    intro f g
    have hpath := S.connected f g
    induction hpath with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail g h hfg hgh ih => exact ih.trans (S.reachable_of_facet_step (rep g) (rep h) hgh)
  have : Nonempty S.Triangle := ⟨rep (Classical.arbitrary F)⟩
  constructor
  intro i j
  exact (S.reachable_same_facet i (rep i.1) rfl).trans
    ((hrep i.1 j.1).trans (S.reachable_same_facet (rep j.1) j rfl))

/-- The black-diagonal triangulation is a complete minimal 2-cycle. -/
theorem triangulation_circuit [Nonempty F] :
    IsFacetCircuit S.triangle Finset.univ :=
  facetCircuit_of_ridgePairing_connected S.ridgePairing S.triangulation_connected

/-- Its triangles are homogeneous of cardinality three. -/
theorem triangulation_pure : Pure 3 S.triangle Finset.univ := fun i _ => S.triangle_card i

section Counting

variable [Fintype B] [Fintype W]
attribute [local instance] Classical.propDecidable
include S

/-- The original black-white edges, without an orientation multiplicity. -/
abbrev Edge := {bw : B × W // adj bw.1 bw.2}

/-- Every vertex occurs in the triangulation. -/
theorem triangulation_vertices : vertices S.triangle Finset.univ = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_univ, iff_true]
  cases v with
  | inl b =>
    obtain ⟨f, hf⟩ := S.cover_black b
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [S.white_card f]; decide)
    exact Finset.mem_biUnion.mpr ⟨⟨f, ⟨w, hw⟩⟩, Finset.mem_univ _,
      (S.mem_triangle_black _ b).mpr hf⟩
  | inr w =>
    obtain ⟨f, hf⟩ := S.cover_white w
    exact Finset.mem_biUnion.mpr ⟨⟨f, ⟨w, hf⟩⟩, Finset.mem_univ _,
      (S.mem_triangle_white _ w).mpr rfl⟩

/-- Counting edge-facet incidences gives four per square and two per
original edge. -/
theorem incidence_count : 2 * Fintype.card (Edge (adj := adj)) = 4 * Fintype.card F := by
  classical
  let e : (Σ f : F, {b // b ∈ S.black f} × {w // w ∈ S.white f}) ≃
      (Σ bw : Edge (adj := adj), {f // bw.val.1 ∈ S.black f ∧ bw.val.2 ∈ S.white f}) :=
    { toFun := fun x => ⟨⟨(x.2.1.val, x.2.2.val),
        S.complete x.1 x.2.1.val x.2.1.property x.2.2.val x.2.2.property⟩,
        ⟨x.1, x.2.1.property, x.2.2.property⟩⟩
      invFun := fun x => ⟨x.2.val, ⟨⟨x.1.val.1, x.2.property.1⟩,
        ⟨x.1.val.2, x.2.property.2⟩⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  have hc : ∀ bw : Edge (adj := adj),
      Fintype.card {f // bw.val.1 ∈ S.black f ∧ bw.val.2 ∈ S.white f} = 2 := by
    intro bw
    rw [Fintype.card_subtype]
    exact S.edge_facets _ _ bw.property
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe,
    S.black_card, S.white_card, hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at he
  omega

/-- The triangulated rigidity count uses exactly the original edges
and one selected diagonal for each square as its equation labels. -/
theorem triangulation_count [Nonempty F] :
    3 * (Fintype.card B + Fintype.card W) ≤
      Fintype.card (Edge (adj := adj)) + Fintype.card F + 6 := by
  classical
  let U := {v // v ∈ vertices S.triangle Finset.univ}
  let inc : B ⊕ W → U := fun v => ⟨v, by rw [S.triangulation_vertices]; simp⟩
  have hinj : Function.Injective inc := fun _ _ h => congrArg Subtype.val h
  have hsurj : Function.Surjective inc := fun v => ⟨v.val, Subtype.ext rfl⟩
  have hcardU : Fintype.card U = Fintype.card B + Fintype.card W := by
    rw [← Fintype.card_congr (Equiv.ofBijective inc ⟨hinj, hsurj⟩), Fintype.card_sum]
  have hpairs : ∀ f, ∃ a b, a ≠ b ∧ S.black f = {a, b} := fun f =>
    Finset.card_eq_two.mp (S.black_card f)
  choose a b hab hpair using hpairs
  let L := Edge (adj := adj) ⊕ F
  let left : L → U := Sum.elim (fun e => inc (.inl e.val.1)) (fun f => inc (.inl (a f)))
  let right : L → U := Sum.elim (fun e => inc (.inr e.val.2)) (fun f => inc (.inl (b f)))
  have hcover : ∀ x y : U, (supportGraph S.triangle Finset.univ).Adj x y → ∃ l,
      (left l = x ∧ right l = y) ∨ (left l = y ∧ right l = x) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨hne, i, _, hxi, hyi⟩
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hx' := (S.mem_triangle_black i x).mp hxi
        have hy' := (S.mem_triangle_black i y).mp hyi
        rw [hpair i.1] at hx' hy'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
        refine ⟨Sum.inr i.1, ?_⟩
        rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
        · exact (hne rfl).elim
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact (hne rfl).elim
      | inr y =>
        have hx' := (S.mem_triangle_black i x).mp hxi
        have hy' := (S.mem_triangle_white i y).mp hyi
        let e : Edge (adj := adj) := ⟨(x, y), S.complete i.1 x hx' y
          (hy' ▸ i.2.property)⟩
        exact ⟨Sum.inl e, Or.inl ⟨rfl, rfl⟩⟩
    | inr x =>
      cases y with
      | inl y =>
        have hx' := (S.mem_triangle_white i x).mp hxi
        have hy' := (S.mem_triangle_black i y).mp hyi
        let e : Edge (adj := adj) := ⟨(y, x), S.complete i.1 y hy' x
          (hx' ▸ i.2.property)⟩
        exact ⟨Sum.inl e, Or.inr ⟨rfl, rfl⟩⟩
      | inr y =>
        have hx' := (S.mem_triangle_white i x).mp hxi
        have hy' := (S.mem_triangle_white i y).mp hyi
        exact (hne (congrArg Sum.inr (hx'.trans hy'.symm))).elim
  obtain ⟨p, hp⟩ := S.triangulation_circuit.genericallyRigid
    (E := EuclideanSpace ℝ (Fin 3)) (by decide) S.triangulation_pure
    (by simp)
  have h := hp.edge_count_of_edge_cover left right hcover
  norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceAdd,
    Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_self] at h
  change 3 * Fintype.card U ≤ Fintype.card L + 6 at h
  simpa only [hcardU, L, Fintype.card_sum] using h

/-- The dimension-three cubical edge lower bound, with no assumed Euler
formula: it follows from the verified triangulated rigidity theorem. -/
theorem edge_lower_bound [Nonempty F] :
    2 * (Fintype.card B + Fintype.card W) ≤ Fintype.card (Edge (adj := adj)) + 4 := by
  have hi := S.incidence_count
  have ht := S.triangulation_count
  omega

/-- The corresponding lower bound on quadrilateral facets. -/
theorem facet_lower_bound [Nonempty F] :
    Fintype.card B + Fintype.card W ≤ Fintype.card F + 2 := by
  have hi := S.incidence_count
  have ht := S.triangulation_count
  omega

end Counting

end Surface
end Cubical.Quadrilateral
