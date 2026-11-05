import cubical.stars
import cubical.facet_determination
import cubical.facet_rank
import cubical.generic_neighbors
import cubical.generic_certificates
import cubical.rigidity_to_local
import cubical.generic_rigidity
import cubical.counting

/-!
# Assembly of the cubical rigidity bound

This file joins the independent polynomial rank witnesses for all local
stars and all black vertices inside facets. One common parameter choice
then gives local propagation, injective restriction to every facet, the
facet nullity calculation, and the asymmetric edge bound.

The hypotheses here are explicit incidence and rigidity data. The convex
polytope and PL-sphere applications must establish those hypotheses from
their geometric definitions.
-/

namespace Cubical

open Module Matrix
attribute [local instance] Classical.propDecidable

noncomputable section

variable {B W E F : Type*} {black : E → B} {white : E → W}

namespace FacetCover

/-- A white vertex together with a facet containing it. -/
abbrev WhiteIncidence (C : FacetCover black white F) :=
  {fw : F × W // C.whiteMem fw.1 fw.2}

/-- Actual facet edges incident to a specified black facet vertex. -/
abbrev EdgeAtBlack (C : FacetCover black white F) (f : F)
    (b : {b : B // C.blackMem f b}) :=
  {e : {e : E // C.edgeMem f e} // C.facetBlack f e = b}

/-- Local graph and square data for every facet-white incidence. The
center and pins are explicitly tied to the facet incidence relation. -/
structure StarCover (C : FacetCover black white F)
    (N L T : C.WhiteIncidence → Type*) where
  star : ∀ j, StarData black white (N j) (L j) (T j)
  center : ∀ j, (star j).center = j.val.2
  covers : ∀ j e, white e = (star j).center → ∃ n, (star j).neighbor n = black e
  pinMem : ∀ j t, C.blackMem j.val.1 ((star j).neighbor ((star j).pin t))
  link : ∀ j, SimpleGraph (N j)
  linkEdges : ∀ j a b, (link j).Adj a b → ∃ e,
    ((star j).left e = a ∧ (star j).right e = b) ∨
      ((star j).left e = b ∧ (star j).right e = a)
  pin_injective : ∀ j, Function.Injective (star j).pin
  opposite_injective : ∀ j, Function.Injective (star j).opposite
  opposite_ne_center : ∀ j e, (star j).opposite e ≠ (star j).center

variable [Fintype B] [Fintype W] [Fintype E] [Fintype F]

omit [Fintype B] [Fintype W] [Fintype E] [Fintype F] in
/-- A rigid link has a placement for which the selected facet vertices
provide all the pins required by the normalized local system. -/
theorem StarCover.exists_pinned_witness
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k))) :
    ∀ j, ∃ q : N j → Fin k → ℝ,
      Local.PinnedRigid k (D.star j).left (D.star j).right (D.star j).pin q := by
  intro j
  have : Nonempty (T j) := Fintype.card_pos_iff.mp (by rw [hpin]; exact hk)
  obtain ⟨q, hq, hpos⟩ := (hlink j).exists_in_general_position
  have hpins : AffineIndependent ℝ (q ∘ (D.star j).pin) :=
    (hpos.linearIndependent (D.star j).pin (D.pin_injective j) (by simp [hpin])).affineIndependent
  exact ⟨fun b i => q b i, Local.pinnedRigid_of_rigid k (D.link j)
    (D.star j).left (D.star j).right (D.star j).pin (D.linkEdges j) q hq hpins
    (by rw [hpin])⟩

omit [Fintype B] [Fintype W] [Fintype E] [Fintype F] in
/-- Full column rank of every local star matrix implies the local
propagation property used by the facet cover. -/
theorem StarCover.localPropagation_of_rank
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    [∀ j, Nonempty (T j)] (D : C.StarCover N L T)
    (d : ℕ) (p : W → Fin d → ℝ)
    (hrank : ∀ j, Function.Injective
      (evalMatrix ((D.star j).matrix d) (fun wi => p wi.1 wi.2)).mulVec) :
    C.LocalPropagation d p := by
  intro m hm f w hw hpin e he
  let j : C.WhiteIncidence := ⟨(f, w), hw⟩
  have hpin' : ∀ t, m.1 ((D.star j).neighbor ((D.star j).pin t)) = 0 := by
    intro t
    have h := hpin ((D.star j).centralEdge ((D.star j).pin t))
      (by rw [(D.star j).centralWhite, D.center])
      (by rw [(D.star j).centralBlack]; exact D.pinMem j t)
    simpa only [(D.star j).centralBlack] using h
  obtain ⟨n, hn⟩ := D.covers j e (by rw [D.center]; exact he)
  rw [← hn]
  exact (D.star j).propagate d p (hrank j) m hm hpin' n

/-- A nonzero polynomial certifies local propagation and independent
facet equations simultaneously for every parameter outside its zero set. -/
theorem StarCover.generic_parameters
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}),
      Fintype.card (C.EdgeAtBlack f b) ≤ k + 1) :
    ∃ P : MvPolynomial (W × Fin (k + 1)) ℝ, P ≠ 0 ∧
      ∀ x : W × Fin (k + 1) → ℝ, MvPolynomial.eval x P ≠ 0 →
        C.LocalPropagation (k + 1) (fun w i => x (w, i)) ∧
          ∀ f (b : {b : B // C.blackMem f b}),
            LinearIndependent ℝ (fun e : C.EdgeAtBlack f b => fun i => x (white e.val.val, i)) := by
  classical
  let : ∀ j, Nonempty (T j) := fun j =>
    Fintype.card_pos_iff.mp (by rw [hpin]; exact hk)
  have hlocal : ∀ j, ∃ x : W × Fin (k + 1) → ℝ,
      Function.Injective (evalMatrix ((D.star j).matrix (k + 1)) x).mulVec := by
    intro j
    obtain ⟨q, hq⟩ := D.exists_pinned_witness k hk hpin hlink j
    exact Local.exists_injective_specialization k (D.star j).center (D.star j).opposite
      (D.star j).left (D.star j).right (D.star j).pin
      (D.opposite_injective j) (D.opposite_ne_center j) q hq
  let K := Σ f : F, {b : B // C.blackMem f b}
  let neighbors : ∀ a : K, C.EdgeAtBlack a.1 a.2 → W := fun a e => white e.val.val
  have hneighbor : ∀ a : K, ∃ x : W × Fin (k + 1) → ℝ,
      Function.Injective (evalMatrix (neighborPolynomialMatrix (k + 1) (neighbors a)) x).mulVec := by
    intro a
    exact neighborMatrix_has_injective_specialization (k + 1) (neighbors a)
      (hwhite a.1 a.2) (hdegree a.1 a.2)
  obtain ⟨P, hP, hgeneric⟩ := simultaneous_injective_certificate_pair
    (fun j => (D.star j).matrix (k + 1))
    (fun a : K => neighborPolynomialMatrix (k + 1) (neighbors a)) hlocal hneighbor
  refine ⟨P, hP, ?_⟩
  intro x hx
  obtain ⟨hxlocal, hxneighbor⟩ := hgeneric x hx
  refine ⟨D.localPropagation_of_rank (k + 1) _ hxlocal, ?_⟩
  intro f b
  exact (neighborMatrix_injective_iff (k + 1) (neighbors ⟨f, b⟩) x).mp (hxneighbor ⟨f, b⟩)

/-- One parameter placement simultaneously satisfies local propagation
and independent facet edge equations at every black vertex. -/
theorem StarCover.exists_parameters
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}),
      Fintype.card (C.EdgeAtBlack f b) ≤ k + 1) :
    ∃ p : W → Fin (k + 1) → ℝ, C.LocalPropagation (k + 1) p ∧
      ∀ f (b : {b : B // C.blackMem f b}),
        LinearIndependent ℝ (fun e : C.EdgeAtBlack f b => p (white e.val.val)) := by
  obtain ⟨P, hP, hgeneric⟩ := D.generic_parameters k hk hpin hlink hwhite hdegree
  obtain ⟨x, hx⟩ := exists_eval_ne_zero hP
  exact ⟨fun w i => x (w, i), hgeneric x hx⟩

/-- An explicit nonzero polynomial certifies Proposition 3 for every
parameter outside its zero set: all facet restrictions are injective
and every facet solution space has dimension `2^k`. -/
theorem StarCover.generic_facet_determination
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}),
      Fintype.card (C.EdgeAtBlack f b) ≤ k + 1)
    (hblack_count : ∀ f, Fintype.card {b : B // C.blackMem f b} = 2 ^ (k - 1))
    (hwhite_count : ∀ f, Fintype.card {w : W // C.whiteMem f w} = 2 ^ (k - 1))
    (hedge_count : ∀ f, Fintype.card {e : E // C.edgeMem f e} = k * 2 ^ (k - 1)) :
    ∃ P : MvPolynomial (W × Fin (k + 1)) ℝ, P ≠ 0 ∧
      ∀ x : W × Fin (k + 1) → ℝ, MvPolynomial.eval x P ≠ 0 →
        (∀ f, Function.Injective (C.restriction (k + 1) (fun w i => x (w, i)) f)) ∧
        (∀ f, finrank ℝ (solutionSpace (k + 1) (C.facetBlack f) (C.facetWhite f)
          (fun w : {w : W // C.whiteMem f w} => fun i => x (w.val, i))) = 2 ^ k) := by
  obtain ⟨P, hP, hgeneric⟩ := D.generic_parameters k hk hpin hlink hwhite hdegree
  refine ⟨P, hP, ?_⟩
  intro x hx
  let p : W → Fin (k + 1) → ℝ := fun w i => x (w, i)
  obtain ⟨hprop, hind⟩ := hgeneric x hx
  refine ⟨fun f => C.restriction_injective (k + 1) p hprop f, ?_⟩
  intro f
  have h := balanced_facet_dimension k (2 ^ (k - 1)) (C.facetBlack f) (C.facetWhite f)
    (fun w : {w : W // C.whiteMem f w} => p w) (hind f)
    (hblack_count f) (hwhite_count f) (hedge_count f)
  have hpow : 2 * 2 ^ (k - 1) = 2 ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp [pow_succ, Nat.mul_comm]
  exact h.trans hpow

/-- Proposition 3 for an explicit cubical facet cover: a single common
parameter choice gives injective restriction to every facet, whose
solution space has dimension `2^k`. -/
theorem StarCover.exists_facet_determination
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}),
      Fintype.card (C.EdgeAtBlack f b) ≤ k + 1)
    (hblack_count : ∀ f, Fintype.card {b : B // C.blackMem f b} = 2 ^ (k - 1))
    (hwhite_count : ∀ f, Fintype.card {w : W // C.whiteMem f w} = 2 ^ (k - 1))
    (hedge_count : ∀ f, Fintype.card {e : E // C.edgeMem f e} = k * 2 ^ (k - 1)) :
    ∃ p : W → Fin (k + 1) → ℝ,
      (∀ f, Function.Injective (C.restriction (k + 1) p f)) ∧
      (∀ f, finrank ℝ (solutionSpace (k + 1) (C.facetBlack f) (C.facetWhite f)
        (fun w : {w : W // C.whiteMem f w} => p w)) = 2 ^ k) := by
  obtain ⟨P, hP, hgeneric⟩ := D.generic_facet_determination k hk hpin hlink hwhite hdegree
    hblack_count hwhite_count hedge_count
  obtain ⟨x, hx⟩ := exists_eval_ne_zero hP
  exact ⟨fun w i => x (w, i), hgeneric x hx⟩

/-- The asymmetric edge bound from the explicit local rigidity and
cubical incidence hypotheses. Its two color orientations give the
strengthened bound in the paper. -/
theorem StarCover.asymmetric_edge_bound
    {C : FacetCover black white F} {N L T : C.WhiteIncidence → Type*}
    [∀ j, Fintype (N j)] [∀ j, Fintype (L j)] [∀ j, Fintype (T j)]
    (D : C.StarCover N L T) (k : ℕ) (hk : 0 < k)
    (hpin : ∀ j, Fintype.card (T j) = k)
    (hlink : ∀ j, Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin k)))
    (hwhite : ∀ f (b : {b : B // C.blackMem f b}),
      Function.Injective (fun e : C.EdgeAtBlack f b => white e.val.val))
    (hdegree : ∀ f (b : {b : B // C.blackMem f b}),
      Fintype.card (C.EdgeAtBlack f b) ≤ k + 1)
    (hblack_count : ∀ f, Fintype.card {b : B // C.blackMem f b} = 2 ^ (k - 1))
    (hwhite_count : ∀ f, Fintype.card {w : W // C.whiteMem f w} = 2 ^ (k - 1))
    (hedge_count : ∀ f, Fintype.card {e : E // C.edgeMem f e} = k * 2 ^ (k - 1))
    (f : F) :
    (k + 1) * Fintype.card B + Fintype.card W ≤ Fintype.card E + 2 ^ k := by
  obtain ⟨p, hinj, hdim⟩ := D.exists_facet_determination k hk hpin hlink hwhite hdegree
    hblack_count hwhite_count hedge_count
  exact edge_count_of_injective_restriction (k + 1) (2 ^ k) black white p
    (C.restriction (k + 1) p f) (hinj f) (hdim f).le

end FacetCover

end
end Cubical
