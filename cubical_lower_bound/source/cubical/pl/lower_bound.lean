import cubical.pl.square_stars
import cubical.pl.facet_counts
import cubical.pl.face_counts
import cubical.pl.cell_cocycle
import cubical.abstract_card_bound

/-! # Corollary 4: the full cubical PL-sphere edge bound

The only geometric/topological hypothesis is that the original finite
cubical common-face complex has a genuine PL-sphere realization. All
bipartition, rigidity, purity, connectivity and incidence facts are proved.
-/

noncomputable section

namespace Cubical.PL.CubeComplex

open Classical Cubical.Bipartite

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

theorem asymmetric_edge_bound {m : ℕ} (hK : K.IsSphere m) (hm : 3 ≤ m)
    (c : K.graph.Coloring Bool) :
    (m + 1) * Fintype.card (Black c) + Fintype.card (White c) ≤
      K.faceNumber 1 + 2 ^ m := by
  have hm1 : 1 ≤ m := by omega
  let C := K.cubicalFacetCover hK hm1 c
  let D := K.cubicalStarCover hK hm1 c
  have hpin : ∀ j : C.WhiteIncidence,
      Fintype.card (K.FacetPins j.val.1 j.val.2.val) = m := by
    intro j
    exact K.facetPins_card j.val.1 j.val.2.val j.property
  have hlink : ∀ j : C.WhiteIncidence,
      Cubical.Rigidity.GenericallyRigid (D.link j) (EuclideanSpace ℝ (Fin m)) := by
    intro j
    exact K.neighborGraph_genericallyRigid_dim j.val.2.val hm hK
  have hwhite : ∀ F (b : {b : Black c // C.blackMem F b}),
      Function.Injective (fun e : C.EdgeAtBlack F b => white c e.val.val) := by
    intro F b
    exact K.facet_global_whiteEndpoint_injective hK hm1 c F b
  have hdegree : ∀ F (b : {b : Black c // C.blackMem F b}),
      Nat.card (C.EdgeAtBlack F b) ≤ m + 1 := by
    intro F b
    have hcard := K.facet_black_degree hK hm1 c F b
    have heq : Fintype.card (C.EdgeAtBlack F b) = m := by
      exact (Fintype.card_congr (Equiv.refl _)).trans hcard
    rw [Nat.card_eq_fintype_card, heq]
    exact Nat.le_succ _
  have hblack_count : ∀ F, Nat.card {b : Black c // C.blackMem F b} = 2 ^ (m - 1) := by
    intro F
    change Nat.card {b : Black c // b.val ∈ F.val.val} = _
    rw [Nat.card_eq_fintype_card]
    exact (K.facet_color_cards c F hm1).1
  have hwhite_count : ∀ F, Nat.card {w : White c // C.whiteMem F w} = 2 ^ (m - 1) := by
    intro F
    change Nat.card {w : White c // w.val ∈ F.val.val} = _
    rw [Nat.card_eq_fintype_card]
    exact (K.facet_color_cards c F hm1).2
  have hedge_count : ∀ F, Nat.card {e : Edge c // C.edgeMem F e} = m * 2 ^ (m - 1) := by
    intro F
    rw [Nat.card_eq_fintype_card]
    exact K.facet_edges_card hK hm1 c F
  obtain ⟨F⟩ := K.nonempty_facets hK
  have h := D.asymmetric_edge_bound_intrinsic m (by omega) hpin hlink hwhite hdegree
    hblack_count hwhite_count hedge_count F
  rwa [K.card_edges c] at h

/-- A proper two-colouring exists; it is a consequence of sphere topology. -/
theorem exists_coloring {m : ℕ} (hK : K.IsSphere m) (hm : 2 ≤ m) :
    Nonempty (K.graph.Coloring Bool) := by
  obtain ⟨c, hc⟩ := K.bipartite_of_orderSphere hm hK
  exact ⟨SimpleGraph.Coloring.mk c (fun {v w} h => hc v w h)⟩

/-- Corollary 4 in exact integral form, with the paper's dimension `d`. -/
theorem strengthened_edge_bound_nat (d : ℕ) (hd : 4 ≤ d)
    (hK : K.IsSphere (d - 1)) (c : K.graph.Coloring Bool) :
    (d + 1) * K.faceNumber 0 + (d - 1) *
      Nat.dist (Fintype.card (Black c)) (Fintype.card (White c)) ≤
        2 * K.faceNumber 1 + 2 ^ d := by
  have hd' : d - 1 + 1 = d := by omega
  have hb := K.asymmetric_edge_bound hK (by omega) c
  have hw := K.asymmetric_edge_bound hK (by omega) (swapColoring c)
  rw [hd'] at hb hw
  rw [Fintype.card_congr (swappedBlackEquiv c),
    Fintype.card_congr (swappedWhiteEquiv c)] at hw
  have hw' : Fintype.card (Black c) + d * Fintype.card (White c) ≤
      K.faceNumber 1 + 2 ^ (d - 1) := by simpa only [Nat.add_comm] using hw
  have h := Cubical.Counting.strengthened_nat d (Fintype.card (Black c))
    (Fintype.card (White c)) (K.faceNumber 1) (2 ^ (d - 1)) (by omega) hb hw'
  have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    conv_lhs => rw [← hd', pow_succ]
    exact Nat.mul_comm _ _
  rw [Cubical.Bipartite.card_vertices, ← K.faceNumber_zero, ← hpow] at h
  exact h

/-- **Corollary 4**, exactly the displayed strengthened inequality from
Theorem 1, for all finite cubical PL `(d-1)`-spheres, `d ≥ 4`. -/
theorem strengthened_edge_bound (d : ℕ) (hd : 4 ≤ d)
    (hK : K.IsSphere (d - 1)) (c : K.graph.Coloring Bool) :
    ((d : ℝ) + 1) / 2 * K.faceNumber 0 - 2 ^ (d - 1) +
      ((d : ℝ) - 1) / 2 *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ K.faceNumber 1 := by
  have hd' : d - 1 + 1 = d := by omega
  have hbN := K.asymmetric_edge_bound hK (by omega) c
  have hwN := K.asymmetric_edge_bound hK (by omega) (swapColoring c)
  rw [hd'] at hbN hwN
  rw [Fintype.card_congr (swappedBlackEquiv c),
    Fintype.card_congr (swappedWhiteEquiv c)] at hwN
  have hb : (d : ℝ) * Fintype.card (Black c) + Fintype.card (White c) ≤
      (K.faceNumber 1 : ℝ) + 2 ^ (d - 1) := by exact_mod_cast hbN
  have hw : (Fintype.card (Black c) : ℝ) + (d : ℝ) * Fintype.card (White c) ≤
      (K.faceNumber 1 : ℝ) + 2 ^ (d - 1) := by
    exact_mod_cast (by simpa only [Nat.add_comm] using hwN :
      Fintype.card (Black c) + d * Fintype.card (White c) ≤
        K.faceNumber 1 + 2 ^ (d - 1))
  have hsum : (Fintype.card (Black c) : ℝ) + Fintype.card (White c) = K.faceNumber 0 := by
    rw [K.faceNumber_zero]
    exact_mod_cast Cubical.Bipartite.card_vertices c
  have h := Cubical.Counting.strengthened_of_asymmetric (d : ℝ)
    (Fintype.card (Black c)) (Fintype.card (White c)) (K.faceNumber 1)
    (2 ^ (d - 1)) (by exact_mod_cast (by omega : 1 ≤ d)) hb hw
  rwa [hsum] at h

/-- The sphere hypothesis alone supplies a colouring and the strengthened
bound for every colouring; the assertion is nonvacuous. -/
theorem cubical_pl_lower_bound (d : ℕ) (hd : 4 ≤ d) (hK : K.IsSphere (d - 1)) :
    Nonempty (K.graph.Coloring Bool) ∧
    ∀ c : K.graph.Coloring Bool,
      ((d : ℝ) + 1) / 2 * K.faceNumber 0 - 2 ^ (d - 1) +
        ((d : ℝ) - 1) / 2 *
          |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ K.faceNumber 1 :=
  ⟨K.exists_coloring hK (by omega), K.strengthened_edge_bound d hd hK⟩

end Cubical.PL.CubeComplex
