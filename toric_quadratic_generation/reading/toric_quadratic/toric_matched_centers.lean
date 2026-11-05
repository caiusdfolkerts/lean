module
public import PaperVerification.ToricNormalFan
@[expose] public section
/-!
# Matched unit boxes for actual smooth lattice polytopes

This is the geometric center construction in Lemma 4.2, obtained from the literal
smoothness, edge-length, and common-normal-fan assumptions. Every interior lattice
point is proved to lie in the convex hull of the matched center sums. The lattice
point selection from those boxes is supplied by the independent basis-box covering
argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

namespace LatticePolytope

/-- Full matched-center geometry for the actual polytopes, with no additional
normal-fan or shifted-polytope hypothesis. The indexing set consists of the
actual vertices of `P`; all integral edge bases are allowed to differ. -/
theorem matched_unit_box_centers {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hlP : P.EdgesAtLeast n) (hlQ : Q.EdgesAtLeast n) :
    ∃ (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℤ (Lattice n))
      (a c : P.carrier.extremePoints ℝ → Ambient n),
      (∀ j (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
        a j + ∑ i, t i • integralBasisReal (b j) i ∈ P.carrier) ∧
      (∀ j (t : Fin n → ℝ), (∀ i, |t i| ≤ 1 / 2) →
        c j + ∑ i, t i • integralBasisReal (b j) i ∈ Q.carrier) ∧
      ∀ m : Lattice n, embed n m ∈ interior (P.minkowskiSum Q) →
        embed n m ∈ convexHull ℝ (Set.range fun j => a j + c j) := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  have hdata (j : J) := P.sameNormalFan_matched_bases Q hP hQ hfan j j.property
  choose w vZ wZ b p q hw hvZ hwZ hcones hp hq hPcone hQcone using hdata
  let u : J × Fin n → Ambient n →ₗ[ℝ] ℝ :=
    fun i => (integralBasisReal (b i.1)).coord i.2
  let ap : J × Fin n → ℤ := fun i => (b i.1).repr (vZ i.1) i.2
  let aq : J × Fin n → ℤ := fun i => (b i.1).repr (wZ i.1) i.2
  let active : J → Fin n → J × Fin n := fun j i => (j, i)
  let a : J → Ambient n := fun j => cornerCenter (j : Ambient n) (integralBasisReal (b j))
  let c : J → Ambient n := fun j => cornerCenter (w j) (integralBasisReal (b j))
  have hdual (j : J) (i : Fin n) (x : Ambient n) :
      u (active j i) x = (integralBasisReal (b j)).repr x i := rfl
  have hactiveP (j : J) (i : Fin n) : u (active j i) j = (ap (active j i) : ℝ) := by
    change (integralBasisReal (b j)).repr (j : Ambient n) i = _
    rw [← hvZ j, integralBasisReal_repr]
  have hactiveQ (j : J) (i : Fin n) : u (active j i) (w j) = (aq (active j i) : ℝ) := by
    change (integralBasisReal (b j)).repr (w j) i = _
    rw [← hwZ j, integralBasisReal_repr]
  have hsupportP (x : Ambient n) (hx : x ∈ P.carrier) :
      x ∈ normalHalfspaces u (fun i => (ap i : ℝ)) := by
    rintro ⟨j, i⟩
    have h := hPcone j x hx i
    rw [map_sub, Finsupp.sub_apply] at h
    change (ap (j, i) : ℝ) ≤ (integralBasisReal (b j)).repr x i
    rw [← hactiveP j i]
    exact sub_nonneg.mp h
  have hsupportQ (x : Ambient n) (hx : x ∈ Q.carrier) :
      x ∈ normalHalfspaces u (fun i => (aq i : ℝ)) := by
    rintro ⟨j, i⟩
    have h := hQcone j x hx i
    rw [map_sub, Finsupp.sub_apply] at h
    change (aq (j, i) : ℝ) ≤ (integralBasisReal (b j)).repr x i
    rw [← hactiveQ j i]
    exact sub_nonneg.mp h
  have hunitP (j : J) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
      (j : Ambient n) + ∑ i, t i • integralBasisReal (b j) i ∈ P.carrier := by
    have hv : embed n (vZ j) ∈ P.carrier := by rw [hvZ]; exact j.property.1
    have h := P.integral_edges_unit_corner_box hlP (vZ j) hv (b j) (p j)
      (fun i => by simpa only [hvZ] using (hp j i).2) t ht
    simpa only [hvZ] using h
  have hunitQ (j : J) (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
      w j + ∑ i, t i • integralBasisReal (b j) i ∈ Q.carrier := by
    have hv : embed n (wZ j) ∈ Q.carrier := by rw [hwZ]; exact (hw j).1
    have h := Q.integral_edges_unit_corner_box hlQ (wZ j) hv (b j) (q j)
      (fun i => by simpa only [hwZ] using (hq j i).2) t ht
    simpa only [hwZ] using h
  have hu (i : J × Fin n) : u i ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Ambient n →ₗ[ℝ] ℝ => f (integralBasisReal (b i.1) i.2)) hz
    simpa [u, Module.Basis.coord_apply] using h
  have hint (i : J × Fin n) (j : J) (k : Fin n) :
      ∃ z : ℤ, (z : ℝ) = u i (integralBasisReal (b j) k) := by
    refine ⟨(b i.1).repr (b j k) i.2, ?_⟩
    simp [u, Module.Basis.coord_apply]
  have hcomplete (f : Ambient n →ₗ[ℝ] ℝ) :
      ∃ j : J, ∀ i, 0 ≤ f (integralBasisReal (b j) i) :=
    P.smooth_basis_cones_complete b vZ p hvZ hp f
  have hac (j : J) : a j ∈ normalHalfspaces u (fun i => (ap i : ℝ) + 1 / 2) :=
    integral_cornerCenter_feasible u (fun i => (ap i : ℝ)) j
      (integralBasisReal (b j)) hu (fun i k => hint i j k)
      (fun t ht => hsupportP _ (hunitP j t ht))
  have hcc (j : J) : c j ∈ normalHalfspaces u (fun i => (aq i : ℝ) + 1 / 2) :=
    integral_cornerCenter_feasible u (fun i => (aq i : ℝ)) (w j)
      (integralBasisReal (b j)) hu (fun i k => hint i j k)
      (fun t ht => hsupportQ _ (hunitQ j t ht))
  have hacactive (j : J) (i : Fin n) :
      u (active j i) (a j) = (ap (active j i) : ℝ) + 1 / 2 := by
    change u (active j i) (cornerCenter j (integralBasisReal (b j))) = _
    rw [cornerCenter_dual_coordinate _ _ _ i (hdual j i), hactiveP]
  have hccactive (j : J) (i : Fin n) :
      u (active j i) (c j) = (aq (active j i) : ℝ) + 1 / 2 := by
    change u (active j i) (cornerCenter (w j) (integralBasisReal (b j))) = _
    rw [cornerCenter_dual_coordinate _ _ _ i (hdual j i), hactiveQ]
  have hcenters := matched_centers_convexHull u
    (fun i => (ap i : ℝ) + 1 / 2) (fun i => (aq i : ℝ) + 1 / 2)
    (fun j => integralBasisReal (b j)) active a c hdual hcomplete hacactive hccactive hac hcc
  refine ⟨b, a, c, ?_, ?_, ?_⟩
  · intro j t ht
    exact cornerCenter_box_mem P.carrier j (integralBasisReal (b j)) (hunitP j) t ht
  · intro j t ht
    exact cornerCenter_box_mem Q.carrier (w j) (integralBasisReal (b j)) (hunitQ j) t ht
  · intro m hm
    have hsumsubset : P.minkowskiSum Q ⊆
        normalHalfspaces u (fun i => ((ap i + aq i : ℤ) : ℝ)) := by
      rintro _ ⟨x, hx, y, hy, rfl⟩ i
      have hp' := hsupportP x hx i
      have hq' := hsupportQ y hy i
      simpa only [map_add, Int.cast_add] using add_le_add hp' hq'
    have hmint := interior_mono hsumsubset hm
    have huinteger (i : J × Fin n) (z : Lattice n) :
        ∃ k : ℤ, u i (embed n z) = k :=
      ⟨(b i.1).repr z i.2, integralBasisReal_repr (b i.1) z i.2⟩
    have hslack := integral_support_of_interior u (fun i => ap i + aq i)
      huinteger hu m hmint
    rw [← hcenters]
    intro i
    have h := hslack i
    push_cast at h
    linarith

end LatticePolytope

end PaperVerification.ToricGeometry
