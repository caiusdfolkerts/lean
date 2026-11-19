module

public import Unimodular.SeriesParallelPrograms
public import Unimodular.TriangleExtension
public import Unimodular.GraphicUniformity

@[expose] public section

/-!
# Actual network interpretation of the construction programs

Vertices and endpoints are explicit. Parallel extension repeats an edge, and
series extension subdivides an edge through a fresh vertex. An actual integral
basis identifies every program column with the corresponding directed incidence
vector. This supplies a mathematical graph realization, not just a name for the
program class.
-/

namespace Unimodular.SeriesParallel

noncomputable section

/-- A finite directed rooted multigraph, allowing loops and parallel edges. -/
structure RootedNetwork (n m : ℕ) where
  source : Fin m → Option (Fin n)
  target : Fin m → Option (Fin n)

/-- Include the old vertices after adjoining a new first vertex. -/
def liftVertex {n : ℕ} : Option (Fin n) → Option (Fin (n + 1)) := Option.map Fin.succ

namespace RootedNetwork

/-- The empty network on its root vertex. -/
def empty : RootedNetwork 0 0 := ⟨Fin.elim0, Fin.elim0⟩

/-- Adjoin a loop and one unused vertex (the latter only pads coordinates). -/
def addLoop {n m : ℕ} (G : RootedNetwork n m) : RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons none (liftVertex ∘ G.source)
  target := Fin.cons none (liftVertex ∘ G.target)

/-- Adjoin a bridge from a new vertex to the root, a singleton direct summand
of the cycle matroid. -/
def addBridge {n m : ℕ} (G : RootedNetwork n m) : RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons (some 0) (liftVertex ∘ G.source)
  target := Fin.cons none (liftVertex ∘ G.target)

/-- Repeat precisely the selected edge. -/
def parallel {n m : ℕ} (G : RootedNetwork n m) (e : Fin m) :
    RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons (liftVertex (G.source e)) (liftVertex ∘ G.source)
  target := Fin.cons (liftVertex (G.target e)) (liftVertex ∘ G.target)

/-- Subdivide precisely the selected edge through the new vertex. The new edge
runs from its old source to the new vertex; the retained selected label runs
from the new vertex to its old target. -/
def subdivide {n m : ℕ} (G : RootedNetwork n m) (e : Fin m) :
    RootedNetwork (n + 1) (m + 1) where
  source := Fin.cons (liftVertex (G.source e))
    (fun j => if j = e then some 0 else liftVertex (G.source j))
  target := Fin.cons (some 0) (liftVertex ∘ G.target)

/-- Relabel the edge set, retaining the actual graph and all its incidences. -/
def relabel {n m : ℕ} (G : RootedNetwork n m) (e : Equiv.Perm (Fin m)) :
    RootedNetwork n m := ⟨G.source ∘ e, G.target ∘ e⟩

/-- The ordinary constructive network operations, on explicit graph endpoints.
The unused vertex in a loop or parallel step has no effect on its cycle matroid. -/
inductive HasSeriesParallelConstruction : {m : ℕ} → RootedNetwork m m → Prop
  | empty : HasSeriesParallelConstruction empty
  | addLoop {m : ℕ} {G : RootedNetwork m m} : HasSeriesParallelConstruction G →
      HasSeriesParallelConstruction G.addLoop
  | addBridge {m : ℕ} {G : RootedNetwork m m} : HasSeriesParallelConstruction G →
      HasSeriesParallelConstruction G.addBridge
  | parallel {m : ℕ} {G : RootedNetwork m m} : HasSeriesParallelConstruction G →
      (e : Fin m) → HasSeriesParallelConstruction (G.parallel e)
  | subdivide {m : ℕ} {G : RootedNetwork m m} : HasSeriesParallelConstruction G →
      (e : Fin m) → HasSeriesParallelConstruction (G.subdivide e)
  | relabel {m : ℕ} {G : RootedNetwork m m} : HasSeriesParallelConstruction G →
      (e : Equiv.Perm (Fin m)) → HasSeriesParallelConstruction (G.relabel e)

end RootedNetwork

namespace SPProgram

/-- The literal rooted graph built by the program. -/
def network : {m : ℕ} → SPProgram m → RootedNetwork m m
  | _, .empty => .empty
  | _, .addLoop P => P.network.addLoop
  | _, .addColoop P => P.network.addBridge
  | _, .parallel P e => P.network.parallel e
  | _, .series P e => P.network.subdivide e
  | _, .relabel P e => P.network.relabel e

theorem network_hasConstruction {m : ℕ} (P : SPProgram m) :
    P.network.HasSeriesParallelConstruction := by
  induction P with
  | empty => exact .empty
  | addLoop P ih => exact .addLoop ih
  | addColoop P ih => exact .addBridge ih
  | parallel P e ih => exact .parallel ih e
  | series P e ih => exact .subdivide ih e
  | relabel P e ih => exact .relabel ih e

/-- The integral basis changes with subdivision: the new basis vector is
`(1, old source)`. This is the exact integral shear needed for directed incidence. -/
def networkBasis : {m : ℕ} → SPProgram m → Module.Basis (Fin m) ℤ (Lattice m)
  | _, .empty => Pi.basisFun ℤ (Fin 0)
  | _, .addLoop P => TriangleExtension.basis P.networkBasis 0 true
  | _, .addColoop P => TriangleExtension.basis P.networkBasis 0 true
  | _, .parallel P _ => TriangleExtension.basis P.networkBasis 0 true
  | _, .series P e => TriangleExtension.basis P.networkBasis
      (Graphic.vertex P.networkBasis (P.network.source e)) true
  | _, .relabel P _ => P.networkBasis

private lemma vertex_lift {m : ℕ} (b : Module.Basis (Fin m) ℤ (Lattice m))
    (u : Lattice m) (v : Option (Fin m)) :
    Graphic.vertex (TriangleExtension.basis b u true) (liftVertex v) =
      liftColumn (Graphic.vertex b v) := by
  cases v with
  | none =>
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [Graphic.vertex, liftVertex, liftColumn]
  | some i =>
    simp [Graphic.vertex, liftVertex, TriangleExtension.basis_succ,
      TriangleExtension.lift, liftColumn]

private lemma lift_sub {m : ℕ} (x y : Lattice m) :
    liftColumn (x - y) = liftColumn x - liftColumn y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftColumn]

/-- Every column, with its actual sign, is an incidence vector in an actual
integral basis. No regular-orientation-uniqueness theorem is assumed. -/
theorem columns_eq_incidence {m : ℕ} (P : SPProgram m) :
    ∀ j, P.columns j =
      Graphic.vertex P.networkBasis (P.network.source j) -
        Graphic.vertex P.networkBasis (P.network.target j) := by
  induction P with
  | empty => intro j; exact Fin.elim0 j
  | addLoop P ih =>
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [columns, network, RootedNetwork.addLoop, Graphic.vertex]
    · change liftColumn (P.columns j) =
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.source j)) -
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.target j))
      rw [vertex_lift, vertex_lift, ← lift_sub, ih]
  | addColoop P ih =>
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [columns, network, networkBasis, RootedNetwork.addBridge,
        Graphic.vertex, TriangleExtension.newRay, newColumn]
    · change liftColumn (P.columns j) =
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.source j)) -
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.target j))
      rw [vertex_lift, vertex_lift, ← lift_sub, ih]
  | parallel P e ih =>
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change liftColumn (P.columns e) =
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.source e)) -
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.target e))
      rw [vertex_lift, vertex_lift, ← lift_sub, ih]
    · change liftColumn (P.columns j) =
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.source j)) -
        Graphic.vertex (TriangleExtension.basis P.networkBasis 0 true)
          (liftVertex (P.network.target j))
      rw [vertex_lift, vertex_lift, ← lift_sub, ih]
  | series P e ih =>
    let s := Graphic.vertex P.networkBasis (P.network.source e)
    let t := Graphic.vertex P.networkBasis (P.network.target e)
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · change Fin.cons (-1) 0 =
        Graphic.vertex (TriangleExtension.basis P.networkBasis s true)
          (liftVertex (P.network.source e)) -
        Graphic.vertex (TriangleExtension.basis P.networkBasis s true) (some 0)
      rw [vertex_lift]
      simp only [Graphic.vertex, TriangleExtension.basis_zero, TriangleExtension.newRay,
        if_true]
      ext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [liftColumn, s, Graphic.vertex]
    · by_cases hje : j = e
      · subst j
        simp only [columns_series_selected, network, RootedNetwork.subdivide,
          Fin.cons_succ, if_pos rfl]
        change Fin.cons 1 (P.columns e) =
          Graphic.vertex (TriangleExtension.basis P.networkBasis s true) (some 0) -
          Graphic.vertex (TriangleExtension.basis P.networkBasis s true)
            (liftVertex (P.network.target e))
        rw [vertex_lift]
        simp only [Graphic.vertex, TriangleExtension.basis_zero, TriangleExtension.newRay,
          if_true]
        rw [ih e]
        ext i
        refine Fin.cases ?_ (fun k => ?_) i <;> simp [liftColumn, s, Graphic.vertex]
      · change (if j = e then Fin.cons 1 (P.columns e) else liftColumn (P.columns j)) =
          Graphic.vertex (TriangleExtension.basis P.networkBasis s true)
            (if j = e then some 0 else liftVertex (P.network.source j)) -
          Graphic.vertex (TriangleExtension.basis P.networkBasis s true)
            (liftVertex (P.network.target j))
        rw [if_neg hje, if_neg hje, vertex_lift, vertex_lift, ← lift_sub, ih]
  | relabel P e ih =>
    intro j
    exact ih (e j)

/-- The resulting actual directed incidence configuration has all maximal
minors in `{−1,0,1}` in every dimension. -/
theorem columns_uniform {m : ℕ} (P : SPProgram m) :
    IntegralRigidity.Uniform P.networkBasis P.columns := by
  have he := funext P.columns_eq_incidence
  rw [he]
  exact Graphic.incidence_uniform P.networkBasis P.network.source P.network.target

end SPProgram

#print axioms Unimodular.SeriesParallel.SPProgram.columns_eq_incidence
#print axioms Unimodular.SeriesParallel.SPProgram.columns_uniform

end
end Unimodular.SeriesParallel
