module

public import Unimodular.TriangleCones

@[expose] public section

noncomputable section

namespace Unimodular

attribute [local instance] Classical.propDecidable

/-- A Boolean labeling of the actual ray vectors and maximal bases.  Every choice of
one ray from each opposite facet pair occurs, and these are all maximal bases. -/
structure CubicalFan {n : ℕ} (fan : SmoothCompleteFan n) where
  ray : Fin n → Bool → Lattice n
  ray_injective : Function.Injective (fun p : Fin n × Bool => ray p.1 p.2)
  basis : (Fin n → Bool) → Module.Basis (Fin n) ℤ (Lattice n)
  basis_mem : ∀ ε, basis ε ∈ fan.maximal
  maximal_surj : ∀ b ∈ fan.maximal, ∃ ε, basis ε = b
  basis_vectors : ∀ ε i, basis ε i = ray i (ε i)

namespace CubicalFan

variable {n : ℕ} {fan : SmoothCompleteFan n} (C : CubicalFan fan)

theorem ray_mem (i : Fin n) (s : Bool) : C.ray i s ∈ fan.rays :=
  ⟨C.basis (fun _ => s), C.basis_mem _, i, C.basis_vectors _ _⟩

theorem rays_eq : fan.rays = Set.range (fun p : Fin n × Bool => C.ray p.1 p.2) := by
  ext u
  constructor
  · rintro ⟨b, hb, i, rfl⟩
    obtain ⟨ε, rfl⟩ := C.maximal_surj b hb
    exact ⟨(i, ε i), (C.basis_vectors ε i).symm⟩
  · rintro ⟨⟨i, s⟩, rfl⟩
    exact C.ray_mem i s

def extend (u : Lattice n) : CubicalFan (TriangleExtension.fan fan u) where
  ray i s := Fin.cases (TriangleExtension.newRay u s)
    (fun j => TriangleExtension.lift (C.ray j s)) i
  ray_injective := by
    rintro ⟨i, s⟩ ⟨j, t⟩ he
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        have hh := congrFun he 0
        have hst : s = t := by
          cases s <;> cases t <;>
            simp [TriangleExtension.newRay] at hh ⊢
        exact Prod.ext rfl hst
      | succ j =>
        have hh := congrFun he 0
        cases s <;> simp [TriangleExtension.newRay, TriangleExtension.lift] at hh
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have hh := congrFun he 0
        cases t <;> simp [TriangleExtension.newRay, TriangleExtension.lift] at hh
      | succ j =>
        have h : (i, s) = (j, t) :=
          C.ray_injective (TriangleExtension.lift_injective he)
        exact Prod.ext (congrArg Fin.succ (congrArg (fun p : Fin n × Bool => p.1) h))
          (congrArg (fun p : Fin n × Bool => p.2) h)
  basis ε := TriangleExtension.basis (C.basis (Fin.tail ε)) u (ε 0)
  basis_mem ε := (TriangleExtension.mem_maximal fan u _).2
    ⟨C.basis (Fin.tail ε), C.basis_mem _, ε 0, rfl⟩
  maximal_surj b hb := by
    obtain ⟨b', hb', s, rfl⟩ := (TriangleExtension.mem_maximal fan u b).1 hb
    obtain ⟨ε, rfl⟩ := C.maximal_surj b' hb'
    exact ⟨Fin.cons s ε, by simp⟩
  basis_vectors ε i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [C.basis_vectors, Fin.tail]

def zero : CubicalFan TriangleExtension.zeroFan where
  ray i := Fin.elim0 i
  ray_injective := by rintro ⟨i, s⟩; exact Fin.elim0 i
  basis _ := Pi.basisFun ℤ (Fin 0)
  basis_mem _ := by simp [TriangleExtension.zeroFan]
  maximal_surj b hb := by
    have hb' : b = Pi.basisFun ℤ (Fin 0) := by simpa [TriangleExtension.zeroFan] using hb
    exact ⟨Fin.elim0, hb'.symm⟩
  basis_vectors _ i := Fin.elim0 i

/-- The actual polar vertices have the Boolean vertex/facet incidence of a cube. -/
theorem polar_incidence (hfan : fan.PositiveCoordinateCriterion)
    (ε : Fin n → Bool) (i : Fin n) (s : Bool) :
    pairing (embed (latticeDualVertex (C.basis ε))) (C.ray i s) = 1 ↔ ε i = s := by
  rw [embed_latticeDualVertex]
  rw [(fan.strict_support_at_basis hfan (C.basis ε) (C.basis_mem ε)
    (C.ray i s) (C.ray_mem i s)).2]
  constructor
  · rintro ⟨j, hj⟩
    rw [C.basis_vectors] at hj
    have he : (j, ε j) = (i, s) := C.ray_injective hj
    have hji : j = i := congrArg (fun p : Fin n × Bool => p.1) he
    subst j
    exact congrArg Prod.snd he
  · intro he
    exact ⟨i, by rw [C.basis_vectors, he]⟩

theorem polar_vertices_surj (v : Lattice n)
    (hv : v ∈ fan.dualVertices) : ∃ ε, latticeDualVertex (C.basis ε) = v := by
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨ε, rfl⟩ := C.maximal_surj b hb
  exact ⟨ε, rfl⟩

theorem polar_vertices_injective (hfan : fan.PositiveCoordinateCriterion) :
    Function.Injective (fun ε => latticeDualVertex (C.basis ε)) := by
  intro ε δ he
  change latticeDualVertex (C.basis ε) = latticeDualVertex (C.basis δ) at he
  ext i
  symm
  apply (C.polar_incidence hfan δ i (ε i)).1
  rw [← he]
  exact (C.polar_incidence hfan ε i (ε i)).2 rfl

include C

/-- Exact vertex count, using injectivity supplied by strict support. -/
theorem polar_vertices_card (hfan : fan.PositiveCoordinateCriterion) :
    (fan.polarPresentation hfan).vertices.card = 2 ^ n := by
  have he : fan.dualVertices =
      Finset.univ.image (fun ε : Fin n → Bool => latticeDualVertex (C.basis ε)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨ε, rfl⟩ := C.polar_vertices_surj v hv
      exact Finset.mem_image.2 ⟨ε, Finset.mem_univ _, rfl⟩
    · rintro hv
      obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 hv
      exact Finset.mem_image.2 ⟨C.basis ε, C.basis_mem ε, rfl⟩
  change fan.dualVertices.card = _
  rw [he, Finset.card_image_of_injective _ (C.polar_vertices_injective hfan)]
  simp

/-- Exact primitive-normal count, using distinct ray vectors rather than labels. -/
theorem polar_normals_card (hfan : fan.PositiveCoordinateCriterion) :
    (fan.polarPresentation hfan).normals.card = 2 * n := by
  have he : fan.rayFinset =
      Finset.univ.image (fun p : Fin n × Bool => C.ray p.1 p.2) := by
    ext u
    rw [fan.mem_rayFinset, C.rays_eq]
    simp
  change fan.rayFinset.card = _
  rw [he, Finset.card_image_of_injective _ C.ray_injective]
  simp [Nat.mul_comm]

end CubicalFan

/-- The ordinary coordinate cube fan, built as repeated products with the line fan. -/
def coordinateCubeFan : (n : ℕ) → SmoothCompleteFan n
  | 0 => TriangleExtension.zeroFan
  | n + 1 => TriangleExtension.fan (coordinateCubeFan n) 0

def coordinateCubeFan_cubical : (n : ℕ) → CubicalFan (coordinateCubeFan n)
  | 0 => CubicalFan.zero
  | n + 1 => (coordinateCubeFan_cubical n).extend 0

theorem coordinateCubeFan_criterion : ∀ n, (coordinateCubeFan n).PositiveCoordinateCriterion
  | 0 => TriangleExtension.zeroFan_positiveCriterion
  | n + 1 => TriangleExtension.positiveCriterion_of_bound (coordinateCubeFan n) 0
      (by intro b hb; simp) (coordinateCubeFan_criterion n)

theorem coordinateCubeFan_ray : ∀ n (i : Fin n) (s : Bool),
    (coordinateCubeFan_cubical n).ray i s =
      (if s then Pi.single i 1 else -Pi.single i 1) := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i s
    refine Fin.cases ?_ (fun j => ?_) i
    · cases s <;> ext k <;> refine Fin.cases ?_ (fun l => ?_) k <;>
        simp [coordinateCubeFan_cubical, CubicalFan.extend, TriangleExtension.newRay,
          Pi.single_apply]
    · change TriangleExtension.lift ((coordinateCubeFan_cubical n).ray j s) = _
      rw [ih]
      cases s <;> ext k <;> refine Fin.cases ?_ (fun l => ?_) k <;>
        simp [TriangleExtension.lift, Pi.single_apply]

def coordinateCubePresentation (n : ℕ) : SmoothReflexivePresentation n :=
  (coordinateCubeFan n).polarPresentation (coordinateCubeFan_criterion n)

theorem coordinateCubePresentation_carrier (n : ℕ) :
    (coordinateCubePresentation n).carrier =
      {x : Ambient n | ∀ i, -1 ≤ x i ∧ x i ≤ 1} := by
  ext x
  rw [(coordinateCubePresentation n).mem_carrier_iff]
  change (∀ u ∈ (coordinateCubeFan n).rayFinset, pairing x u ≤ 1) ↔ _
  simp only [SmoothCompleteFan.mem_rayFinset,
    (coordinateCubeFan_cubical n).rays_eq, Set.mem_range]
  constructor
  · intro h i
    constructor
    · have hi := h _ ⟨(i, false), rfl⟩
      rw [coordinateCubeFan_ray] at hi
      simp [pairing, Pi.single_apply] at hi
      linarith
    · have hi := h _ ⟨(i, true), rfl⟩
      simpa [coordinateCubeFan_ray, pairing, Pi.single_apply] using hi
  · rintro h u ⟨⟨i, s⟩, rfl⟩
    rw [coordinateCubeFan_ray]
    cases s <;> simp [pairing, Pi.single_apply] <;> linarith [h i]

end Unimodular

end
