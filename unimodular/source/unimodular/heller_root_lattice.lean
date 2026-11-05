module

public import Unimodular.Extensions
public import Unimodular.GraphicUniformity

@[expose] public section

noncomputable section

namespace Unimodular.Heller.TypeA

open scoped BigOperators

/-- The summation map defining the paper's type-A root lattice. -/
def sumMap (n : ℕ) : Lattice (n + 1) →ₗ[ℤ] ℤ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

/-- Exactly the integral zero-sum lattice in ℤ^(n+1), not a replacement lattice. -/
abbrev RootLattice (n : ℕ) := LinearMap.ker (sumMap n)

/-- A vertex index for the rooted incidence convention used in the formalization. -/
def vertexIndex {n : ℕ} : Option (Fin n) → Fin (n + 1)
  | none => 0
  | some i => i.succ

/-- The usual root eᵢ-eⱼ, as an element of the actual zero-sum lattice. -/
def root {n : ℕ} (i j : Fin (n + 1)) : RootLattice n :=
  ⟨Pi.single i 1 - Pi.single j 1, by
    change (∑ k : Fin (n + 1), ((Pi.single i 1 : Lattice (n + 1)) k -
      (Pi.single j 1 : Lattice (n + 1)) k)) = 0
    simp [Finset.sum_sub_distrib]⟩

/-- Full type-A root set, with the unequal-index condition in the paper. -/
def roots (n : ℕ) : Set (RootLattice n) :=
  {u | ∃ i j : Fin (n + 1), i ≠ j ∧ u = root i j}

/-- Standard integral coordinates for the zero-sum lattice. The inverse discards
the zeroth coordinate; its value is recovered from the zero-sum equation. -/
def coordinateEquiv (n : ℕ) : Lattice n ≃ₗ[ℤ] RootLattice n where
  toFun x := ⟨Fin.cons (-(∑ i, x i)) x, by
    change (∑ i, Fin.cons (-(∑ j, x j)) x i) = 0
    rw [Fin.sum_univ_succ]
    simp⟩
  invFun x := fun i => x.val i.succ
  left_inv x := by ext i; rfl
  right_inv x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h := x.property
      change (∑ k, x.val k) = 0 at h
      rw [Fin.sum_univ_succ] at h
      change -(∑ k : Fin n, x.val k.succ) = x.val 0
      omega
    · rfl
  map_add' x y := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.mul_sum, mul_neg]
    · rfl

@[simp] theorem coordinateEquiv_tail {n : ℕ} (x : Lattice n) (i : Fin n) :
    (coordinateEquiv n x).val i.succ = x i := rfl

@[simp] theorem coordinateEquiv_zero_coordinate {n : ℕ} (x : Lattice n) :
    (coordinateEquiv n x).val 0 = -(∑ i, x i) := rfl

/-- The basis vector maps to the corresponding difference from the root vertex. -/
theorem coordinateEquiv_basis {n : ℕ} (i : Fin n) :
    coordinateEquiv n ((Pi.basisFun ℤ (Fin n)) i) = root i.succ 0 := by
  apply Subtype.ext
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [coordinateEquiv, root, Pi.basisFun_apply, Pi.single_apply, Fin.succ_ne_zero]
  · simp [coordinateEquiv, root, Pi.basisFun_apply, Pi.single_apply,
      Fin.succ_ne_zero, Fin.succ_inj]

theorem coordinateEquiv_vertex {n : ℕ} (p : Option (Fin n)) :
    coordinateEquiv n (Graphic.vertex (Pi.basisFun ℤ (Fin n)) p) = root (vertexIndex p) 0 := by
  cases p with
  | none =>
    apply Subtype.ext
    simp [Graphic.vertex, vertexIndex, root]
  | some i => exact coordinateEquiv_basis i

/-- Exact identification of the rooted incidence differences with the paper's
roots. The zero coordinate and its negative sign are part of the checked map. -/
theorem coordinateEquiv_difference {n : ℕ} (p q : Option (Fin n)) :
    coordinateEquiv n (Graphic.vertex (Pi.basisFun ℤ (Fin n)) p -
      Graphic.vertex (Pi.basisFun ℤ (Fin n)) q) = root (vertexIndex p) (vertexIndex q) := by
  rw [map_sub, coordinateEquiv_vertex, coordinateEquiv_vertex]
  apply Subtype.ext
  change (Pi.single (vertexIndex p) 1 - Pi.single 0 1) -
    (Pi.single (vertexIndex q) 1 - Pi.single 0 1) =
    Pi.single (vertexIndex p) 1 - Pi.single (vertexIndex q) 1
  abel

/-- Basis-normalized root coordinates are related by an actual lattice isomorphism. -/
def basisEquiv {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Lattice n ≃ₗ[ℤ] RootLattice n :=
  (b.equiv (Pi.basisFun ℤ (Fin n)) (Equiv.refl _)).trans (coordinateEquiv n)

theorem basisEquiv_difference {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (p q : Option (Fin n)) :
    basisEquiv b (Graphic.vertex b p - Graphic.vertex b q) =
      root (vertexIndex p) (vertexIndex q) := by
  have hv (p : Option (Fin n)) :
      b.equiv (Pi.basisFun ℤ (Fin n)) (Equiv.refl _) (Graphic.vertex b p) =
        Graphic.vertex (Pi.basisFun ℤ (Fin n)) p := by
    cases p <;> simp [Graphic.vertex]
  change coordinateEquiv n
    (b.equiv (Pi.basisFun ℤ (Fin n)) (Equiv.refl _) (Graphic.vertex b p - Graphic.vertex b q)) = _
  rw [map_sub, hv, hv]
  exact coordinateEquiv_difference p q

theorem vertexIndex_bijective {n : ℕ} : Function.Bijective (@vertexIndex n) := by
  constructor
  · intro p q h
    cases p with
    | none => cases q with
      | none => rfl
      | some j => exact False.elim ((Fin.succ_ne_zero j) h.symm)
    | some i => cases q with
      | none => exact False.elim ((Fin.succ_ne_zero i) h)
      | some j => exact congrArg some (Fin.succ_inj.1 h)
  · intro i
    refine Fin.cases ⟨none,rfl⟩ (fun j => ⟨some j,rfl⟩) i

/-- The exact set-image statement justifying the equivalent root presentation. -/
theorem basisEquiv_image_roots {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    basisEquiv b '' {u | ∃ p q : Option (Fin n), p ≠ q ∧
      u = Graphic.vertex b p - Graphic.vertex b q} = roots n := by
  ext u
  constructor
  · rintro ⟨x, ⟨p,q,hpq,rfl⟩, rfl⟩
    exact ⟨vertexIndex p, vertexIndex q, fun he => hpq (vertexIndex_bijective.1 he),
      basisEquiv_difference b p q⟩
  · rintro ⟨i,j,hij,rfl⟩
    obtain ⟨p,rfl⟩ := vertexIndex_bijective.2 i
    obtain ⟨q,rfl⟩ := vertexIndex_bijective.2 j
    refine ⟨Graphic.vertex b p - Graphic.vertex b q, ?_, basisEquiv_difference b p q⟩
    exact ⟨p,q,fun he => hij (congrArg vertexIndex he),rfl⟩


/-- Distinct ordered endpoint pairs define distinct roots in the actual lattice. -/
theorem root_eq_imp {n : ℕ} {i j k l : Fin (n + 1)} (hij : i ≠ j) (hkl : k ≠ l)
    (h : root i j = root k l) : i = k ∧ j = l := by
  have hfirst : i = k := by
    by_contra hik
    have hv := congrFun (congrArg Subtype.val h) i
    by_cases hli : l = i <;>
      simp [root, Pi.single_apply, hij, Ne.symm hij, hik, Ne.symm hik, hli] at hv
  subst k
  refine ⟨rfl, ?_⟩
  by_contra hjl
  have hv := congrFun (congrArg Subtype.val h) j
  simp [root, Pi.single_apply, hij, Ne.symm hij, hjl, Ne.symm hjl] at hv

/-- Finite presentation of exactly all nonzero roots. -/
def rootFinset (n : ℕ) : Finset (RootLattice n) :=
  (Finset.univ : Finset (Fin (n + 1))).offDiag.image (fun p => root p.1 p.2)

@[simp] theorem coe_rootFinset (n : ℕ) : (rootFinset n : Set (RootLattice n)) = roots n := by
  ext u
  simp [rootFinset, roots, Finset.mem_offDiag, eq_comm]

/-- Exact cardinality of the full root system, including every orientation. -/
theorem rootFinset_card (n : ℕ) : (rootFinset n).card = n * (n + 1) := by
  have hinj : Set.InjOn (fun p : Fin (n + 1) × Fin (n + 1) => root p.1 p.2)
      ((Finset.univ : Finset (Fin (n + 1))).offDiag : Set _) := by
    intro p hp q hq he
    have hp' := (Finset.mem_offDiag.1 hp).2.2
    have hq' := (Finset.mem_offDiag.1 hq).2.2
    have h := root_eq_imp hp' hq' he
    exact Prod.ext h.1 h.2
  rw [rootFinset, Finset.card_image_of_injOn hinj, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  calc
    (n + 1) * (n + 1) - (n + 1) = ((n + 1) * n + (n + 1)) - (n + 1) := by ring_nf
    _ = (n + 1) * n := Nat.add_sub_cancel _ _
    _ = n * (n + 1) := Nat.mul_comm _ _

theorem roots_ncard (n : ℕ) : (roots n).ncard = n * (n + 1) := by
  rw [← coe_rootFinset, Set.ncard_coe_finset, rootFinset_card]

end Unimodular.Heller.TypeA

end
