module

public import PaperVerification.PowerDegreeActions
public import PaperVerification.PowerConjugation

/-!
# The complete finite presentation of an original-family homogeneous tail

In degree `d` all operator indices `0≤k≤d` are retained, with zero blocks for
`k<m`. This is essential at singular diagonal parameters: no assertion that
the first `n` original operators generate is used. Homogeneous projection of
every generator of the full image span proves that this finite matrix presents
the actual degree quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix Representation
open scoped BigOperators

namespace PaperVerification.PowerOperators

abbrev OriginalDegreeIndex (n d : ℕ) := (k : Fin (d+1)) × ShiftedExponent n k.val d

section Ring

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem map_original (φ : R →+* S) (c : Fin n → R) (lam : R) (k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (original c lam k p) =
      original (fun i => φ (c i)) (φ lam) k (MvPolynomial.map φ p) := by
  simp only [original,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_mul,map_pow,
    map_add,map_coefficient_smul,MvPolynomial.map_X,map_euler]

theorem shiftedProjection_original (c : Fin n → R) (lam : R) (s d k : ℕ)
    (p : MvPolynomial (Fin n) R) :
    shiftedProjection s d (original c lam k p) =
      original c lam k (shiftedProjection (s+k) d p) := by
  simp only [original,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm (X i^k),shiftedProjection_mul (isHomogeneous_X_pow i k),mul_comm]
  rw [map_add,map_smul,map_smul,shiftedProjection_euler]

def originalDegreeDecode (d : ℕ) (v : OriginalDegreeIndex n d → R) :
    (k : Fin (d+1)) → MvPolynomial (Fin n) R :=
  fun k => shiftedDecode k.val d (fun a => v ⟨k,a⟩)

def originalFiniteMap (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : OriginalDegreeIndex n d → R) : MvPolynomial (Fin n) R :=
  ∑ k : Fin (d+1), if m ≤ k.val then original c lam k.val (originalDegreeDecode d v k) else 0

theorem originalFiniteMap_mem (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : OriginalDegreeIndex n d → R) :
    originalFiniteMap c lam m d v ∈ shiftedPiece R n 0 d := by
  have he : shiftedProjection 0 d (originalFiniteMap c lam m d v) = originalFiniteMap c lam m d v := by
    unfold originalFiniteMap
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · rw [shiftedProjection_original,Nat.zero_add,originalDegreeDecode,
        shiftedProjection_of_mem (shiftedDecode_mem k.val d (fun a => v ⟨k,a⟩))]
    · exact map_zero _
  rw [← he]
  exact shiftedProjection_mem _ _ _

def originalDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ) :
    Matrix (ShiftedExponent n 0 d) (OriginalDegreeIndex n d) R :=
  fun b a => if m ≤ a.1.val then (original c lam a.1.val (monomial a.2.val 1)).coeff b.val else 0

theorem originalDegreeMatrix_mulVec (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : OriginalDegreeIndex n d → R) (b : ShiftedExponent n 0 d) :
    (originalDegreeMatrix c lam m d *ᵥ v) b = (originalFiniteMap c lam m d v).coeff b.val := by
  classical
  simp only [Matrix.mulVec,dotProduct,originalDegreeMatrix,Fintype.sum_sigma,
    originalFiniteMap,originalDegreeDecode,shiftedDecode_eq_sum,coeff_sum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · simp only [map_sum,map_smul,coeff_sum,coeff_smul,smul_eq_mul,mul_comm]
  · simp only [zero_mul,Finset.sum_const_zero,MvPolynomial.coeff_zero,Finsupp.zero_apply]

theorem shiftedDecode_originalDegreeMatrix (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : OriginalDegreeIndex n d → R) :
    shiftedDecode 0 d (originalDegreeMatrix c lam m d *ᵥ v) = originalFiniteMap c lam m d v := by
  rw [show originalDegreeMatrix c lam m d *ᵥ v =
      (fun b => (originalFiniteMap c lam m d v).coeff b.val) from
    funext (originalDegreeMatrix_mulVec c lam m d v)]
  exact shiftedDecode_coeffs _ _ _ (originalFiniteMap_mem c lam m d v)

def originalDegreePolynomialMap (c : Fin n → R) (lam : R) (m d : ℕ) :
    (OriginalDegreeIndex n d → R) →ₗ[R] MvPolynomial (Fin n) R :=
  (shiftedDecode 0 d).comp (originalDegreeMatrix c lam m d).mulVecLin

@[simp] theorem originalDegreePolynomialMap_apply (c : Fin n → R) (lam : R) (m d : ℕ)
    (v : OriginalDegreeIndex n d → R) :
    originalDegreePolynomialMap c lam m d v = originalFiniteMap c lam m d v :=
  shiftedDecode_originalDegreeMatrix c lam m d v

def originalDegreeInsert (d : ℕ) (k : Fin (d+1)) (v : ShiftedExponent n k.val d → R) :
    OriginalDegreeIndex n d → R :=
  fun a => if h : a.1=k then v (h ▸ a.2) else 0

theorem originalFiniteMap_insert (c : Fin n → R) (lam : R) (m d : ℕ)
    (k : Fin (d+1)) (v : ShiftedExponent n k.val d → R) :
    originalFiniteMap c lam m d (originalDegreeInsert d k v) =
      if m ≤ k.val then original c lam k.val (shiftedDecode k.val d v) else 0 := by
  classical
  unfold originalFiniteMap
  rw [Finset.sum_eq_single k]
  · simp [originalDegreeDecode,originalDegreeInsert]
  · intro j hj hjk
    simp only [originalDegreeDecode,originalDegreeInsert,dif_neg hjk]
    change (if m ≤ j.val then original c lam j.val (shiftedDecode j.val d 0) else 0) = 0
    simp only [map_zero,ite_self]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

theorem map_originalDegreeMatrix (φ : R →+* S) (c : Fin n → R) (lam : R) (m d : ℕ) :
    (originalDegreeMatrix c lam m d).map φ =
      originalDegreeMatrix (fun i => φ (c i)) (φ lam) m d := by
  ext b a
  change φ (if m ≤ a.1.val then (original c lam a.1.val (monomial a.2.val 1)).coeff b.val
      else 0) =
    if m ≤ a.1.val then
      (original (fun i => φ (c i)) (φ lam) a.1.val (monomial a.2.val 1)).coeff b.val else 0
  split_ifs
  · rw [← coeff_map,map_original,MvPolynomial.map_monomial,map_one]
  · exact map_zero _

def originalDegreeAction (G : Subgroup (Equiv.Perm (Fin n))) (d : ℕ) :
    Representation R G (OriginalDegreeIndex n d → R) :=
  sigmaCoordinateAction fun k : Fin (d+1) => shiftedDegreeAction G k.val d

theorem originalDegreeDecode_action (G : Subgroup (Equiv.Perm (Fin n))) (d : ℕ)
    (g : G) (v : OriginalDegreeIndex n d → R) (k : Fin (d+1)) :
    originalDegreeDecode d (originalDegreeAction G d g v) k =
      MvPolynomial.rename (g : Equiv.Perm (Fin n)) (originalDegreeDecode d v k) := by
  change shiftedDecode k.val d
    (shiftedRename (g : Equiv.Perm (Fin n)) k.val d (fun a => v ⟨k,a⟩)) =
      MvPolynomial.rename (g : Equiv.Perm (Fin n))
        (shiftedDecode k.val d (fun a => v ⟨k,a⟩))
  exact shiftedDecode_shiftedRename (R := R) (n := n)
    (g : Equiv.Perm (Fin n)) k.val d (fun a => v ⟨k,a⟩)

theorem rename_original_ring (e : Equiv.Perm (Fin n)) (c : Fin n → R) (lam : R)
    (hfix : ∀ i, c (e i) = c i) (k : ℕ) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.rename e (original c lam k p) =
      original c lam k (MvPolynomial.rename e p) := by
  simp only [original,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sum,map_mul,map_pow,
    map_add,map_smul,MvPolynomial.rename_X,rename_euler]
  calc
    _ = ∑ i : Fin n, (c (e i) • (X (e i)^k * MvPolynomial.rename e p) +
        lam • (X (e i)^k * euler (e i) (MvPolynomial.rename e p))) := by
      simp only [hfix]
    _ = _ := Equiv.sum_comp e (fun i =>
      c i • (X i^k * MvPolynomial.rename e p) +
        lam • (X i^k * euler i (MvPolynomial.rename e p)))

theorem originalDegreeMatrix_intertwines (G : Subgroup (Equiv.Perm (Fin n)))
    (c : Fin n → R) (lam : R) (m d : ℕ)
    (hfix : ∀ g : G, ∀ i, c ((g : Equiv.Perm (Fin n)) i) = c i) (g : G) :
    (originalDegreeMatrix c lam m d).mulVecLin.comp (originalDegreeAction G d g) =
      (shiftedDegreeAction G 0 d g).comp (originalDegreeMatrix c lam m d).mulVecLin := by
  apply LinearMap.ext
  intro v
  apply shiftedDecode_injective 0 d
  change shiftedDecode 0 d
      (originalDegreeMatrix c lam m d *ᵥ (originalDegreeAction G d g v)) =
    shiftedDecode 0 d (shiftedRename (g : Equiv.Perm (Fin n)) 0 d
      (originalDegreeMatrix c lam m d *ᵥ v))
  rw [shiftedDecode_originalDegreeMatrix,shiftedDecode_shiftedRename,
    shiftedDecode_originalDegreeMatrix]
  simp only [originalFiniteMap,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [originalDegreeDecode_action,rename_original_ring _ c lam (hfix g)]
  · exact (map_zero _).symm

theorem map_originalDegreeAction (φ : R →+* S) (G : Subgroup (Equiv.Perm (Fin n))) (d : ℕ) :
    EquivariantHomMatrices.mapRepresentation φ (originalDegreeAction (R := R) G d) =
      originalDegreeAction (R := S) G d := by
  classical
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  have hmat (M : Matrix (OriginalDegreeIndex n d) (OriginalDegreeIndex n d) S) :
      LinearMap.toMatrix' M.mulVecLin = M := LinearMap.toMatrix'_toLin' M
  change LinearMap.toMatrix' (Matrix.mulVecLin _) = _
  rw [hmat]
  ext a b
  simp only [Matrix.map_apply,LinearMap.toMatrix'_apply]
  change φ (shiftedRename (g : Equiv.Perm (Fin n)) a.1.val d _ a.2) =
    shiftedRename (R := S) (g : Equiv.Perm (Fin n)) a.1.val d _ a.2
  rw [map_shiftedRename]
  apply congrArg (fun v : ShiftedExponent n a.1.val d → S =>
    shiftedRename (R := S) (g : Equiv.Perm (Fin n)) a.1.val d v a.2)
  funext t
  simp only [Pi.single_apply, apply_ite φ, map_one, map_zero]

end Ring

section Field

variable {K : Type*} [Field K] {n : ℕ}

theorem originalDegreePolynomialMap_mem_hit (c : Fin n → K) (lam : K) (m d : ℕ)
    (v : OriginalDegreeIndex n d → K) :
    originalDegreePolynomialMap c lam m d v ∈ originalTailHit c lam m := by
  rw [originalDegreePolynomialMap_apply,originalFiniteMap]
  apply Submodule.sum_mem
  intro k hk
  split_ifs with hmk
  · exact Submodule.subset_span ⟨k.val,hmk,originalDegreeDecode d v k,rfl⟩
  · exact Submodule.zero_mem _

/-- Every generator of the infinite original tail has its homogeneous
projection in the full finite degree matrix image. -/
theorem original_projection_mem_degree_range (c : Fin n → K) (lam : K) (m d : ℕ)
    {p : MvPolynomial (Fin n) K} (hp : p ∈ originalTailHit c lam m) :
    shiftedProjection 0 d p ∈ LinearMap.range (originalDegreePolynomialMap c lam m d) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k,hk,q,rfl⟩ := hp
    rw [shiftedProjection_original,Nat.zero_add]
    by_cases hkd : k ≤ d
    · let j : Fin (d+1) := ⟨k,by omega⟩
      let v : ShiftedExponent n k d → K := fun a => (shiftedProjection k d q).coeff a.val
      refine ⟨originalDegreeInsert d j v,?_⟩
      rw [originalDegreePolynomialMap_apply,originalFiniteMap_insert,if_pos hk]
      congr 1
      exact shiftedDecode_coeffs k d _ (shiftedProjection_mem k d q)
    · have hz : shiftedProjection k d q = 0 := by
        simp only [shiftedProjection,hkd,if_false,LinearMap.zero_apply]
      rw [hz,map_zero]
      exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (LinearMap.range (originalDegreePolynomialMap c lam m d)).zero_mem
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact Submodule.add_mem _ ihp ihq
  | smul a p hp ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ a ih

end Field

end PaperVerification.PowerOperators
