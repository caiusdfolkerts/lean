module

public import Papers.GraphicalZonotopes.PathJoinSupermodular

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

theorem mobius_setMonomial {n : ℕ} (C : Finset (Vertex n)) :
    mobius (setMonomial C)=Pi.single C 1 := by
  apply zeta_injective
  rw [zeta_mobius,zeta_eq_sum_monomials]
  simp

theorem mobius_polynomial_clique {n : ℕ} (x : Slot n → ℝ) (s : Slot n) :
    mobius (FiniteMonomial.polynomial clique x) (clique s)=x s := by
  change zetaEquiv.symm (∑ i : Slot n,x i • setMonomial (clique i)) (clique s)=x s
  rw [map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (∑ i : Slot n,x i*mobius (setMonomial (clique i)) (clique s))=x s
  simp_rw [mobius_setMonomial]
  have he (i : Slot n) : (clique i=clique s) ↔ i=s :=
    ⟨fun h => clique_injective h,fun h => congrArg clique h⟩
  have he' (i : Slot n) : (clique s=clique i) ↔ s=i :=
    ⟨fun h => clique_injective h,fun h => congrArg clique h⟩
  simp only [Pi.single_apply,he']
  simp

def coordinate {n : ℕ} (f : SetFunction (Vertex n)) (s : Slot n) : ℝ :=
  mobius f (clique s)

@[simp] theorem coordinate_setFunction {n : ℕ} (s : Slot n) :
    coordinate (setFunction n) s=coefficient n s :=
  mobius_polynomial_clique (coefficient n) s

def aCoeff {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :=
  coordinate f (.inr (.inl (0,i)))
def bCoeff {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :=
  coordinate f (.inr (.inl (1,i)))
def eCoeff {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :=
  coordinate f (.inr (.inl (2,i)))
def dCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (0,j)))
def taCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (1,j)))
def tbCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (2,j)))
def hCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (3,j)))
def nCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  if j.val%2=0 then taCoeff f j else tbCoeff f j
def zCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  if j.val%2=0 then tbCoeff f j else taCoeff f j

theorem delta_a_hub {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :
    delta f (hubA n) (vertex i) {hubB n}=aCoeff f i+eCoeff f i := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubA_ne_vertex i)
    (hubA_ne_hubB n) (vertex_ne_hubB i)]
  simp [aCoeff,eCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_b_hub {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :
    delta f (hubB n) (vertex i) {hubA n}=bCoeff f i+eCoeff f i := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubB_ne_vertex i)
    (hubB_ne_hubA n) (vertex_ne_hubA i)]
  simp [bCoeff,eCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem delta_a_right {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubA n) (vertex j.succ) {vertex j.castSucc}=
      aCoeff f j.succ+taCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubA_ne_vertex j.succ)
    (hubA_ne_vertex j.castSucc) (vertex_right_ne_left j)]
  simp [aCoeff,taCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_b_right {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubB n) (vertex j.succ) {vertex j.castSucc}=
      bCoeff f j.succ+tbCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubB_ne_vertex j.succ)
    (hubB_ne_vertex j.castSucc) (vertex_right_ne_left j)]
  simp [bCoeff,tbCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_a_left {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubA n) (vertex j.castSucc) {vertex j.succ}=
      aCoeff f j.castSucc+taCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubA_ne_vertex j.castSucc)
    (hubA_ne_vertex j.succ) (vertex_left_ne_right j)]
  simp [aCoeff,taCoeff,coordinate,clique]

theorem delta_b_left {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubB n) (vertex j.castSucc) {vertex j.succ}=
      bCoeff f j.castSucc+tbCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubB_ne_vertex j.castSucc)
    (hubB_ne_vertex j.succ) (vertex_left_ne_right j)]
  simp [bCoeff,tbCoeff,coordinate,clique]

theorem delta_a_right_hub {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubA n) (vertex j.succ) {hubB n,vertex j.castSucc}=
      aCoeff f j.succ+eCoeff f j.succ+taCoeff f j+hCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubA_ne_vertex j.succ)
    (hubA_ne_hubB n) (hubA_ne_vertex j.castSucc)
    (vertex_ne_hubB j.succ) (vertex_right_ne_left j) (hubB_ne_vertex j.castSucc)]
  simp [aCoeff,eCoeff,taCoeff,hCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem delta_b_right_hub {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubB n) (vertex j.succ) {hubA n,vertex j.castSucc}=
      bCoeff f j.succ+eCoeff f j.succ+tbCoeff f j+hCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubB_ne_vertex j.succ)
    (hubB_ne_hubA n) (hubB_ne_vertex j.castSucc)
    (vertex_ne_hubA j.succ) (vertex_right_ne_left j) (hubA_ne_vertex j.castSucc)]
  simp [bCoeff,eCoeff,tbCoeff,hCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  have he : mobius f {hubB n,vertex j.succ,hubA n}=
      mobius f {hubA n,vertex j.succ,hubB n} := by
    congr 1
    ext x
    simp only [mem_insert,mem_singleton]
    tauto
  have hh : mobius f {hubB n,vertex j.castSucc,vertex j.succ,hubA n}=
      mobius f {hubA n,hubB n,vertex j.succ,vertex j.castSucc} := by
    congr 1
    ext x
    simp only [mem_insert,mem_singleton]
    tauto
  rw [he,hh]

theorem delta_path_a {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (vertex j.castSucc) (vertex j.succ) {hubA n}=
      dCoeff f j+taCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (vertex_left_ne_right j)
    (vertex_ne_hubA j.castSucc) (vertex_ne_hubA j.succ)]
  simp [dCoeff,taCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem delta_path_b {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (vertex j.castSucc) (vertex j.succ) {hubB n}=
      dCoeff f j+tbCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (vertex_left_ne_right j)
    (vertex_ne_hubB j.castSucc) (vertex_ne_hubB j.succ)]
  simp [dCoeff,tbCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem consecutive_middle {n : ℕ} (j : Fin n) :
    j.castSucc.succ=j.succ.castSucc := Fin.ext rfl

theorem consecutive_endpoints_ne {n : ℕ} (j : Fin n) :
    vertex j.castSucc.castSucc≠vertex j.succ.succ := by
  simp [vertex,Fin.ext_iff]

theorem consecutive_endpoints_nonadj {n : ℕ} (j : Fin n) :
    ¬(graph n).Adj (vertex j.castSucc.castSucc) (vertex j.succ.succ) := by
  rw [graph_vertices]
  simp only [Fin.val_castSucc,Fin.val_succ]
  omega

theorem delta_a_two_neighbors {n : ℕ} (f : SetFunction (Vertex n))
    (hn : TranslationNormalized f) (hg : Graphical (graph n) f) (j : Fin n) :
    delta f (hubA n) (vertex j.castSucc.succ)
      {vertex j.castSucc.castSucc,vertex j.succ.succ}=
      aCoeff f j.castSucc.succ+taCoeff f j.castSucc+taCoeff f j.succ := by
  have hy := (mobius_cliqueSupported_iff (graph n) f).mpr ⟨hn,hg⟩
  have hz : mobius f {hubA n,vertex j.castSucc.succ,
      vertex j.castSucc.castSucc,vertex j.succ.succ}=0 :=
    hy.2.2 _ _ _ (by simp) (by simp) (consecutive_endpoints_ne j)
      (consecutive_endpoints_nonadj j)
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubA_ne_vertex j.castSucc.succ)
    (hubA_ne_vertex j.castSucc.castSucc) (hubA_ne_vertex j.succ.succ)
    (vertex_right_ne_left j.castSucc)
    (by rw [consecutive_middle]; exact vertex_left_ne_right j.succ)
    (consecutive_endpoints_ne j),hz,add_zero]
  simp [aCoeff,taCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_b_two_neighbors {n : ℕ} (f : SetFunction (Vertex n))
    (hn : TranslationNormalized f) (hg : Graphical (graph n) f) (j : Fin n) :
    delta f (hubB n) (vertex j.castSucc.succ)
      {vertex j.castSucc.castSucc,vertex j.succ.succ}=
      bCoeff f j.castSucc.succ+tbCoeff f j.castSucc+tbCoeff f j.succ := by
  have hy := (mobius_cliqueSupported_iff (graph n) f).mpr ⟨hn,hg⟩
  have hz : mobius f {hubB n,vertex j.castSucc.succ,
      vertex j.castSucc.castSucc,vertex j.succ.succ}=0 :=
    hy.2.2 _ _ _ (by simp) (by simp) (consecutive_endpoints_ne j)
      (consecutive_endpoints_nonadj j)
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubB_ne_vertex j.castSucc.succ)
    (hubB_ne_vertex j.castSucc.castSucc) (hubB_ne_vertex j.succ.succ)
    (vertex_right_ne_left j.castSucc)
    (by rw [consecutive_middle]; exact vertex_left_ne_right j.succ)
    (consecutive_endpoints_ne j),hz,add_zero]
  simp [bCoeff,tbCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

end GraphicalZonotopes.PathJoin
