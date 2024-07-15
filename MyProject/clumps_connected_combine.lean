import MyProject

import MyProject.clumps_2basics

 --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


 --set_option maxHeartbeats 400000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h: ℕ}
variable (κPositive: κ >0)
variable (pPositive: p >0)
variable (mPositive: m >0)
variable (hPositive: h >0)
variable (prPositive: pr >0)
variable (prggp: pr≫ p)
variable (mggpr: m≫ pr)



lemma clump_add_Hi_and_I_cut_dense
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ :ℕ }
{I: Set V}
(hHi: Hi∈ K.H)
(μbiggerthanp: μ ≥ 2*p)
(qDef: q ≥  4096 * (κ^(2*Nat.factorial (100*K.k))) * μ*h^2*pr)
(hI: I⊆ BSet K)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
:
cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))) q := by

let q1:ℕ := 32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h
--let q2:ℕ :=16*(κ^(2*Nat.factorial (100*K.k)))

have hq1bound: 32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h≥16*(κ^(2*Nat.factorial (100*K.k))):=by
  calc
  32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h
  ≥ 32 * (κ^(2*Nat.factorial (100*K.k))) * μ*1:=by
    gcongr
    exact hPositive
  _=(2*μ )*(16 * (κ^(2*Nat.factorial (100*K.k)))) := by
    ring_nf
  _≥ 1*(16*(κ^(2*Nat.factorial (100*K.k)))):=by
    gcongr
    --16 ≤ 2 * μ
    sorry
  _=16*(κ^(2*Nat.factorial (100*K.k))):=by
    ring_nf

#check clump_add_B_vertices_cut_dense_simplified
have cutdense1: cut_dense G (K.Gr.induce (I∪ K.C.verts)) q1:= by
  apply clump_add_B_vertices_cut_dense_simplified  κPositive pPositive μ _ _ _
  exact Iorder
  exact Iorderupperbound
  exact μbiggerthanp
  exact Nat.le_refl (32 * κ ^ (2 * (100 * K.k).factorial) * μ * h) --Nat.le_refl (32 * κ ^ (2 * (100 * K.k).factorial) * μ)
  exact hI

have q1Positive: q1>0:= by
  calc
  q1=32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h:=by
    exact rfl
  _>0:=by
    apply Nat.mul_pos
    apply Nat.mul_pos
    apply Nat.mul_pos

    exact Nat.zero_lt_succ 31
    exact Nat.pos_pow_of_pos (2 * (100 * K.k).factorial) κPositive
    calc
      μ≥ 2*p:= by
        exact μbiggerthanp
      _>0:= by
        apply Nat.mul_pos
        exact Nat.zero_lt_two
        exact pPositive
    exact hPositive




have cutdense2: cut_dense G (K.C⊔ Hi) q1 := by
  apply clump_add_Hi_cut_dense
  exact mPositive
  exact pPositive
  exact κPositive
  exact hq1bound
  exact hHi



#check cut_dense_union_simplified
apply cut_dense_union_simplified  q1 q (6*h*pr)

exact cutdense1
exact cutdense2

calc
  16 * q1 * (6 * h * pr)≤ 16 * q1 * (8 * h * pr):=by
    gcongr
    exact Nat.le_of_ble_eq_true rfl
  _=4096 * (κ^(2*Nat.factorial (100*K.k))) * μ * h^2 * pr:=by
    ring_nf
  _≤ q:=by
    exact qDef

exact q1Positive


--((K.Gr.induce (I ∪ K.C.verts)).verts ∩ (K.C ⊔ Hi).verts).Nonempty
sorry



have h1: (K.Gr.induce (I ∪ K.C.verts)).verts=I∪ K.C.verts:= by
  exact rfl
rw[h1]
have h1: (K.C ⊔ Hi).verts=K.C.verts ∪ Hi.verts:= by
  exact rfl
rw[h1]
have h1: I ∪ K.C.verts ∪ (K.C.verts ∪ Hi.verts)=I ∪ K.C.verts ∪ Hi.verts:= by
  calc
  I ∪ K.C.verts ∪ (K.C.verts ∪ Hi.verts)=I ∪ (K.C.verts ∪ K.C.verts) ∪ Hi.verts:=by
   rw [@Set.union_assoc]
   rw [@Set.union_assoc]
   rw [@Set.union_assoc]
  _=I ∪ K.C.verts ∪ Hi.verts:=by
    congr
    exact Set.union_eq_self_of_subset_left fun ⦃a⦄ a ↦ a
simp_rw[h1]

simp
calc
(I.toFinset ∪ (K.C.verts.toFinset ∪ Hi.verts.toFinset)).card
_≤ (I.toFinset).card + (K.C.verts.toFinset∪  Hi.verts.toFinset).card:= by
  exact card_union_le I.toFinset (K.C.verts.toFinset ∪ Hi.verts.toFinset)
_≤ I.toFinset.card + (K.C.verts.toFinset.card + Hi.verts.toFinset.card):= by
  gcongr
  exact card_union_le K.C.verts.toFinset Hi.verts.toFinset
_= I.toFinset.card + K.C.verts.toFinset.card + Hi.verts.toFinset.card:= by ring_nf
_≤ I.toFinset.card + K.C.verts.toFinset.card + h*m:= by
  gcongr
  apply K.H_Order_Upper_Bound
  exact hHi
_≤ K.C.verts.toFinset.card + K.C.verts.toFinset.card + h*m:= by
  gcongr
_≤ K.C.verts.toFinset.card + K.C.verts.toFinset.card + h*(4*pr*K.C.verts.toFinset.card):=by
  gcongr
  exact C_lower_bound_simplified prPositive
_=K.C.verts.toFinset.card*(2*1*1+4*h*pr):=by
  ring_nf
_≤ K.C.verts.toFinset.card*(2*h*pr+4*h*pr):=by
  gcongr
  exact hPositive
  exact prPositive
_=K.C.verts.toFinset.card*(6*h*pr):=by
  ring_nf
_≤ ((I.toFinset ∪ K.C.verts.toFinset) ∩ (K.C.verts.toFinset ∪ Hi.verts.toFinset)).card *(6*h*pr):=by
  gcongr
  simp

/-
lemma clump_add_Hi_and_I_easier_subgraph
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ :ℕ }
{I: Set V}
(hHi: Hi∈ K.H)
(μbiggerthanp: μ ≥ κ)
(qDef: q ≥  4096 * (κ^(4*Nat.factorial (100*K.k))) * μ)
(hI: I⊆ BSet K)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
:K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))≤K.Gr.induce (I∪ K.C.verts∪ Hi.verts):=by
refine subgraph_subgraph_of_induced_on_larger_set ?hS ?hHK
sorry
sorry
-/



lemma BSet_subgraph_Kgr
{K: Clump G p m κ pr h}
:BSet K ⊆ K.Gr.verts:=by
unfold BSet
exact  Set.sep_subset K.Gr.verts fun x ↦(K.Gr.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2 ≥ m




lemma clump_add_Hi_and_I_easier_subgraph_verts
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{I: Set V}
(hI: I⊆ BSet K)
:(K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))).verts=(K.Gr.induce (I∪ K.C.verts)⊔Hi).verts:=by
have h1:K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))=K.Gr.induce (I∪ K.C.verts)⊔ K.C⊔Hi:=by
  exact (sup_assoc (K.Gr.induce (I ∪ K.C.verts)) K.C Hi).symm
rw[h1]
congr
have h2: (K.Gr.induce (I∪ K.C.verts)).verts= (I∪ K.C.verts):= by
  exact rfl
have h3: (K.Gr.induce (I ∪ K.C.verts) ⊔ K.C⊔ Hi).verts=(I∪ K.C.verts) ∪ K.C.verts∪  Hi.verts:= by
  exact rfl
rw[h3]
simp
calc
I ∪ K.C.verts ∪ K.C.verts ∪ Hi.verts
=I ∪ (K.C.verts ∪ K.C.verts) ∪ Hi.verts:=by
  rw [@Set.union_assoc]
  rw [@Set.union_assoc]
  rw [@Set.union_assoc]
  rw [@Set.union_assoc]
_= I ∪ K.C.verts ∪ Hi.verts:= by
  congr
  exact Set.union_eq_self_of_subset_left fun ⦃a⦄ a ↦ a

lemma clump_add_Hi_and_I_easier_subgraph
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{I: Set V}
(hI: I⊆ BSet K)
:K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))≤K.Gr.induce (I∪ K.C.verts)⊔ Hi:=by
have h1:K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))=K.Gr.induce (I∪ K.C.verts)⊔ K.C⊔Hi:=by
  exact (sup_assoc (K.Gr.induce (I ∪ K.C.verts)) K.C Hi).symm
rw[h1]
gcongr
refine subgraph_subgraph_of_induced_on_larger_set ?h₁.hS ?h₁.hHK
have h2: (K.Gr.induce (I∪ K.C.verts)).verts= (I∪ K.C.verts):= by
  exact rfl
have h3: (K.Gr.induce (I ∪ K.C.verts) ⊔ K.C).verts=(I∪ K.C.verts) ∪ K.C.verts:= by
  exact rfl
rw[h3]
simp

refine sup_le_iff.mpr ?h₁.hHK.a
constructor
refine induced_subgraph_subgraph ?h₁.hHK.a.left.hS
refine Set.union_subset ?h₁.hHK.a.left.hS.sr ?h₁.hHK.a.left.hS.tr
--I ⊆ K.Gr.verts
calc
  I⊆ BSet K:= by
   exact hI
  _⊆ K.Gr.verts:= by
    exact BSet_subgraph_Kgr


apply subgraphs_vertex_sets_subsets G
exact K.C_In_K
exact K.C_In_K

lemma clump_add_Hi_and_I_cut_dense_simplified
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ :ℕ }
{I: Set V}
(hHi: Hi∈ K.H)
(μbiggerthanp: μ ≥ κ)
(qDef: q ≥  4096 * (κ^(4*Nat.factorial (100*K.k))) * μ)
(hI: I⊆ BSet K)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
:cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))) q := by
have h1: q≥ 4096 * (κ^(2*Nat.factorial (100*K.k))) * μ * h^2 * pr:= by
  calc
  q≥  4096 * (κ^(4*Nat.factorial (100*K.k))) * μ:= by
    exact qDef
  _= 4096 * (κ^(2*Nat.factorial (100*K.k)+ 2*Nat.factorial (100*K.k))) * μ:= by
    ring_nf
  _≥ 4096 * (κ^(2*Nat.factorial (100*K.k)+ 2)) * μ:=by
    gcongr
    exact κPositive
    refine Nat.le_mul_of_pos_right 2 ?bc.bc.h.bc.h
    exact Nat.factorial_pos (100 * K.k)
  _=4096 * (κ^(2*Nat.factorial (100*K.k))*κ^2) * μ:=by
    ring_nf
  _= 4096 * (κ^(2*Nat.factorial (100*K.k))) * μ * κ*κ :=by
    ring_nf
  _≥  4096 * (κ^(2*Nat.factorial (100*K.k))) * μ * h^2 * pr:=by
    gcongr
    --h ≤ κ
    sorry
    --pr ≤ κ
    sorry

have h2: μ ≥ 2*p:= by
  calc
  μ≥ κ:= by
    exact μbiggerthanp
  _≥ 2*p:= by
    --κ≥ 2*p
    sorry
exact clump_add_Hi_and_I_cut_dense κPositive pPositive mPositive hPositive  prPositive  hHi h2 h1 hI Iorder Iorderupperbound



lemma clump_add_Hi_and_I_cut_dense_more_simplified
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ :ℕ }
{I: Set V}
(hHi: Hi∈ K.H)
(μbiggerthanp: μ ≥ κ)
(qDef: q ≥  4096 * (κ^(4*Nat.factorial (100*K.k))) * μ)
(hI: I⊆ BSet K)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
:cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ Hi) q := by
have h1: cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))) q := by
  exact
    clump_add_Hi_and_I_cut_dense_simplified κPositive pPositive mPositive hPositive prPositive  hHi μbiggerthanp
      qDef hI Iorder Iorderupperbound

have h2: K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))≤K.Gr.induce (I∪ K.C.verts)⊔ Hi:=by
  exact clump_add_Hi_and_I_easier_subgraph hI
apply cut_dense_subgraph_monotone _ h2
exact clump_add_Hi_and_I_easier_subgraph_verts hI
exact h1



lemma two_clump_add_Hi_and_I_cut_dense
{K1 K2: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ k:ℕ }
{I: Set V}
(hHi: Hi∈ K1.H)
(μbiggerthanp: μ ≥ κ)
(hk1biggerthank: K1.k ≤  k)
(hk2biggerthank: K2.k ≤  k)
(qDef: q ≥  (κ^(7*Nat.factorial (100*k)))*μ^2)
(hI: I⊆ BSet K1∩ BSet K2)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: 4*pr*I.toFinset.card≤ m)
:cut_dense G (K1.Gr.induce (I∪ K1.C.verts)⊔ Hi⊔ K2.Gr.induce (I∪ K2.C.verts)) q := by
have hIupperbound1: 4*pr*I.toFinset.card≤ 4*pr*K1.C.verts.toFinset.card:= by
  calc
  4*pr*I.toFinset.card≤m:= by
    exact Iorderupperbound
  _≤ 4*pr*K1.C.verts.toFinset.card:= by
    exact C_lower_bound_simplified prPositive
have hIupperbound1: I.toFinset.card≤ K1.C.verts.toFinset.card:= by
  apply Nat.le_of_mul_le_mul_left hIupperbound1 _
  exact Nat.succ_mul_pos 3 prPositive

have hIupperbound2: 4*pr*I.toFinset.card≤ 4*pr*K2.C.verts.toFinset.card:= by
  calc
  4*pr*I.toFinset.card≤m:= by
    exact Iorderupperbound
  _≤ 4*pr*K2.C.verts.toFinset.card:= by
    exact C_lower_bound_simplified prPositive
have hIupperbound2: I.toFinset.card≤ K2.C.verts.toFinset.card:= by
  apply Nat.le_of_mul_le_mul_left hIupperbound2 _
  exact Nat.succ_mul_pos 3 prPositive

let q1:ℕ :=4096* (κ^(4*Nat.factorial (100*k))) * μ*h


have cutdense1: cut_dense G (K1.Gr.induce (I∪ K1.C.verts)⊔ Hi) q1:=by
  apply clump_add_Hi_and_I_cut_dense_more_simplified
  exact κPositive
  exact pPositive
  exact mPositive
  exact hPositive
  exact prPositive
  exact hHi
  exact μbiggerthanp
  calc
    q1=4096* (κ^(4*Nat.factorial (100*k))) * μ*h:= by
      exact rfl
    _≥ 4096* (κ^(4*Nat.factorial (100*k))) * μ*1:= by
      gcongr
      --h≥ 1
      sorry
    _= 4096* (κ^(4*Nat.factorial (100*k))) * μ:= by
      ring_nf
    _≥ 4096* (κ^(4*Nat.factorial (100*K1.k))) * μ:= by
      gcongr
      exact κPositive
  calc
    I ⊆ BSet K1 ∩ BSet K2:= by exact hI
    _⊆  BSet K1:= by
      exact Set.inter_subset_left (BSet K1) (BSet K2)
  exact Iorder
  exact hIupperbound1

let q2:ℕ :=  32 * (κ^(2*Nat.factorial (100*K2.k))) * μ

have hq1_q2_ineq: q1≥q2*h:= by
  calc
  q1=4096* (κ^(4*Nat.factorial (100*k))) * μ*h:= by
    exact rfl
  _≥ 32 * (κ^(2*Nat.factorial (100*K2.k))) * μ*h:= by
    gcongr
    exact Nat.le_of_ble_eq_true rfl
    exact κPositive
    exact Nat.AtLeastTwo.prop


have μPositive: μ>0:= by
  calc
  μ≥κ:= by
    exact μbiggerthanp
  _>0:= by
    exact κPositive

have cutdense2: cut_dense G (K2.Gr.induce (I∪ K2.C.verts)) q1:=by
  apply clump_add_B_vertices_cut_dense_simplified
  exact κPositive
  exact pPositive
  calc
     μ ≥ κ:= by
       exact μbiggerthanp
      _≥ 2*p:= by
        --κ≥ 2*p
        sorry
  exact hq1_q2_ineq
  calc
    I ⊆ BSet K1 ∩ BSet K2:= by exact hI
    _⊆  BSet K2:= by
      exact Set.inter_subset_right (BSet K1) (BSet K2)
  exact Iorder
  exact hIupperbound2

apply cut_dense_union_simplified  q1 q (2*μ*4^(k)*h^2)
exact cutdense1
exact cutdense2

--q ≥ 16 * (4096* (κ^(4*Nat.factorial (100*k))) * μ) * (2 * μ * 4 ^ k * h)
calc
  16 * q1 * (2 * μ * 4 ^ k * h^2)
  =16 * (4096* (κ^(4*Nat.factorial (100*k))) * μ*h) * (2 * μ * 4 ^ k * h^2):=by
    rw [Nat.mul_mul_mul_comm]

  _=131072*(κ^(4*Nat.factorial (100*k)))*μ^2*h^3*4^(k):=by
    ring_nf

  _≤ κ*(κ^(4*Nat.factorial (100*k)))*μ^2*κ*κ^(k):=by
    gcongr
    --131072 ≤ κ
    sorry
    --h^3 ≤ κ
    sorry
    --4 ≤ κ
    sorry
  _=(κ^(4*Nat.factorial (100*k)+1+1+k))*μ^2:=by
    ring_nf
  _≤(κ^(4*Nat.factorial (100*k)+Nat.factorial (100*k)+Nat.factorial (100*k)+Nat.factorial (100*k)))*μ^2:=by
    gcongr
    exact κPositive
    refine Nat.succ_le_of_lt ?bc.bc.h.h₁.bc.h
    exact Nat.factorial_pos (100 * k)
    refine Nat.succ_le_of_lt ?bc.bc.h.h₁.bc.h
    calc
    k= 1*k:= by  ring_nf
    _≤ 100*k:= by  gcongr; exact NeZero.one_le
    _≤ (100 * k).factorial:= by exact Nat.self_le_factorial (100 * k)
  _=(κ^(7*Nat.factorial (100*k)))*μ^2:=by ring_nf
  _≤ q:=by
    exact qDef


calc
  q1=4096* (κ^(4*Nat.factorial (100*k))) * μ*h:= by exact rfl
  _>0:=by
    apply Nat.mul_pos
    apply Nat.mul_pos
    apply Nat.mul_pos
    exact Nat.zero_lt_succ 4095
    exact Nat.pos_pow_of_pos (4 * (100 * k).factorial) κPositive
    exact μPositive
    --h>0
    sorry

--((K1.Gr.induce (I ∪ K1.C.verts) ⊔ Hi).verts ∩ (K2.Gr.induce (I ∪ K2.C.verts)).verts).Nonempty
sorry

simp
calc
(I.toFinset ∪ (K1.C.verts.toFinset ∪ (Hi.verts.toFinset ∪ (I.toFinset ∪ K2.C.verts.toFinset)))).card
_=(I.toFinset ∪ K1.C.verts.toFinset ∪ Hi.verts.toFinset ∪ I.toFinset ∪ K2.C.verts.toFinset).card:=by
  simp
_≤ I.toFinset.card+  K1.C.verts.toFinset.card+ Hi.verts.toFinset.card + I.toFinset.card + K2.C.verts.toFinset.card:=by
  exact card_union_5 I.toFinset K1.C.verts.toFinset Hi.verts.toFinset I.toFinset K2.C.verts.toFinset
_=2*I.toFinset.card+  K1.C.verts.toFinset.card+ Hi.verts.toFinset.card + K2.C.verts.toFinset.card:=by
  ring_nf
_≤ 2*I.toFinset.card+  K1.C.verts.toFinset.card+ Hi.verts.toFinset.card + m*h*4^(K2.k):=by
  gcongr
  exact K2.C_Order
_≤ 2*I.toFinset.card+  m*h*4^(K1.k)+ Hi.verts.toFinset.card + m*h*4^(K2.k):=by
  gcongr
  exact K1.C_Order
_≤ 2*I.toFinset.card+  m*h*4^(k)+ h*m + m*h*4^(K2.k):=by
  gcongr
  exact NeZero.one_le
  apply K1.H_Order_Upper_Bound
  exact hHi
_≤ 2*I.toFinset.card+  (μ *I.toFinset.card)*h*4^(k)+ h*(μ *I.toFinset.card) + (μ *I.toFinset.card)*h*4^(K2.k):=by
  gcongr
_=I.toFinset.card*(2+μ*h*4^(k)+h*μ+μ*h*4^(K2.k)):=by
  ring_nf
_≤ I.toFinset.card*(2*μ*h*4^(k)*h):= by
  gcongr
  --2 + μ * h*4 ^ k + h * μ + μ * h*4 ^ K2.k ≤ 2 * μ * 4 ^ k * h^2
  sorry
_≤ ((I.toFinset ∪ (K1.C.verts.toFinset ∪ Hi.verts.toFinset)) ∩ (I.toFinset ∪ K2.C.verts.toFinset)).card * (2*μ*h*4^(k)*h):= by
  gcongr
  simp
_=((I.toFinset ∪ (K1.C.verts.toFinset ∪ Hi.verts.toFinset)) ∩ (I.toFinset ∪ K2.C.verts.toFinset)).card *
    (2 * μ * 4 ^ k * h ^ 2):=by
  ring_nf
