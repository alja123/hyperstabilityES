--import MyProject

import hyperstabilityES.lemmas.clumps_2basics

 --import hyperstabilityES.lemmas.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 600000

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
variable (iSub:Inhabited (Subgraph G))



lemma clump_add_Hi_and_I_cut_dense
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ :ℕ }
{I': Set V}
(hHi: Hi∈ K.H)
(μbiggerthanp: μ ≥ 2*p)
(qDef: q ≥  4096 * (κ^(2*Nat.factorial (100*K.k))) * μ*h^2*pr)
(hI': I'⊆ BSetPlusM K)
(I'orderupperbound: I'.toFinset.card≤ K.C.verts.toFinset.card)
(pLarge: p≥ 20)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ p)
(κggh: κ ≥ h)
:
cut_dense G (K.Gr.induce (I'∪ K.C.verts)⊔ ((K.C⊔Hi))) q := by

let I: Set V:= I'∩ (BSet K)
have hI:I ⊆ BSet K:= by
  exact Set.inter_subset_right I' (BSet K)
have Iorderupperbound:I.toFinset.card≤ K.C.verts.toFinset.card:= by
  calc
    I.toFinset.card≤
    I'.toFinset.card:= by
      gcongr
      dsimp[I]
      simp
    _≤     K.C.verts.toFinset.card:= by
      assumption

have Iunion: I∪ K.C.verts=I'∪ K.C.verts:= by
  --dsimp[I]
  have h2: I'⊆   I∪(BSetPlusM K\ BSet K):= by
    dsimp[I]
    intro x hx
    simp
    have h5: x∈ BSetPlusM K:= by
      exact hI' hx
    have h6: x ∈ BSet K ∨ x ∉ BSet K:= by
      exact Decidable.em (x ∈ BSet K)
    aesop
  have h0: I∪ K.C.verts⊆ I'∪ K.C.verts:= by
    gcongr
    dsimp[I]
    exact Set.inter_subset_left I' (BSet K)

  have h01: I∪ K.C.verts⊇  I'∪ K.C.verts:= by
    calc
      I'∪ K.C.verts⊆(I∪(BSetPlusM K\ BSet K))∪ K.C.verts:= by
        gcongr
      _= I∪ ((BSetPlusM K\ BSet K)∪ K.C.verts):= by
        rw [@Set.union_assoc]
      _= I∪ K.C.verts:= by
        congr
        unfold BSetPlusM
        simp only [ mem_coe, Set.union_diff_left, Set.union_eq_right]
        calc
          _ ⊆(sSup K.M: Subgraph G).verts:= by
            exact Set.diff_subset (sSup ↑K.M: Subgraph G).verts (BSet K)
          _⊆ K.C.verts:= by
            exact clump_M_contained_in_C
  exact Set.Subset.antisymm h0 h01



rw[Iunion.symm]

have κLarge: κ≥ 4:= by
  calc
    κ ≥ h:= by assumption
    _≥ p:= by assumption
    _≥ 20:= by assumption
    _≥ 4:= by simp


have mLarge: m≥ 20:=by
  calc
    m ≥ pr:= by
      apply gg1_ge
      repeat assumption
    _≥ p:= by
      apply gg2_ge
      repeat assumption
    _≥ 20:= by assumption

have μPositive: μ>0:= by
  calc
    μ ≥ 2*p:= by assumption
    _≥ 2*1:= by
      gcongr
      exact pPositive
    _=2:= by ring_nf
    _>0:= by simp

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
    refine Right.one_le_mul ?bc.ha ?bc.hb
    simp
    assumption
  _=16*(κ^(2*Nat.factorial (100*K.k))):=by
    ring_nf

#check clump_add_B_vertices_cut_dense_simplified
have cutdense1: cut_dense G (K.Gr.induce (I∪ K.C.verts)) q1:= by
  apply clump_add_B_vertices_cut_dense_simplified  κPositive pPositive μ _ _ _
  repeat assumption
  calc
    _ =  I.toFinset.card:= by
      dsimp [I]
      simp
    _≤ _:= by exact Iorderupperbound
    _= _:= by simp
  repeat assumption
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
  repeat assumption
  --




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
have h33: K.C.verts⊆ ((K.Gr.induce (I ∪ K.C.verts)).verts ∩ (K.C ⊔ Hi).verts):= by
  simp

have h44: K.C.verts.Nonempty := by
  have h55:K.C.verts.toFinset.Nonempty:= by
    apply clump_C_has_verts
    repeat assumption
  simp at h55
  exact h55
  --
exact Set.Nonempty.mono h33 h44




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
  exact C_lower_bound_simplified prPositive mggpr
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

-/



lemma BSet_subgraph_Kgr
{K: Clump G p m κ pr h}
:BSet K ⊆ K.Gr.verts:=by
unfold BSet
exact  Set.sep_subset K.Gr.verts fun x ↦(K.Gr.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2 ≥ m


lemma BSetPlusM_subgraph_Kgr
{K: Clump G p m κ pr h}
:BSetPlusM K ⊆ K.Gr.verts:=by
unfold BSetPlusM
refine Set.union_subset ?sr ?tr
exact  Set.sep_subset K.Gr.verts fun x ↦(K.Gr.neighborSet x ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2 ≥ m
apply subgraphs_vertex_sets_subsets G
simp
intro M hM
have h1: _:= by exact K.M_graphs_in_H M hM
rcases h1 with ⟨Hi, hHi1, hHi2 ⟩
have h2: Hi≤ K.Gr:= by
  apply K.H_In_K
  assumption
exact Preorder.le_trans M Hi K.Gr hHi2 h2



lemma clump_add_Hi_and_I_easier_subgraph_verts
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{I: Set V}
--(hI: I⊆ BSet K)
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
(hI: I⊆ BSetPlusM K)
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
  I⊆ BSetPlusM K:= by
   exact hI
  _⊆ K.Gr.verts:= by
    exact BSetPlusM_subgraph_Kgr


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
(hI: I⊆ BSetPlusM K)
--(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
(pLarge: p≥ 20)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ pr)
(κggh: κ ≥ gg1 h)
:cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))) q := by
have κgeh:κ ≥ h:=by
  apply gg1_ge
  repeat assumption
have hgep: h≥ p:= by
  calc
    h≥ pr:= by assumption
    _≥ p:= by
      apply gg2_ge
      repeat assumption



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
    calc
      κ ≥ 10000 *h^3:=by
        apply gg1_1
        assumption
        assumption
      _≥ 1*h^2:= by
        gcongr
        simp
        exact hPositive
        simp
      _=h^2:= by
        ring_nf

    --pr ≤ κ
    calc
      κ ≥ h:= by
        apply gg1_ge
        repeat assumption
      _≥ pr:= by
        assumption


have h2: μ ≥ 2*p:= by
  calc
  μ≥ κ:= by
    exact μbiggerthanp
  _≥ 2*p:= by
    --κ≥ 2*p
    calc
      κ ≥ 10000 *h^3:=by
        apply gg1_1
        assumption
        assumption
      _≥ 2*h^1:= by
        gcongr
        simp
        exact hPositive
        simp
      _= 2*h:= by
        ring_nf
      _≥ 2*p:= by
        gcongr
apply clump_add_Hi_and_I_cut_dense κPositive pPositive mPositive hPositive  prPositive  iSub hHi h2 h1 hI Iorderupperbound pLarge mggpr prggp
repeat assumption

lemma clump_add_Hi_and_I_cut_dense_more_simplified
{K: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ :ℕ }
{I: Set V}
(hHi: Hi∈ K.H)
(μbiggerthanp: μ ≥ κ)
(qDef: q ≥  4096 * (κ^(4*Nat.factorial (100*K.k))) * μ)
(hI: I⊆ BSetPlusM K)
--(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
(pLarge: p≥ 20)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ pr)
(κggh: κ ≥ gg1 h)
:cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ Hi) q := by
have h1: cut_dense G (K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))) q := by
  apply
    clump_add_Hi_and_I_cut_dense_simplified κPositive pPositive mPositive hPositive prPositive iSub hHi μbiggerthanp
      qDef hI Iorderupperbound
  repeat assumption

have h2: K.Gr.induce (I∪ K.C.verts)⊔ ((K.C⊔Hi))≤K.Gr.induce (I∪ K.C.verts)⊔ Hi:=by
  exact clump_add_Hi_and_I_easier_subgraph hI
apply cut_dense_subgraph_monotone _ h2
exact clump_add_Hi_and_I_easier_subgraph_verts
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
(hI: I⊆ BSetPlusM K1∩ BSetPlusM K2)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: 4*pr*I.toFinset.card≤ m)
(pLarge: p≥ 20)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ pr)
(κggh: κ ≥ gg1 h)
(mggμ: m≥ μ )
:cut_dense G (K1.Gr.induce (I∪ K1.C.verts)⊔ Hi⊔ K2.Gr.induce (I∪ K2.C.verts)) q := by
have hIupperbound1: 4*pr*I.toFinset.card≤ 4*pr*K1.C.verts.toFinset.card:= by
  calc
  4*pr*I.toFinset.card≤m:= by
    exact Iorderupperbound
  _≤ 4*pr*K1.C.verts.toFinset.card:= by
    apply C_lower_bound_simplified prPositive
    repeat assumption
have hIupperbound1: I.toFinset.card≤ K1.C.verts.toFinset.card:= by
  apply Nat.le_of_mul_le_mul_left hIupperbound1 _
  exact Nat.succ_mul_pos 3 prPositive

have hIupperbound2: 4*pr*I.toFinset.card≤ 4*pr*K2.C.verts.toFinset.card:= by
  calc
  4*pr*I.toFinset.card≤m:= by
    exact Iorderupperbound
  _≤ 4*pr*K2.C.verts.toFinset.card:= by
    apply C_lower_bound_simplified prPositive
    repeat assumption
have hIupperbound2: I.toFinset.card≤ K2.C.verts.toFinset.card:= by
  apply Nat.le_of_mul_le_mul_left hIupperbound2 _
  exact Nat.succ_mul_pos 3 prPositive

let q1:ℕ :=4096* (κ^(4*Nat.factorial (100*k))) * μ*h


have cutdense1: cut_dense G (K1.Gr.induce (I∪ K1.C.verts)⊔ Hi) q1:=by
  apply clump_add_Hi_and_I_cut_dense_more_simplified
  repeat assumption
  calc
    q1=4096* (κ^(4*Nat.factorial (100*k))) * μ*h:= by
      exact rfl
    _≥ 4096* (κ^(4*Nat.factorial (100*k))) * μ*1:= by
      gcongr
      --h≥ 1
      exact hPositive
    _= 4096* (κ^(4*Nat.factorial (100*k))) * μ:= by
      ring_nf
    _≥ 4096* (κ^(4*Nat.factorial (100*K1.k))) * μ:= by
      gcongr
      exact κPositive
  calc
    I ⊆ BSetPlusM K1 ∩ BSetPlusM K2:= by exact hI
    _⊆  BSetPlusM K1:= by
      exact Set.inter_subset_left (BSetPlusM K1) (BSetPlusM  K2)
  exact hIupperbound1
  repeat assumption

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
  apply clump_add_BSetPlusM_vertices_cut_dense_simplified
  exact κPositive
  exact pPositive
  calc
     μ ≥ κ:= by
       exact μbiggerthanp
      _≥ 2*p:= by
        --κ≥ 2*p
        calc
          κ ≥10000 *h^3:= by
            apply gg1_1
            repeat assumption
          _≥ 2*h^1:= by
            gcongr
            simp
            assumption
            simp
          _=2*h:=by ring_nf
          _≥2*pr:= by
            gcongr
          _≥ 2*p:= by
            gcongr
            apply gg2_ge
            exact prggp
            exact pPositive

  exact hq1_q2_ineq
  calc
    I ⊆ BSetPlusM K1 ∩ BSetPlusM K2:= by exact hI
    _⊆  BSetPlusM K2:= by
      exact Set.inter_subset_right (BSetPlusM K1) (BSetPlusM K2)
  exact hIupperbound2
  exact mggpr
  exact prPositive
  exact hPositive

  calc
          κ ≥10000 *h^3:= by
            apply gg1_1
            repeat assumption
          _≥ 4*h^0:= by
            gcongr
            simp
            assumption
            simp
          _=4:=by ring_nf

  --



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
    calc
          κ ≥10000 *h^3:= by
            apply gg1_1
            repeat assumption
          _≥ 10000*h^1:= by
            gcongr
            exact hPositive
            simp
          _=10000*h:=by ring_nf
          _≥10000*pr:= by
            gcongr
          _≥ 10000*(gg1 p):= by
            gcongr
            apply gg2_gg1
            exact prggp
            exact pPositive
          _≥10000*(10000* p^3):= by
            gcongr
            apply gg1_1
            exact Nat.le_refl (gg1 p)
            assumption
          _≥10000*(10000* 1^3):= by
            gcongr
            assumption
          _=100000000:= by
            ring_nf
          _≥ _:= by
            simp

    --h^3 ≤ κ
    calc
          κ ≥10000 *h^3:= by
            apply gg1_1
            repeat assumption
          _≥ 1*h^3:= by
            gcongr
            simp
          _=h^3:=by ring_nf
    --4 ≤ κ
    calc
          κ ≥10000 *h^3:= by
            apply gg1_1
            repeat assumption
          _≥ 4*h^0:= by
            gcongr
            simp
            assumption
            simp
          _=4:=by ring_nf
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
    assumption

--((K1.Gr.induce (I ∪ K1.C.verts) ⊔ Hi).verts ∩ (K2.Gr.induce (I ∪ K2.C.verts)).verts).Nonempty
simp
have hInonemp: I.toFinset.card>0:=by
  calc
    I.toFinset.card≥ m/μ := by
      exact Nat.div_le_of_le_mul Iorder
    _>0:= by
      refine Nat.div_pos ?hba μPositive
      assumption


have hInonemp2: I.toFinset.Nonempty:= by
  exact card_pos.mp hInonemp
simp at hInonemp2
have h22: I ⊆ (I ∪ K1.C.verts ∪ Hi.verts) := by
  rw[Set.union_assoc]
  apply Set.subset_union_left

have h33: I ⊆ (I ∪ K2.C.verts):= by
  exact Set.subset_union_left I K2.C.verts
refine Set.inter_nonempty.mpr ?hNonemptyIntersection.a
let x:=hInonemp2.some
use x
have xinI:x∈ I:= by
  exact Set.Nonempty.some_mem hInonemp2
constructor
exact h22 xinI
exact h33 xinI


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
  -- 2 + μ * h * 4 ^ k + h * μ + μ * h * 4 ^ K2.k ≤ 2 * μ * h * 4 ^ k * h
  calc
    2 * μ * h * 4 ^ k * h
    ≥
    2 * μ * h * 4 ^ k * 4:= by
      gcongr
      calc
        h≥pr:= by assumption
        _≥ gg1 p:= by
          apply gg2_gg1
          repeat assumption
        _≥ 10000:= by
          apply gg1_large
          assumption
        _≥ 4:= by simp
    _=8* μ * h * (4 ^ k):= by
      ring_nf
    _≥5* μ * h * (4 ^ k):= by
      gcongr
      simp
    _=
    2*μ * h * (4 ^ k)
    +μ * h * (4 ^ k)
    +μ * h * (4 ^ k)
    +μ * h * (4 ^ k):= by
      ring_nf
    _≥
    2*1 * 1 * (1)
    +μ * h * (4 ^ k)
    +μ * h * (1)
    +μ * h * (4 ^ (K2.k)):= by
      gcongr
      repeat assumption
      exact Nat.one_le_pow' k 3
      repeat assumption
      exact Nat.one_le_pow' k 3
      repeat assumption
      simp


    _=
    2
    + μ * h * 4 ^ k
    + h * μ
    + μ * h * 4 ^ K2.k:= by
      ring_nf


_≤ ((I.toFinset ∪ (K1.C.verts.toFinset ∪ Hi.verts.toFinset)) ∩ (I.toFinset ∪ K2.C.verts.toFinset)).card * (2*μ*h*4^(k)*h):= by
  gcongr
  simp
_=((I.toFinset ∪ (K1.C.verts.toFinset ∪ Hi.verts.toFinset)) ∩ (I.toFinset ∪ K2.C.verts.toFinset)).card *
    (2 * μ * 4 ^ k * h ^ 2):=by
  ring_nf
