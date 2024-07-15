import MyProject

import MyProject.clumps_Bset
import MyProject.clumps_Bset_improved

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
variable {p m κ pr h : ℕ}
variable (prggp: pr≫ p)
variable (mggpr: m≫ pr)
variable (mPositive: m>0)
variable (pPositive: p>0)
variable (κPositive: κ>0)




lemma clump_M_contained_in_C
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
:(sSup ↑K.M:Subgraph G).verts ⊆ K.C.verts:= by

sorry


lemma clump_BcapC_order_at_least_Hi
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi: Subgraph G)
(hHi: Hi∈ K.H)
: 2*p*(Hi.verts ∩ (K.C).verts).toFinset.card≥  Hi.verts.toFinset.card:= by
calc
2*p*(Hi.verts ∩ (K.C).verts).toFinset.card≥
2*p*(Hi.verts ∩ (sSup K.M: Subgraph G).verts).toFinset.card:=by
  gcongr
  have h1: (Hi.verts ∩ (sSup ↑K.M:Subgraph G).verts) ⊆ (Hi.verts ∩ K.C.verts):= by
    gcongr
    exact clump_M_contained_in_C
  exact Set.toFinset_subset_toFinset.mpr h1
_≥ Hi.verts.toFinset.card:= by
  exact clump_BcapM_order_improved pPositive Hi hHi

lemma clump_BcapC_order_at_least_m
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
(Hi: Subgraph G)
(hHi: Hi∈ K.H)
: 2*p*(Hi.verts ∩ (K.C).verts).toFinset.card≥  m:= by
calc
2*p*(Hi.verts ∩ (K.C).verts).toFinset.card≥  Hi.verts.toFinset.card:=by
  exact clump_BcapC_order_at_least_Hi pPositive Hi hHi
_≥ m:= by
  apply K.H_Order
  exact hHi


lemma card_positive_implies_nonempty_finset
{S: Finset V}
(hS: S.card>0)
: S≠ ∅:= by
by_contra h
have h1: S.card=0:= by exact card_eq_zero.mpr h
have h2: S.card≠ 0:= by exact Ne.symm (Nat.ne_of_lt hS)
exact h2 h1

lemma card_positive_implies_nonempty_set
{S: Set V}
(hS: S.toFinset.card>0)
: S≠ ∅:= by
have h:(S.toFinset)≠ ∅ :=by
  apply card_positive_implies_nonempty_finset
  exact hS
by_contra h1
have h2: S.toFinset=∅ := by exact Set.toFinset_eq_empty.mpr h1
exact h h2
/- More complicated numbers---------------------
lemma clump_add_B_vertices_cut_dense
{K: Clump G p m κ pm }
{Hi: Subgraph G}
{q:ℕ }
(hq: q = 4 * κ ^ (100 * K.k).factorial * (K.C.verts ∪ Hi.verts).toFinset.card / (K.C.verts ∩ Hi.verts).toFinset.card + 1)
(hHi: Hi∈ K.H):
cut_dense G (K.C⊔ Hi) q := by
intro A B hUnion
have h1: 2*p*(Hi.verts ∩ (K.C).verts).toFinset.card≥  m:= by
  exact clump_BcapC_order Hi hHi
#check cut_dense_union
apply cut_dense_union G  K.C Hi (κ^(Nat.factorial (100*(K.k)))) q

-- (G.cut_dense K.C (κ ^ (100 * K.k).factorial))
apply K.C_Cut_Dense

--G.cut_dense Hi (κ ^ (100 * K.k).factorial)
apply Cut_Dense_monotone p
-- p ≤ κ ^ (100 * K.k).factorial
sorry
apply K.H_Cut_Dense
exact hHi

--q = 4 * κ ^ (100 * K.k).factorial * (K.C.verts ∪ Hi.verts).toFinset.card / (K.C.verts ∩ Hi.verts).toFinset.card + 1
exact hq

--K.C.verts ∩ Hi.verts ≠ ∅
have h2:  2*p*(Hi.verts ∩ (K.C).verts).toFinset.card>0:=by
  calc
  2*p*(Hi.verts ∩ (K.C).verts).toFinset.card
  ≥ m:= by
    exact h1--gcongr
  _>0:= by
    exact mPositive--m>0


have h2: (Hi.verts ∩ (K.C).verts).toFinset.card>0:= by
  exact Nat.pos_of_mul_pos_left h2
have h2: (Hi.verts ∩ (K.C).verts) ≠ ∅ := by
  apply card_positive_implies_nonempty_set
  simp
  simp at h2
  exact h2
have h3: Hi.verts ∩ K.C.verts=K.C.verts ∩ Hi.verts:= by
  exact Set.inter_comm Hi.verts K.C.verts
rw[h3.symm]
exact h2

exact hUnion
-------------------------/






lemma clump_add_Hi_cut_dense
{K: Clump G p m κ pm h}
{Hi: Subgraph G}
{q:ℕ }
--more precise version:(hq: q ≥ 16*(κ^(Nat.factorial (100*K.k)))*(4*p*h*4^(K.k)))
(hq: q ≥ 16*(κ^(2*Nat.factorial (100*K.k))))
(hHi: Hi∈ K.H):
cut_dense G (K.C⊔ Hi) q := by
--intro A B hUnion
have h1: 2*p*(Hi.verts ∩ (K.C).verts).toFinset.card≥  m:= by
  exact clump_BcapC_order_at_least_m pPositive Hi hHi
#check cut_dense_union_simplified
apply cut_dense_union_simplified (κ^(Nat.factorial (100*K.k))) q (4*p*h*4^(K.k)) --G  K.C Hi (κ^(Nat.factorial (100*(K.k)))) q


-- (G.cut_dense K.C (κ ^ (100 * K.k).factorial))
apply K.C_Cut_Dense

--G.cut_dense Hi (κ ^ (100 * K.k).factorial)
apply Cut_Dense_monotone G p
-- p ≤ κ ^ (100 * K.k).factorial
sorry
apply K.H_Cut_Dense
exact hHi

--q = 4 * κ ^ (100 * K.k).factorial * (K.C.verts ∪ Hi.verts).toFinset.card / (K.C.verts ∩ Hi.verts).toFinset.card + 1
calc
  q ≥ 16*(κ^(2*Nat.factorial (100*K.k))):= by exact hq
  _= 16*(κ^(Nat.factorial (100*K.k)+Nat.factorial (100*K.k))):= by
    congr
    ring_nf
  _= 16*((κ^(Nat.factorial (100*K.k)))*(κ^(Nat.factorial (100*K.k)))):= by
    congr
    exact Nat.pow_add κ (100 * K.k).factorial (100 * K.k).factorial
  _≥ 16 * ((κ ^ (100 * K.k).factorial) * (4 * p *h* 4 ^ K.k)):=by
    gcongr
    sorry
  _=16 * κ ^ (100 * K.k).factorial * (4 * p * h*4 ^ K.k):= by
    ring_nf



--κ ^ (100 * K.k).factorial > 0
exact Nat.pos_pow_of_pos (100 * K.k).factorial κPositive
--K.C.verts ∩ Hi.verts ≠ ∅
have h2:  2*p*(Hi.verts ∩ (K.C).verts).toFinset.card>0:=by
  calc
  2*p*(Hi.verts ∩ (K.C).verts).toFinset.card
  ≥ m:= by
    exact h1--gcongr
  _>0:= by
    exact mPositive--m>0



have h2: (Hi.verts ∩ (K.C).verts).toFinset.card>0:= by
  exact Nat.pos_of_mul_pos_left h2
have h2: (Hi.verts ∩ (K.C).verts) ≠ ∅ := by
  apply card_positive_implies_nonempty_set
  simp
  simp at h2
  exact h2
have h3: Hi.verts ∩ K.C.verts=K.C.verts ∩ Hi.verts:= by
  exact Set.inter_comm Hi.verts K.C.verts

rw[h3.symm]
exact Set.nonempty_iff_ne_empty.mpr h2
calc
(K.C.verts ∪ Hi.verts).toFinset.card =
((K.C.verts).toFinset∪ (Hi.verts).toFinset).card:= by
  congr
  exact Set.toFinset_union K.C.verts Hi.verts
_≤ (K.C.verts).toFinset.card+ (Hi.verts).toFinset.card:= by
  exact card_union_le K.C.verts.toFinset Hi.verts.toFinset
_≤ (K.C.verts).toFinset.card+  2*p*( Hi.verts∩ K.C.verts).toFinset.card:=by
  gcongr
  exact clump_BcapC_order_at_least_Hi pPositive Hi hHi
_≤ m*h*4^K.k+  2*p*( Hi.verts∩ K.C.verts).toFinset.card:=by
  gcongr
  exact K.C_Order
_≤ (2*p*( Hi.verts∩ K.C.verts).toFinset.card)*h*4^K.k+  2*p*( Hi.verts∩ K.C.verts).toFinset.card:=by
  gcongr
_= (2*p*( Hi.verts∩ K.C.verts).toFinset.card)*h*4^K.k+  2*p*( Hi.verts∩ K.C.verts).toFinset.card*1:=by
  ring_nf
_≤ (2*p*( Hi.verts∩ K.C.verts).toFinset.card)*h*4^K.k+  2*p*( Hi.verts∩ K.C.verts).toFinset.card*(h*4^K.k):= by
  gcongr
  -- 1 ≤ h * 4 ^ K.k
  sorry

_= (K.C.verts ∩ Hi.verts).toFinset.card * (4 * p *h* 4 ^ K.k):=by
  have h33:K.C.verts ∩ Hi.verts= Hi.verts∩ K.C.verts:= by exact    Set.inter_comm K.C.verts Hi.verts
  simp_rw[h33]
  ring_nf
  