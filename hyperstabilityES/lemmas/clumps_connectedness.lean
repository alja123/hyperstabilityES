--import MyProject

import hyperstabilityES.lemmas.clumps_basics
import hyperstabilityES.lemmas.clumps_3basics
 --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false

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
--variable (prggp: pr≫ p)
--variable (mggpr: m≫ pr)


lemma clump_M_nonempty
{K: Clump G p m κ pr h}
: K.M.Nonempty := by
have h1:K.M.card>0:= by
  rw[K.M_Size]
  exact K.Nonemptyness
exact card_pos.mp h1

lemma M_graphs_nonempty
{K: Clump G p m κ pr h}
{M: Subgraph G}
(mggpr: m≥ gg1 pr)
(prPositive: pr>0)
(hM: M ∈ K.M)
: M.verts.toFinset.Nonempty := by

have h0: MNear_Regular K.M m pr:= by
  exact K.M_Near_Regular
unfold MNear_Regular at h0
have h1: near_regular M m pr:= by
  apply h0
  exact hM
unfold near_regular at h1
have h2: M.verts.toFinset.card > 0:= by
  apply near_regular_nonempty
  repeat assumption


exact card_pos.mp h2

lemma subgraph_subgraph_of_induced
{K H: Subgraph G}
(hHK: H≤ K)
: H≤K.induce (H.verts):= by
have h1:H.induce (H.verts)≤  K.induce (H.verts):= by
  exact Subgraph.induce_mono hHK fun ⦃a⦄ a ↦ a
have h2: H.induce (H.verts)=H:=by
  exact Subgraph.induce_self_verts
calc
H=H.induce (H.verts):= by exact h2.symm
_≤ K.induce (H.verts):= by exact h1

lemma subgraph_subgraph_of_induced_on_larger_set
{K H: Subgraph G}
{S: Set V}
(hS: H.verts ⊆ S)
(hHK: H≤ K)
: H≤K.induce S:= by
have h1:H.induce (H.verts)≤  K.induce (H.verts):= by
  exact Subgraph.induce_mono hHK fun ⦃a⦄ a ↦ a
have h2: H.induce (H.verts)=H:=by
  exact Subgraph.induce_self_verts
calc
H=H.induce (H.verts):= by exact h2.symm
_≤ K.induce (H.verts):= by exact h1
_≤ K.induce S:= by exact Subgraph.induce_mono_right hS


lemma clump_C_has_verts
{K: Clump G p m κ pr h}
(mggpr: m≥ gg1 pr)
(prPositive: pr>0)
: K.C.verts.toFinset.Nonempty := by
have hNonempM: K.M.Nonempty := by exact clump_M_nonempty
have hex: ∃ (M : Subgraph G), M ∈ K.M := by
  exact hNonempM
rcases hex with ⟨M, hM⟩
have h1: M ≤ K.C := by
  apply  K.M_In_C
  exact hM
have h2: M.verts.toFinset.Nonempty := by
  apply M_graphs_nonempty
  repeat assumption
have h3: M.verts.toFinset ⊆ K.C.verts.toFinset := by
  exact subgraphs_vertex_subsets G M K.C h1
exact Nonempty.mono h3 h2

lemma clump_C_has_verts_Set
{K: Clump G p m κ pr h}
(mggpr: m≥ gg1 pr)
(prPositive: pr>0)
: Nonempty (↑K.C.verts:Set V)
:= by
have hNonemptyC: K.C.verts.toFinset.Nonempty := by
  apply clump_C_has_verts
  repeat assumption
by_contra h
have hCempty: K.C.verts = ∅:= by
  exact Set.not_nonempty_iff_eq_empty'.mp h
have hCempty2: K.C.verts.toFinset = ∅:= by
  exact Set.toFinset_eq_empty.mpr hCempty
rw[hCempty2] at hNonemptyC
have h3:¬ ((∅:Finset V).Nonempty):= by exact Finset.not_nonempty_empty
exact h3 hNonemptyC


lemma M_verts_contained_in_C_verts
{K: Clump G p m κ pr h}
{M: Subgraph G}
(hM: M ∈ K.M)
: M.verts.toFinset ⊆ K.C.verts.toFinset := by
refine subgraphs_vertex_subsets G M K.C ?hHK
apply K.M_In_C
exact hM

lemma M_verts_contained_in_C_verts_set
{K: Clump G p m κ pr h}
{M: Subgraph G}
(hM: M ∈ K.M)
: M.verts ⊆ K.C.verts := by
apply subgraphs_vertex_sets_subsets
apply K.M_In_C
exact hM

lemma M_order_lower_bound
{K: Clump G p m κ pr h}
{M: Subgraph G}
(hM: M ∈ K.M)
:  M.verts.toFinset.card ≥ m/pr := by
have h1: MNear_Regular K.M m pr:= by
  exact K.M_Near_Regular
unfold MNear_Regular at h1
have h2: near_regular M m pr:= by
  apply h1
  exact hM
exact near_regular_vertices_lower_bound h2


lemma C_order_lower_bound
{K: Clump G p m κ pr h}
:  K.C.verts.toFinset.card ≥ m/pr := by
have h1: K.M.Nonempty:= by exact clump_M_nonempty
have hex: ∃ (M : Subgraph G), M ∈ K.M := by
  exact h1
rcases hex with ⟨M, hM⟩

have h4:  M.verts.toFinset⊆ K.C.verts.toFinset:= by
  exact M_verts_contained_in_C_verts hM
calc
K.C.verts.toFinset.card ≥ M.verts.toFinset.card:= by
  exact card_le_card h4
_≥ m/pr:= by
  exact M_order_lower_bound hM






lemma q_simplified_bound
{K: Clump G p m κ pm h }
{I: Set V}
{μ q:ℕ }
(IorderUpperBound: I.toFinset.card≤  K.C.verts.toFinset.card)
(μbig: μ ≥ 2*p)
(qDef: q = 4 * (κ^(Nat.factorial (100*K.k))) * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2 + 1)
(mggpr: m≥ gg1 pm)
(prPositive: pm>0)
: q≤ 32 * (κ^(Nat.factorial (100*K.k))) * μ := by
have μPositive: μ > 0 := by calc
  μ ≥ 2*p:= by exact μbig
  _>0:= by exact Nat.succ_mul_pos 1 pPositive



have h1: (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ≥  K.C.verts.toFinset.card:= by
  gcongr
  refine Set.toFinset_subset_toFinset.mpr ?_
  apply subgraphs_vertex_sets_subsets
  refine subgraph_subgraph_of_induced_on_larger_set ?_ ?_
  exact Set.subset_union_right I K.C.verts
  exact K.C_In_K

have h2: (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card^2 ≥  K.C.verts.toFinset.card^2:= by
  exact Nat.pow_le_pow_of_le_left h1 2

have h3: 0 < K.C.verts.toFinset.card ^ 2:= by
  refine Nat.pos_pow_of_pos 2 ?h
  refine card_pos.mpr ?h.a
  apply clump_C_has_verts
  repeat assumption



have h4: (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card≤ 2*K.C.verts.toFinset.card:=by
  calc
   (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card
  = (I ∪ K.C.verts).toFinset.card:= by
    simp
  _= (I.toFinset ∪ K.C.verts.toFinset).card:= by
    simp
  _≤ I.toFinset.card + K.C.verts.toFinset.card:= by
    exact card_union_le I.toFinset K.C.verts.toFinset
  _≤ K.C.verts.toFinset.card + K.C.verts.toFinset.card:= by
    gcongr
  _= 2*K.C.verts.toFinset.card:=by
    ring_nf


calc
q
= 4 * (κ^(Nat.factorial (100*K.k))) * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2 + 1:=by
  exact qDef

_≤ 4 * (κ^(Nat.factorial (100*K.k))) * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2*2:= by
  have h1: 4 * (κ^(Nat.factorial (100*K.k))) * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2>0:= by
    --apply mul_pos
    #check Nat.div_pos
    apply Nat.div_pos _ h3
    calc
      K.C.verts.toFinset.card ^ 2
      ≤ (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2:=by
        exact h2
      _≤ 4 * κ ^ (100 * K.k).factorial * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2:= by
       apply Nat.le_mul_of_pos_left
       apply mul_pos
       apply mul_pos
       exact Nat.zero_lt_succ 3
       exact Nat.pos_pow_of_pos (100 * K.k).factorial κPositive
       exact μPositive
    --exact Nat.zero_lt_two
  apply plus_one_leq_than_double
  exact h1
_≤ 4*4* (κ^(Nat.factorial (100*K.k))) * μ *2:= by
  gcongr
  refine Nat.div_le_of_le_mul' ?bc.h
  calc
  4 * κ ^ (100 * K.k).factorial * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2
  =(K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 * (4 * κ ^ (100 * K.k).factorial * μ):=
    by ring_nf
  _=4 * κ ^ (100 * K.k).factorial * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card:=
    by ring_nf
  _≤ 4 * κ ^ (100 * K.k).factorial * μ * ( 2*K.C.verts.toFinset.card) * (2* K.C.verts.toFinset.card):=by
    gcongr
  _=  K.C.verts.toFinset.card ^ 2 * (4*4 * κ ^ (100 * K.k).factorial * μ):= by
    ring_nf
_= 32 * (κ^(Nat.factorial (100*K.k))) * μ:= by
  ring_nf

lemma clump_add_B_vertices_cut_dense
{K: Clump G p m κ pm h }
{I: Set V}
{μ q:ℕ }
(μbiggerthanp: μ ≥ 2*p)
(qDef: q = 4 * (κ^(Nat.factorial (100*K.k))) * (μ*h*4^(K.k)) * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2 + 1)
(hI: I⊆ BSet K)
--(Iorder: μ *I.toFinset.card≥ m)
(mggpr: m≥ gg1 pm)
(prPositive: pm>0)
(hPositive: h>0)
:
cut_dense G (K.Gr.induce (I∪ K.C.verts)) q := by

have μPositive: μ > 0 := by calc
  μ ≥ 2*p:= by exact μbiggerthanp
  _>0:= by exact Nat.succ_mul_pos 1 pPositive
have μPositive: (μ*h*4^(K.k)) > 0 := by
  apply mul_pos
  apply mul_pos
  exact μPositive
  --h>0
  exact hPositive
  exact Fin.size_pos'

let Ccd:ℕ := (κ^(Nat.factorial (100*K.k)))
--intro A B hUnion
#check cut_dense_add_vertices
apply cut_dense_add_vertices G K.C (K.Gr.induce (I∪ K.C.verts)) _ Ccd (μ*h*4^(K.k)) q

exact K.C_Cut_Dense
--*****K.C ≤ K.Gr.induce (I ∪ K.C.verts)
refine subgraph_subgraph_of_induced_on_larger_set ?KContainsH.hS ?KContainsH.hHK
exact Set.subset_union_right I K.C.verts
exact K.C_In_K
--Ccd ≥ 1
exact Nat.one_le_pow (100 * K.k).factorial κ κPositive
--μ ≥ 1
exact μPositive
--K.C.verts.toFinset.Nonempty
apply clump_C_has_verts
repeat assumption

intro v hv
have hBv: v ∈ BSet K := by
  have h1: (K.Gr.induce (I ∪ K.C.verts)).verts=I ∪ K.C.verts:=by
    exact rfl
  have h2: (I ∪ K.C.verts)\ (K.C.verts)⊆ I:= by
    refine Set.diff_subset_iff.mpr ?_
    have h3: I ∪ K.C.verts = K.C.verts ∪ I:= by exact Set.union_comm I K.C.verts
    exact Eq.subset h3
  have h2:(I ∪ K.C.verts)\ (K.C.verts)⊆ BSet K:= by
    exact fun ⦃a⦄ a_1 ↦ hI (h2 a_1)
  exact h2 hv



have hbv2:v ∈ (K.Gr).verts∧ (((K.Gr.neighborSet v)∩ (sSup K.M: Subgraph G).verts).toFinset.card*p*2 ≥ m):= by
  unfold BSet at hBv
  exact hBv

have hMinC: (sSup ↑K.M:Subgraph G).verts⊆ K.C.verts := by
  have h1: (sSup ↑K.M:Subgraph G)≤  K.C:= by
    apply M_sub_C

  exact @subgraphs_vertex_sets_subsets V G (sSup K.M) K.C  h1
have h2: (K.Gr.neighborSet v ∩ (I∪ K.C.verts): Set V)=((K.Gr.induce (I ∪ K.C.verts)).neighborSet v: Set V):= by
  ext x
  constructor
  intro h
  simp at h
  simp
  constructor
  have h11: v∈ (K.Gr.induce (I ∪ K.C.verts)).verts:=by
    exact Set.mem_of_mem_diff hv
  have h11: v∈ I ∪ K.C.verts:= by
    exact h11
  exact h11
  constructor
  exact h.2
  exact h.1
  intro hx2
  simp at hx2
  simp
  constructor
  exact hx2.2.2
  exact hx2.2.1


have h3: (K.Gr.neighborSet v) ∩ ((sSup ↑K.M: Subgraph G).verts)⊆ (K.Gr.neighborSet v) ∩ ((K.C).verts)
:= by exact Set.inter_subset_inter (fun ⦃a⦄ a ↦ a) hMinC


simp_rw[h2.symm]
have hBv': v ∈ K.Gr.verts ∧ (K.Gr.neighborSet v ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2 ≥ m:= by
 --unfold BSet at hBv
 exact hBv
have hBv22: (K.Gr.neighborSet v ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2 ≥ m:= by
  exact hBv'.2
-- μ * ((K.Gr.neighborSet v ∩ K.C.verts).toFinset ∩ K.C.verts.toFinset).card ≥ K.C.verts.toFinset.card
calc
  K.C.verts.toFinset.card
  ≤ m* h*4^(K.k):=by
    exact K.C_Order
  _≤ ((K.Gr.neighborSet v ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card * p * 2)* h*4^(K.k):=by
    gcongr
  _=((p * 2)* h*4^(K.k))*((K.Gr.neighborSet v ∩ (sSup ↑K.M: Subgraph G).verts).toFinset.card):=by
    ring_nf
  _≤ μ * h*4 ^ K.k * ((K.Gr.neighborSet v ∩ (I ∪ K.C.verts)).toFinset ∩ K.C.verts.toFinset).card   := by
    gcongr
    --p * 2 ≤ μ
    rw[mul_comm]
    exact μbiggerthanp
    --(K.Gr.neighborSet v ∩ (sSup ↑K.M).verts).toFinset ⊆ (K.Gr.neighborSet v ∩ (I ∪ K.C.verts)).toFinset ∩ K.C.verts.toFinset
    let M:=(sSup ↑K.M: Subgraph G).verts
    let C:=K.C.verts
    have hM1: M=(sSup ↑K.M: Subgraph G).verts:= by exact rfl
    have hC1: C=K.C.verts:= by exact rfl
    have hcont1: M⊆ C:= by
      dsimp[M, C]
      exact hMinC
    simp_rw[hM1.symm, hC1.symm]
    rw [← @Set.toFinset_inter]
    rw [@Set.toFinset_subset_toFinset]
    simp
    constructor
    calc
      K.Gr.neighborSet v ∩ M
      ⊆ M:= by exact Set.inter_subset_right (K.Gr.neighborSet v) M
      _⊆ C:= by exact hcont1
      _⊆ I ∪ C:= by exact Set.subset_union_right I C
    calc
      K.Gr.neighborSet v ∩ M ⊆
      M:= by exact Set.inter_subset_right (K.Gr.neighborSet v) M
      _⊆ C:= by exact hcont1





--q = 4 * Ccd * μ * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2 + 1

rw[qDef]


--Nonempty ↑K.C.verts
apply clump_C_has_verts_Set
repeat assumption





lemma clump_add_B_vertices_cut_dense_simplified
{K: Clump G p m κ pm h}
{I: Set V}
{q:ℕ }
(μ : ℕ)
(μbiggerthanp: μ ≥ 2*p)
(qDef: q ≥  32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h)
(hI: I⊆ BSet K)
--(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I.toFinset.card≤ K.C.verts.toFinset.card)
(mggpr: m≥ gg1 pm)
(prPositive: pm>0)
(hPositive: h>0)
(κlarge: κ≥ 4)
:
--Could have alternative I≤ m
cut_dense G (K.Gr.induce (I∪ K.C.verts)) q := by
let q':ℕ := 4 * (κ^(Nat.factorial (100*K.k))) * (μ*h*4^(K.k)) * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2 + 1
have h1: cut_dense G (K.Gr.induce (I∪ K.C.verts)) q':= by
  apply clump_add_B_vertices_cut_dense
  exact κPositive
  exact pPositive
  exact μbiggerthanp
  exact rfl
  exact hI
  --exact Iorder
  repeat assumption
#check Cut_Dense_monotone
apply Cut_Dense_monotone _ _ _ h1
calc
q'= 4 * (κ^(Nat.factorial (100*K.k))) * (μ*h*4^(K.k)) * (K.Gr.induce (I ∪ K.C.verts)).verts.toFinset.card ^ 2 / K.C.verts.toFinset.card ^ 2 + 1:= by
  exact rfl
_≤ 32 * (κ^(Nat.factorial (100*K.k))) * (μ*h*4^(K.k)):= by
  apply q_simplified_bound
  exact κPositive
  exact pPositive
  exact Iorderupperbound
  calc
    μ * h*4 ^ K.k≥ μ*1:=by
      gcongr
      refine Nat.le_mul_of_pos_right μ ?h₁.h
      --h>0
      exact hPositive
      exact Nat.one_le_pow' K.k 3
    _=μ := by
      ring_nf
    _≥ 2*p:= by exact μbiggerthanp
  exact rfl
  repeat assumption
_≤ 32 * (κ^(Nat.factorial (100*K.k))) * (μ*h*(κ^(Nat.factorial (100*K.k)))):= by
  gcongr

  --4 ^ K.k ≤ κ ^ (100 * K.k).factorial
  calc
    4 ^ K.k ≤κ^(K.k):= by
      gcongr
    _≤ κ^(100*K.k).factorial:= by
      gcongr
      exact κPositive
      calc
        (100 * K.k).factorial≥(100 * K.k):= by exact Nat.self_le_factorial (100 * K.k)
        _≥ 1*K.k:= by
          gcongr
          simp
        _=K.k:= by ring_nf

_= 32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h:= by
  ring_nf
_≤  q:= by
  exact qDef




lemma clump_M_contained_in_C
--{p m κ pr : ℕ}
{K: Clump G p m κ pr h}
:(sSup ↑K.M:Subgraph G).verts ⊆ K.C.verts:= by
apply subgraphs_vertex_sets_subsets G
simp
intro M hM
apply K.M_In_C
assumption



lemma clump_add_BSetPlusM_vertices_cut_dense_simplified
{K: Clump G p m κ pm h}
{I': Set V}
{q:ℕ }
(μ : ℕ)
(μbiggerthanp: μ ≥ 2*p)
(qDef: q ≥  32 * (κ^(2*Nat.factorial (100*K.k))) * μ*h)
(hI': I'⊆ BSetPlusM K)
--(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: I'.toFinset.card≤ K.C.verts.toFinset.card)
(mggpr: m≥ gg1 pm)
(prPositive: pm>0)
(hPositive: h>0)
(κlarge: κ≥ 4)
:
cut_dense G (K.Gr.induce (I'∪ K.C.verts)) q := by

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

apply clump_add_B_vertices_cut_dense_simplified
repeat assumption
calc
    _ =  I.toFinset.card:= by
      dsimp [I]
      simp
    _≤ _:= by exact Iorderupperbound
    _= _:= by simp
repeat assumption
