--import MyProject

import hyperstabilityES.lemmas.clumps_connected_combine
 --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false

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




lemma two_clump_add_Hi_and_I_cut_dense_better
{K1 K2: Clump G p m κ pr h}
{Hi: Subgraph G}
{q μ k:ℕ }
{I: Set V}
(hHi: Hi∈ K1.H∪ K2.H)
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
:cut_dense G (K1.Gr.induce (I∪ K1.C.verts)⊔ K2.Gr.induce (I∪ K2.C.verts)⊔ Hi) q := by
by_cases hcase:Hi∈ K1.H
have h1: cut_dense G (K1.Gr.induce (I∪ K1.C.verts)⊔ Hi⊔ K2.Gr.induce (I∪ K2.C.verts)) q:=by
  apply two_clump_add_Hi_and_I_cut_dense
  repeat assumption

have h2: (K1.Gr.induce (I∪ K1.C.verts)⊔ Hi⊔ K2.Gr.induce (I∪ K2.C.verts))=(K1.Gr.induce (I∪ K1.C.verts)⊔ K2.Gr.induce (I∪ K2.C.verts)⊔ Hi):=by
  exact sup_right_comm (K1.Gr.induce (I ∪ K1.C.verts)) Hi (K2.Gr.induce (I ∪ K2.C.verts))

rw [h2.symm]
exact h1

have h': Hi∈ K2.H:=by
  rw [mem_union] at hHi
  exact hHi.resolve_left hcase

have hI:  I⊆ BSetPlusM K2∩ BSetPlusM K1:=by
  rw [@Set.inter_comm]
  exact hI


have h3:_:=by
  exact      two_clump_add_Hi_and_I_cut_dense κPositive pPositive mPositive hPositive prPositive iSub h' μbiggerthanp
     hk2biggerthank hk1biggerthank qDef hI Iorder Iorderupperbound pLarge mggpr prggp hggp κggh mggμ


have h2: (K2.Gr.induce (I ∪ K2.C.verts) ⊔ Hi ⊔ K1.Gr.induce (I ∪ K1.C.verts))=(K1.Gr.induce (I∪ K1.C.verts)⊔ K2.Gr.induce (I∪ K2.C.verts)⊔ Hi):=by
  rw [sup_right_comm]
  rw [sup_comm (K1.Gr.induce (I ∪ K1.C.verts)) (K2.Gr.induce (I ∪ K2.C.verts))]

rw [h2.symm]
exact h3




lemma induction_clump_add_Hi_and_I_cut_dense
{K1 K2: Clump G p m κ pr h}
--{HFam: Finset (Subgraph G)}
{μ t k:ℕ }
{I: Set V}

(μbiggerthanp: μ ≥ κ)
(hk1biggerthank: K1.k ≤  k)
(hk2biggerthank: K2.k ≤  k)
(hI: I⊆ BSetPlusM K1∩ BSetPlusM K2)
(Iorder: μ *I.toFinset.card≥ m)
(Iorderupperbound: 4*pr*I.toFinset.card≤ m)
(pLarge: p≥ 20)
(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ pr)
(κggh: κ ≥ gg1 h)
(mggμ: m≥ μ )
:
(HFam: Finset (Subgraph G))→(hHisize: HFam.card=t+1)→(hHi: HFam⊆  K1.H∪ K2.H)→
(q:ℕ )→ (qDef: q ≥  (κ^(7*(t+1)*Nat.factorial (100*k)))*μ^(4*(t+1)*(t+1)*k))→
cut_dense G ((K1.Gr.induce (I∪ K1.C.verts)⊔ K2.Gr.induce (I∪ K2.C.verts))⊔ (sSup HFam: Subgraph G)) q:= by
induction' (t) with t hInd
intro HFam hHisize hHi q qDef

have h1: ∃ (Hi:G.Subgraph), HFam={Hi}:=by
  exact card_eq_one.mp hHisize
rcases h1 with ⟨Hi, hHi2⟩
have h2: (sSup HFam: Subgraph G)=Hi:=by
  rw [hHi2]
  simp
rw [h2]

apply two_clump_add_Hi_and_I_cut_dense_better κPositive pPositive mPositive hPositive prPositive _ _ _ hk1biggerthank _ _
repeat assumption
have h4: Hi∈ HFam:=by
  rw[hHi2]
  exact mem_singleton.mpr rfl
exact hHi h4
repeat assumption
calc
  q ≥ κ ^ (7 * (0 + 1) * (100 * k).factorial) * μ ^ (4 * (0 + 1)*(0 + 1)*k):=by
    exact qDef
  _=κ ^ (7 * (100 * k).factorial) * μ ^ (4*k):=by
    ring_nf
  _≥  κ ^ (7 * (100 * k).factorial) * μ ^ 2:=by
    gcongr
    calc
      μ ≥ κ := by exact μbiggerthanp
      _≥ 1:= by exact κPositive
    calc
      4*k≥ 4*1:= by
        gcongr
        calc
          k≥ K1.k:=by assumption
          _≥ 1:= by
            refine Nat.succ_le_of_lt ?h
            exact K1.Nonemptyness
      _= 4:= by ring_nf
      _≥ 2:= by simp




----Induction step:----
intro HFam hHisize hHi

have h1: HFam.card >0:=by
  rw [hHisize]
  exact Nat.zero_lt_succ (t + 1)
have h2: ∃ (Hi:G.Subgraph), Hi∈ HFam:=by
  exact Multiset.card_pos_iff_exists_mem.mp h1
rcases h2 with ⟨Hi, hHi2⟩

let HFam2: Finset G.Subgraph:= HFam.erase Hi
have hHFam2_prop: HFam2=HFam\{Hi}:= by
  exact erase_eq HFam Hi

have HFam2_size: HFam2.card=t+1:=by
  rw [card_erase_of_mem hHi2, hHisize]
  exact rfl

let q1:ℕ :=κ ^ (7 * (t + 1) * (100 * k).factorial) * μ ^ (4 * (t + 1)*(t + 1)*k)

have hFam2_cut_dense: G.cut_dense (K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ sSup ↑HFam2) q1:=by
  apply hInd
  assumption
  exact (erase_subset_iff_of_mem (hHi hHi2)).mpr hHi
  --assumption
  exact Nat.le_refl (κ ^ (7 * (t + 1) * (100 * k).factorial) * μ ^ (4 * (t + 1) * (t + 1) * k))

let q2: ℕ := κ ^ (7  * (100 * k).factorial) * μ ^ 2
have hHi_Cut_Dense: G.cut_dense (K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ Hi) q2:= by
  apply two_clump_add_Hi_and_I_cut_dense_better κPositive pPositive mPositive hPositive prPositive _ _ μbiggerthanp hk1biggerthank _ _
  repeat assumption
  exact hHi hHi2
  repeat assumption
  exact Nat.le_refl (κ ^ (7 * (100 * k).factorial) * μ ^ 2)



have hFam2plusHieqFam1: (sSup ↑HFam2:Subgraph G)⊔ Hi=(sSup ↑HFam:Subgraph G):= by
  have h1: HFam2∪ {Hi}=HFam:= by
    rw[hHFam2_prop]
    apply sdiff_union_of_subset
    exact singleton_subset_iff.mpr hHi2
  have h2: Hi=(sSup {Hi}:Subgraph G):=by
    simp
  rw[h2]
  have h3:_:=by exact union_of_twograph_families h1.symm
  rw[h3.symm]
  simp

have hsubgrapheq: (K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ (sSup ↑HFam:Subgraph G))=(K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ (sSup ↑HFam2:Subgraph G))⊔  (K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ Hi):= by
  rw[←sup_assoc]
  rw[←sup_assoc]
  symm
  rw[sup_comm _ Hi]
  rw[sup_comm _ (sSup ↑HFam2: Subgraph G)]
  repeat rw[←sup_assoc]
  rw[sup_comm Hi _]
  rw[hFam2plusHieqFam1]
  rw[sup_comm _ (sSup ↑HFam: Subgraph G)]
  have h77:_:=by exact three_graph_sup (K1.Gr.induce (I ∪ K1.C.verts)) (K2.Gr.induce (I ∪ K2.C.verts)) (sSup ↑HFam: Subgraph G)
  rw[h77]
  exact sup_assoc (sSup ↑HFam:Subgraph G) (K1.Gr.induce (I ∪ K1.C.verts)) (K2.Gr.induce (I ∪ K2.C.verts))

rw[hsubgrapheq]

have μPositive:μ >0:= by
  calc
    μ ≥ κ := by assumption
    _>0:= by exact κPositive
have kPositive: k≥ 1:=by
        calc
          k≥ K1.k:=by assumption
          _≥ 1:= by
            refine Nat.succ_le_of_lt ?h
            exact K1.Nonemptyness



intro q3 q3Def
-----------????????????

apply cut_dense_union_simplified q1 q3 (μ^(4*(t+1)*k))
exact hFam2_cut_dense
--apply Cut_Dense_monotone


have q1_bigger_q2: q1≥ q2:= by
  calc
    q1=κ ^ (7 * (t + 1) * (100 * k).factorial) * μ ^ (4 * (t + 1)*(t + 1)*k):=by
      exact rfl
    _≥ κ ^ (7 * (0 + 1) * (100 * k).factorial) * μ ^ (4 * (0 + 1)*(0 + 1)*k):=by
      gcongr
      exact κPositive
      exact Nat.zero_le t
      --μ>0
      assumption
      exact Nat.zero_le t
      exact Nat.zero_le t
    _=κ ^ (7  * (100 * k).factorial) * μ ^ (4 *k):=by
      ring_nf
    _≥ κ ^ (7  * (100 * k).factorial) * μ ^ 2:=by
        gcongr
        --μ>0
        assumption
        --2 ≤ 4 * k
        calc
          4*k≥ 4*1:= by
            gcongr

          _= 4:= by ring_nf
          _≥ 2:= by simp

    _=q2:=by
      exact rfl

#check Cut_Dense_monotone
apply Cut_Dense_monotone _ _ q1_bigger_q2
exact hHi_Cut_Dense

--q3 ≥ 16 * q1 * μ ^ (4 * t * k)
calc
  q3 ≥ κ ^ (7 * (t + 1 + 1) * (100 * k).factorial) * μ ^ (4 * (t + 1 + 1) * (t + 1 + 1) * k):=by
    exact q3Def
  _=κ ^ (7 * (t + 2) * (100 * k).factorial) * μ ^ (4 * (t + 1) * (t + 1) * k)*μ ^ (4 * (2*t + 3) * k):=by
    ring_nf
  _≥ (κ ^ (7 * (t + 1) * (100 * k).factorial) * μ ^ (4 * (t + 1) * (t + 1) * k))* (μ ^ (4 * (t+1) * k)*16):=by
    gcongr
    exact κPositive
    exact NeZero.one_le
    --μ ^ (4 * t * k) * 16 ≤ μ ^ (4 * (2 * t + 3) * k)
    calc
      μ ^ (4 * (2 * t + 3) * k)
      =μ ^ (8 * (t+1)*k + 4*k):= by
        ring_nf
      _≥ μ ^ (4 * (t+1)*k + 1*1):= by
        gcongr
        repeat assumption
        repeat simp
        --
      _=μ ^ (4 * (t+1)*k + 1):= by
        ring_nf
      _=μ ^ (4 * (t+1)*k)*μ := by
        exact rfl
      _≥ μ ^ (4 * (t+1) * k) * 16:= by
        gcongr
        calc
          μ ≥ κ := by assumption
          _≥ gg1 h:= by assumption
          _≥ 10000:= by
            apply gg1_large
            repeat assumption
          _≥ 16:= by simp
  _= 16*(κ ^ (7 * (t + 1) * (100 * k).factorial) * μ ^ (4 * (t + 1) * (t + 1) * k))* μ ^ (4 * (t+1) * k):=by
    ring_nf
  _=16 * q1 * μ ^ (4 * (t+1) * k):= by
    ring_nf

  --_= 16 * q1 * μ ^ (4 * t * k):=by
  --  ring_nf


--q1 > 0
dsimp[q1]
repeat apply mul_pos
exact Nat.pos_pow_of_pos (7 * (t + 1) * (100 * k).factorial) κPositive
apply Nat.pos_pow_of_pos
assumption


--((K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ sSup ↑HFam2).verts ∩
  --  (K1.Gr.induce (I ∪ K1.C.verts) ⊔ K2.Gr.induce (I ∪ K2.C.verts) ⊔ Hi).verts).Nonempty
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
have h22: I ⊆ (I ∪ K1.C.verts ∪ (I ∪ K2.C.verts) ∪ ⋃ G' ∈ HFam2, G'.verts)  := by
  repeat rw[Set.union_assoc]
  apply Set.subset_union_left

have h33: I ⊆ ( (I ∪ K1.C.verts ∪ (I ∪ K2.C.verts) ∪ Hi.verts)):= by
  repeat rw[Set.union_assoc]
  apply Set.subset_union_left
refine Set.inter_nonempty.mpr ?hNonemptyIntersection.a
let x:=hInonemp2.some
use x
have xinI:x∈ I:= by
  exact Set.Nonempty.some_mem hInonemp2
constructor
exact h22 xinI
exact h33 xinI



have C1bound: K1.C.verts.toFinset.card≤ m*h*4^k:=by
  calc
    K1.C.verts.toFinset.card≤ m*h*4^K1.k:=by
      exact K1.C_Order
    _≤ m*h*4^k:=by
      gcongr
      exact NeZero.one_le

have C2bound: K2.C.verts.toFinset.card≤ m*h*4^k:=by
  calc
    K2.C.verts.toFinset.card≤ m*h*4^K2.k:=by
      exact K2.C_Order
    _≤ m*h*4^k:=by
      gcongr
      exact NeZero.one_le

have HiBound: Hi.verts.toFinset.card ≤ h*m:=by
  by_cases h:Hi∈ K1.H
  apply K1.H_Order_Upper_Bound
  exact h
  have h': Hi∈ K2.H:=by
    have h''': Hi∈ K1.H∪ K2.H:=by
      exact hHi hHi2
    rw [mem_union] at h'''
    exact h'''.resolve_left h
  apply K2.H_Order_Upper_Bound
  exact h'


have Hunionbound: (⋃ G' ∈ HFam2, G'.verts).toFinset.card ≤ (t+1)*(h*m):=by
  apply biunion_max_bound2 (h*m) (t+1)
  exact Nat.le_of_eq HFam2_size
  have hHi2New: HFam2 ⊆  K1.H∪ K2.H:= by
      calc
        HFam2 ⊆ HFam:=by exact erase_subset Hi HFam
        _⊆ K1.H∪ K2.H:=by
          exact hHi
  intro Hi hHi
  by_cases h:Hi∈ K1.H
  apply K1.H_Order_Upper_Bound
  exact h
  have h': Hi∈ K2.H:=by
    have h''': Hi∈ K1.H∪ K2.H:=by
      exact hHi2New hHi
    rw [mem_union] at h'''
    exact h'''.resolve_left h
  apply K2.H_Order_Upper_Bound
  exact h'

simp
repeat   rw[←union_assoc]
have μh: μ ≥ h:= by
  calc
          μ ≥ κ :=by assumption
          _≥ h:= by
            apply gg1_ge
            repeat assumption

calc
(I.toFinset ∪ K1.C.verts.toFinset ∪ I.toFinset ∪ K2.C.verts.toFinset ∪ (⋃ G' ∈ HFam2, G'.verts).toFinset ∪ I.toFinset ∪K1.C.verts.toFinset ∪I.toFinset ∪K2.C.verts.toFinset ∪ Hi.verts.toFinset).card
_≤ (I.toFinset).card + (K1.C.verts.toFinset).card + (I.toFinset).card + (K2.C.verts.toFinset).card + (⋃ G' ∈ HFam2, G'.verts).toFinset.card + I.toFinset.card +K1.C.verts.toFinset.card +I.toFinset.card +K2.C.verts.toFinset.card + Hi.verts.toFinset.card:=by
  exact
    card_union_10 I.toFinset K1.C.verts.toFinset I.toFinset K2.C.verts.toFinset
      (⋃ G' ∈ HFam2, G'.verts).toFinset I.toFinset K1.C.verts.toFinset I.toFinset
      K2.C.verts.toFinset Hi.verts.toFinset
_≤ (I.toFinset).card + m*h*4^k + (I.toFinset).card + m*h*4^k + (t+1)*(h*m) + I.toFinset.card +m*h*4^k +I.toFinset.card +m*h*4^k + h*m:= by
  gcongr
_=(I.toFinset).card*4+ m*h*4^k*4 + (t+2)*h*m:= by
  ring_nf
_≤ (I.toFinset).card*4+ (μ * I.toFinset.card)*h*4^k*4 + (t+2)*h*(μ * I.toFinset.card):= by
  gcongr
_=(I.toFinset).card*(4+4*μ*h*4^k+(t+2)*h*μ):= by
  ring_nf
_≤ (I.toFinset).card*μ^(4*(t+1)*k):= by
  gcongr
  --4 + 4 * μ * 4 ^ k + (t + 2) * h * μ ≤ μ ^ (4 * t * k)
  calc
    μ ^ (4 * (t+1) * k)
    =
    μ ^ (3 * (t+1) * k+(t+1) * k):= by
      ring_nf
    _≥μ ^ (3 * 1 * 1+(t+1) * k):= by
      gcongr
      repeat assumption; simp


      --
    _=μ ^ (3 +(t+1) * k):=by
      ring_nf
    _=μ^3 * μ ^ ((t+1) * k):= by
      exact Nat.pow_add μ 3 ((t+1) * k)
    _=μ *μ *μ *μ ^ ((t+1) * k):=by
      ring_nf
    _≥ 11*μ*μ *μ ^ ((t+1) * k):= by
      gcongr
      calc
        μ ≥ κ :=by assumption
        _≥ gg1 h:= by assumption
        _≥ 10000:= by
          apply gg1_large
          assumption
        _≥ _:= by simp
      --
    _=
    4*μ*μ *μ ^ ((t+1) * k)
    +4*μ*μ *μ ^ ((t+1) * k)
    +1*μ*μ *μ ^ ((t+1) * k)
    +2*μ*μ *μ ^ ((t+1) * k):= by
      ring_nf
    _≥
    4*1*1 *1
    +4*μ*h *4 ^ ((t+1) * k)
    +1*h*μ *2 ^ ((t+1) * k)
    +2*h*μ *1 ^ ((t+1) * k):= by
      gcongr
      repeat exact μPositive; --assumption; simp
      apply Nat.pos_pow_of_pos
      exact μPositive
      calc
        μ ≥ κ :=by assumption
        _≥ gg1 h:= by assumption
        _≥ 10000:= by
          apply gg1_large
          assumption
        _≥ _:= by simp
      calc
        μ ≥ κ :=by assumption
        _≥ gg1 h:= by assumption
        _≥ 10000:= by
          apply gg1_large
          assumption
        _≥ _:= by simp

      exact μPositive
      --
    _≥
    4*1*1 *1
    +4*μ*h *4 ^ (1 * k)
    +1*h*μ *2 ^ (t * 1)
    +2*h*μ *1 ^ ((t+1) * k):= by
      gcongr
      repeat simp

      --
    _=
    4
    +4 * μ * h * 4 ^ k
    +h*μ *2 ^ t
    +2*h*μ:= by
      ring_nf
    _≥
    4
    +4 * μ * h * 4 ^ k
    +h*μ *t
    +2*h*μ:= by
      gcongr
      exact bernoulli_inequality t
      --
    _=
    4
    + 4 * μ * h * 4 ^ k
    + (t + 2) * h * μ:= by
      ring_nf


_≤  ((I.toFinset ∪ K1.C.verts.toFinset ∪ I.toFinset ∪ K2.C.verts.toFinset ∪ (⋃ G' ∈ HFam2, G'.verts).toFinset) ∩(I.toFinset ∪ K1.C.verts.toFinset ∪ I.toFinset ∪ K2.C.verts.toFinset ∪ Hi.verts.toFinset)).card *(μ^(4*(t+1)*k)):= by
  gcongr
  simp
