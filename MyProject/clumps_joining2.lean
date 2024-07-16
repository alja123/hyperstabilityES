import MyProject

import MyProject.clumps_joining
 --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h: ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}




lemma  joining_numbers1
{x b:ℕ }
(hb: x *b≥  m)
--(Iorder: (κ^(10*Nat.factorial (100*k))) *I.toFinset.card≥  m)
--(Iorderupperbound: 4*pr*I.toFinset.card≤ m)
:
∃ (n:ℕ ),(n≤ b)∧ (x *n≥  m) ∧ (x*n< m+x)
:=by
let S: Set ℕ:= {n:ℕ| x *n≥  m}
have SNonempty: Set.Nonempty S:=by
  sorry
let n:ℕ := Nat.find SNonempty
have h1: n∈ S:=by
  dsimp [n]
  apply Nat.find_spec SNonempty


dsimp [S] at h1

use n
constructor
dsimp [n]
#check Nat.find_min'
apply Nat.find_min' SNonempty
dsimp[S]
exact hb

constructor
exact h1

by_contra h
simp at h
let n':ℕ := n-1
have h2: x *n'≥  m:=by
  calc
    x*n' = x*(n-1):= by exact rfl
    _= x*n-x*1:= by exact Nat.mul_sub_left_distrib x n 1
    _= x*n-x:= by ring_nf
    _≥ m:=by exact Nat.le_sub_of_add_le h

have h4: n'<n:=by
  refine Nat.sub_one_lt_of_le ?h₀ ?h₁
  --n>0
  sorry
  exact Nat.find_mono fun n a ↦ a
have h3: ¬ (x *n'≥  m):=by
  apply Nat.find_min SNonempty
  exact h4
exact h3 h2


lemma  joining_numbers2
{x y b:ℕ }
(hb: x *b≥  m)
(hxy: y≤ x/2)
(hxb: m≥ x*x)
(xPositive: x>0)
--(Iorder: (κ^(10*Nat.factorial (100*k))) *I.toFinset.card≥  m)
--(Iorderupperbound: 4*pr*I.toFinset.card≤ m)
:
∃ (n:ℕ ),(n≤ b)∧ (x *n≥  m) ∧ (y*n≤ m)
:=by
have h1: ∃ (n:ℕ ),(n≤ b)∧ (x *n≥  m) ∧ (x*n< m+x)
:= by exact joining_numbers1 hb
rcases  h1 with ⟨n, hn, h1, h2⟩
use n
constructor
exact hn
constructor
exact h1
calc
 y * n ≤ (x/2)*n:= by gcongr
  _≤ (x-1)*n:= by
    gcongr;
    refine Nat.le_sub_one_of_lt ?bc.a
    refine Nat.bitwise_rec_lemma ?bc.a.hNe
    exact Nat.not_eq_zero_of_lt xPositive
  _= x*n-n:= by exact (subtract_one_mult x n).symm
  _≤ m+x-n:= by gcongr;
  _≤ m:=by
    refine Nat.sub_le_iff_le_add.mpr ?_
    gcongr
    by_contra h
    have hc:x*x>m:=by
      calc
        x*x > x*n:= by gcongr; exact Nat.gt_of_not_le h
        _≥ m:= by exact h1
    have h3:¬ (x * x > m):=by exact Nat.not_lt.mpr hxb
    exact h3 hc
    --refine Nat.sub_le_iff_le_add'.mpr ?_




lemma clump_joining
{K1 K2: Clump G p m κ pr h}
--{HFam: Finset (Subgraph G)}
{k:ℕ }
 --(μbiggerthanp: μ ≥ κ)
(hk1biggerthank: K1.k =   k)
(hk2biggerthank: K2.k ≤  k)
(hedge_disjoint: HEdge_Disjoint (K1.H ∪ K2.H))
(hIntersection: (κ^(10*Nat.factorial (100*k)))*(BSet K1∩ BSet K2).toFinset.card≥ m )
--(Iorder: (κ^(10*Nat.factorial (100*k))) *I.toFinset.card≥  m)
--(Iorderupperbound: 4*pr*I.toFinset.card≤ m)
--(qDef: q ≥  (κ^(Nat.factorial (100*k+4))))
:
∃ (K: Clump G p m κ pr h),
(K.Gr=K1.Gr⊔ K2.Gr)∧
(K.H=K1.H∪ K2.H)∧
(K.k≥ k)∧
(K.k≤ K1.k+K2.k):=by


let q:ℕ :=  (κ^(Nat.factorial (100*k+4)))
have qDef: q ≥  (κ^(Nat.factorial (100*k+4))):= by
  exact Nat.le_refl (κ ^ (100 * k + 4).factorial)

have h1: ∃ (n:ℕ ),(n≤ (BSet K1∩ BSet K2).toFinset.card)∧ ((κ^(10*Nat.factorial (100*k))) *n≥  m) ∧ (( 4*pr)*n≤ m):=by
  apply joining_numbers2 hIntersection
  --4 * pr ≤ κ ^ (10 * (100 * k).factorial) / 2
  sorry
  --m ≥ κ ^ (10 * (100 * k).factorial) * κ ^ (10 * (100 * k).factorial)
  sorry
  exact Nat.pos_pow_of_pos (10 * (100 * k).factorial) κPositive

rcases h1 with ⟨n, hn, h1, h2⟩

have h3: ∃ (I: Finset V), I⊆ (BSet K1∩ BSet K2).toFinset∧ I.card=n:=by
  exact exists_smaller_set (BSet K1 ∩ BSet K2).toFinset n hn

rcases h3 with ⟨Ifin, hIfin⟩
have h4: Ifin ⊆ (BSet K1 ∩ BSet K2).toFinset:=by
  exact hIfin.left
let I: Set V:= Ifin
have hI : I⊆ (BSet K1∩ BSet K2):= by
  exact Set.subset_toFinset.mp h4
have hIOrd: I.toFinset.card=n:=by
  calc
    I.toFinset.card = Ifin.card:= by simp
    _=n:= by exact hIfin.right
have hIorder: (κ^(10*Nat.factorial (100*k))) *I.toFinset.card≥  m:=by
  calc
  (κ^(10*Nat.factorial (100*k))) *I.toFinset.card=(κ^(10*Nat.factorial (100*k))) *n:= by
    congr
  _≥  m:=by exact h1

have hIorderupperbound: 4*pr*I.toFinset.card≤ m:=by
  calc
    4*pr*I.toFinset.card= 4*pr*n:= by congr
    _≤ m:= by exact h2

apply clump_joining_1
repeat assumption
simp
simp at hIorder
exact hIorder
repeat assumption
simp
simp at hIorderupperbound
exact hIorderupperbound
repeat assumption






 lemma clump_joining_max
{K1 K2: Clump G p m κ pr h} 
(hedge_disjoint: HEdge_Disjoint (K1.H ∪ K2.H))
(hIntersection: (κ^(10*Nat.factorial (100*(Nat.max K1.k K2.k))))*(BSet K1∩ BSet K2).toFinset.card≥ m )
:
∃ (K: Clump G p m κ pr h),
(K.Gr=K1.Gr⊔ K2.Gr)∧
(K.H=K1.H∪ K2.H)∧
(K.k≥ (Nat.max K1.k K2.k))∧
(K.k≤ K1.k+K2.k)
:=by

let k:ℕ := Nat.max K1.k K2.k

have hK1:K1.k≤ k:= by exact Nat.le_max_left K1.k K2.k
have hK2:K2.k≤ k:= by exact Nat.le_max_right K1.k K2.k

by_cases hc: K2.k ≤  K1.k
have h1: K1.k = k:= by
  dsimp [k]
  dsimp[k] at hK1
  exact (Nat.max_eq_left hc).symm
apply clump_joining h1 hK2 hedge_disjoint hIntersection
repeat assumption


have h2: K2.k = k:= by
  dsimp [k]
  refine (Nat.max_eq_right ?h).symm
  exact Nat.le_of_not_ge hc


have hedge_disjoint : HEdge_Disjoint (K2.H ∪ K1.H):=by
  rw[Finset.union_comm K2.H K1.H]
  exact hedge_disjoint

simp_rw[Set.inter_comm (BSet K1) (BSet K2)] at hIntersection
have hk:k=K1.k.max K2.k:= by exact rfl
rw[hk.symm]

have h0: ∃(K: Clump G p m κ pr h), K.Gr = K2.Gr ⊔ K1.Gr ∧ K.H = K2.H ∪ K1.H ∧ K.k ≥ k ∧ K.k ≤ K2.k + K1.k:=by
  apply clump_joining h2 hK1 hedge_disjoint hIntersection
  repeat assumption

rcases h0 with ⟨K, hK1, hK2, hK3, hK4⟩

use K
constructor
rw[hK1]
exact sup_comm K2.Gr K1.Gr
constructor
rw[hK2]
exact union_comm K2.H K1.H
constructor
exact hK3
calc
  K.k ≤ K2.k + K1.k:= by exact hK4
  _= K1.k + K2.k:= by ring_nf
