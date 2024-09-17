--import MyProject

import hyperstabilityES.lemmas.clump_flowers
 --import hyperstabilityES.lemmas.SimpleGraph
set_option linter.unusedVariables false
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
variable (p m κ pr h γ α : ℕ)
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (hI:Inhabited (Clump G p m κ pr h))





lemma Order_family
(KFam: Finset (Clump G p m κ pr h))
(no_dense_sets: ¬ family_contains_dense_list p m κ pr h α hI KFam  )
:
∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧
(Li.Nodup)∧
(clump_list_sparse_up_to_n p m κ pr h α hI (KFam.card) Li )
:=by

let Li0: List (Clump G p m κ pr h):= KFam.toList

let S: Set ℕ:={n:ℕ | ∃ (Li: List (Clump G p m κ pr h)),
 (Li.toFinset= KFam)∧
   (Li.Nodup)
    ∧ (clump_list_sparse_up_to_n p m κ pr h α hI (n) Li  )}

have hNonemp:0∈ S:=by
    use Li0
    constructor
    exact toList_toFinset KFam
    constructor
    exact nodup_toList KFam
    unfold clump_list_sparse_up_to_n
    intro i hi
    by_contra
    exact Nat.not_succ_le_zero i hi

have SNonempty: S.Nonempty:=by
    exact Set.nonempty_of_mem hNonemp


by_cases hcase: ∃ (n: ℕ ), n∈ S ∧ n≥ KFam.card

rcases hcase with ⟨n, hS, hn⟩
dsimp [S] at hS
rcases hS with ⟨Li, hLi, hLi2, hLi3⟩
use Li
constructor
exact hLi
constructor
exact hLi2
unfold clump_list_sparse_up_to_n
intro  i hi
unfold clump_list_sparse_up_to_n at hLi3
have h1: i< n:= by
   calc
    i< KFam.card:=by exact hi
    _≤ n:=by exact hn
apply hLi3 i  h1
push_neg at hcase
have hbdd: BddAbove S:=by
    use KFam.card-1
    intro x hx
    exact Nat.le_sub_one_of_lt (hcase x hx)


let n:ℕ :=sSup  S

have hn: n∈ S:=by
    apply Nat.sSup_mem
    exact SNonempty
    exact hbdd

have n_l_KFam: n<KFam.card:=by
    exact hcase n hn
dsimp [S] at hn
rcases hn with ⟨Li, hLi, hLi2, hLi3⟩

have Lilen_eq_Kfam: Li.length= KFam.card:=by
    rw[← hLi]
    exact (List.toFinset_card_of_nodup hLi2).symm
have Li'_ex:∃ (Li': List (Clump G p m κ pr h)),
(Li'.toFinset= KFam)∧
(Li'.Nodup)∧
(clump_list_sparse_up_to_n p m κ pr h α hI (n+1) Li' )
:=by
    apply Order_family_induction_step
    repeat assumption
    rw[Lilen_eq_Kfam]
    repeat assumption

have n_plus_one_mem_S: n+1∈ S:=by
    dsimp [S]
    exact Li'_ex

by_contra hcont
dsimp[n] at n_plus_one_mem_S
simp at n_plus_one_mem_S
have h1: sSup S + 1 ≤ sSup S:=by
    exact ConditionallyCompleteLattice.le_csSup S (sSup S + 1) hbdd Li'_ex
have h2: ¬(sSup S + 1 ≤ sSup S):=by
    simp

#check bipartite_induce
exact h2 h1
/-
lemma Order_family_induction_step
(n: ℕ )
(KFam: Finset (Clump G p m κ pr h))
(Li: List (Clump G p m κ pr h))
(heqFam: Li.toFinset= KFam)
(hNoDup: Li.Nodup)
(hn: n< Li.length)
(dense_up_to_n:  clump_list_sparse_up_to_n p m κ pr h α hI n Li  )
(no_dense_sets: ¬ family_contains_dense_list p m κ pr h α hI KFam  )
:
∃ (Li': List (Clump G p m κ pr h)),
(Li'.toFinset= KFam)∧
(Li'.Nodup)∧
(clump_list_sparse_up_to_n p m κ pr h α hI (n+1) Li' )
:=by-/

--#check bipartite_induce
