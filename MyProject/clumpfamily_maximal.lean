import MyProject

import MyProject.clumpfamily_joining
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


lemma Clump_family_max
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(hDecompose: Clump_Decomposition L KFam)
(hNarrow: Clump_family_narrow KFam)
(hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L )
: ∃ (KFam2: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam2
∧ Clump_family_narrow KFam2
∧ Clump_family_separated KFam2

:=by
let S: Set ℕ :={n| ∃ (KFam2: Finset (Clump G p m κ pr h)), KFam2.card = n ∧ Clump_Decomposition L KFam2
∧ Clump_family_narrow KFam2}
have S_nonemp: S.Nonempty:=by
  refine Set.nonempty_def.mpr ?_
  use KFam.card
  dsimp [S]
  use KFam

let n: ℕ := Nat.find S_nonemp
have hn_in_S: n∈ S:=by
  dsimp [n]
  apply Nat.find_spec S_nonemp


dsimp [S] at hn_in_S
rcases hn_in_S with ⟨KFam2, hKFam2⟩
use KFam2
constructor
exact hKFam2.2.1
constructor
exact hKFam2.2.2

have h_n_minimal: ∀ (n': ℕ),  n' ∈  S→ n'≥ n:=by
  intro n'
  intro n'inS
  dsimp [n]
  exact Nat.find_min' S_nonemp n'inS

by_contra hUnseparated
have hF3_exist: ∃ (KFam3: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam3
∧ KFam3.card< KFam2.card
∧ Clump_family_narrow KFam3:=by
  apply Clump_family_improvement L KFam2
  repeat assumption
  exact hKFam2.2.1--
  exact hUnseparated
  exact hKFam2.2.2
  repeat assumption--
rcases hF3_exist with ⟨KFam3, hKFam3⟩
let n': ℕ := KFam3.card
have n'inS: n' ∈ S:=by
  dsimp [S]
  use KFam3
  constructor
  exact rfl
  constructor
  exact hKFam3.1
  exact hKFam3.2.2
have h_n'_min: n'≥ n:=by
  exact h_n_minimal n' n'inS


have n_eq_F2_card: n = KFam2.card:=by
  exact hKFam2.1.symm



have hcont: n' < n:=by
  dsimp[ n']
  rw[n_eq_F2_card]
  exact hKFam3.2.1
have h': ¬ n' < n:= by exact Nat.not_lt.mpr (h_n_minimal n' n'inS)
exact h' hcont





lemma Initial_Clump_Decomposition_narrow
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
:
∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam∧ Clump_family_narrow KFam
:= by
let KFam: Finset (Clump G p m κ pr h):=Finset.image (Clump_forming_L nan) L.H
have hKFam: KFam= Finset.image (Clump_forming_L nan) L.H:= by exact rfl
use KFam
constructor
apply Initial_Clump_Decomposition_1
repeat assumption


lemma Clump_decomposition_of_locally_dense
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
(hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L )
: ∃ (KFam2: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam2
∧ Clump_family_narrow KFam2
∧ Clump_family_separated KFam2
:=by

let KFam_ex:∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam:= by
  apply Initial_Clump_Decomposition
  repeat assumption
rcases KFam_ex with ⟨KFam, hKFam⟩
exact Clump_family_max L KFam hKFam hKFam.2 hNoWideClumps

/-lemma Initial_Clump_Decomposition
(L: Locally_Dense G p m h)
(nan: Clump G p m κ pr h)
:
∃ (KFam: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam
:= by-/
/-
lemma Clump_family_improvement
(L: Locally_Dense G p m h)
(KFam: Finset (Clump G p m κ pr h))
(hDecompose: Clump_Decomposition L KFam)
(hUnSeparated: ¬ Clump_family_separated KFam)
(hNarrow: Clump_family_narrow KFam)
(hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L )
: ∃ (KFam2: Finset (Clump G p m κ pr h)),
Clump_Decomposition L KFam2
∧ KFam2.card< KFam.card
∧ Clump_family_narrow KFam2
-/
