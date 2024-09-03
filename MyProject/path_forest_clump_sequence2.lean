import MyProject

import MyProject.path_forests_clump_sequence_preparation
import MyProject.forest_join_rotate
--import MyProject.path_forest_clump_sequence
--C:\Users\alja1\Downloads\pro\my_project\MyProject\path_forests_clump_sequence_preparation.lean
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats  200000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}



/-structure ClumpPathSequence
 (β : ℕ )(KFam: Finset (Clump G p m κ pr h)) where
  (Ord: List (Clump G p m κ pr h))
  (Ord_eq_KFam: Ord.toFinset⊆  KFam)
  (LM: List (Subgraph G))
  (LM_in_M: M_list_in_clump_list iI LM Ord)
  (LM_Sparse: family_sparse β m (LM.toFinset) )
  (Ver: List V)
  (VerNoDup: Ver.Nodup)
  (VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
  (hlength: Ord.length ≥  h*pr)
  (hlengthM: LM.length=Ord.length)
  (hlengthVer: Ver.length=Ord.length-1)
  --(LM_NoDup: LM.Nodup)
-/



lemma get_rotate_tail
(L: List V)
(i: ℕ )
(hi: i< L.length-1)
:
(L.rotate 1).get! i=L.tail.get! i
:= by
sorry

lemma get_take_tail
(L: List V)
(i k: ℕ )
(hi: i< k-1)
:
(List.take k L).tail.get! i= L.tail.get! i
:= by
sorry

lemma Path_forest_ends_contained
(F : PathForest iV iSP H)
:
{v:V| v∈ F.E.take F.k}⊆ Path_forest_support iV iSP F
:= by
sorry
--used
lemma set_disjoint_to_internal_disjoint_reverse_taildisj_symm2_tailaligned2
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S.rotate 1)
(F2SNodup: F2.E.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(j i: ℕ ), (j< k)→ (i<k)→ j≠ i+1→  (tail_disjoint_imp  (F2.P.get! j) (F1.P.get! i))
:= by
sorry

--used
lemma path_forest_avoids_monotone!
{H: Subgraph G}
{F2: PathForest iV iSP H}
{k k': ℕ }
{Fb: Set V}
(hav:Path_forest_avoids! iV iSP F2 Fb (k))
(le: k'≤ k)

:
(Path_forest_avoids! iV iSP F2 Fb (k'))
:=by
  unfold Path_forest_avoids!
  intro i hi
  apply hav
  calc
    i < k':= by exact hi
    _≤ k:= by exact le


lemma disjoint_1_rotate
{L K: List V}
(hdis: L.Disjoint K)
:
L.Disjoint (K.rotate 1)
:= by
refine List.disjoint_left.mpr ?_
intro a ha
simp
exact hdis ha


lemma clump_path_sequence_gives_path2
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV α KFam)
(k: ℕ )
(kLarge: k>2)
(Ord_length: Seq.Ord.length>k+8)
(Ord_length_upper: Seq.Ord.length≤ 4*k+100)
(ineq1: 8 * γ *(82 * γ * k+2*k)≤ m/(2*pr))
(ineq2: 2 * (k + 4) + (4*k+100) + 2≤  m / pr)
(LM_in_H:∀ i < k , Seq.LM.get! i ≤ H)
(prllγ :pr≤ γ)
:
∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  (k*m)

--Has_length_d_path (Clump_Family_Union KFam) (h*m)
:=by

have kPositive: k>0:= by exact Nat.zero_lt_of_lt kLarge
have Ord_length3: Seq.Ord.length>k+1:= by
  calc
    Seq.Ord.length>k+8:= by exact Ord_length
    _>k+1:= by gcongr; exact Nat.one_lt_succ_succ 6

have Ord_length4: Seq.Ord.length>k+3:= by
  calc
    Seq.Ord.length>k+8:= by exact Ord_length
    _>k+3:= by gcongr; exact Nat.lt_of_sub_eq_succ rfl

have Ord_length5: Seq.Ord.length>k+4:= by
  calc
    Seq.Ord.length>k+8:= by exact Ord_length
    _>k+4:= by gcongr; exact Nat.lt_of_sub_eq_succ rfl



have Ord_length2: Seq.Ord.length>k:= by
  exact Nat.lt_of_succ_lt Ord_length3


have LM_length4: Seq.LM.length>k+4:= by
  rw[Seq.hlengthM]
  exact Ord_length5

have LM_length3: Seq.LM.length>k+3:= by
  rw[Seq.hlengthM]
  exact Ord_length4

have LM_length2: Seq.LM.length>k+1:= by
  rw[Seq.hlengthM]
  exact Ord_length3

have LM_length: Seq.LM.length>k:= by
  rw[Seq.hlengthM]
  exact Ord_length2

have Ver_length2: Seq.Ver.length> k+2:= by
  rw[Seq.hlengthVer]
  exact Nat.lt_sub_of_add_lt Ord_length4
have Ver_length1: Seq.Ver.length> k+1:= by
  exact Nat.lt_of_succ_lt Ver_length2
have Ver_length: Seq.Ver.length> k:= by
  rw[Seq.hlengthVer]
  exact Nat.lt_sub_of_add_lt Ord_length3
have LM_length_ge: Seq.LM.length≥ k:= by
  exact Nat.le_of_succ_le LM_length
have LM_length_ge2: Seq.LM.length≥ k+4:= by
  exact LM_length3
have Ord_length_ge2: Seq.Ord.length≥ k+4:= by
  exact Ord_length4
have Ord_length_ge: Seq.Ord.length≥ k:= by
  exact Nat.le_of_succ_le Ord_length2
have Ver_length_ge: Seq.Ver.length≥ k:= by
  exact Nat.le_of_succ_le Ver_length


have ex_pairs: _:= by
  apply find_pairs_in_M_list iI iV iSub Seq.Ord Seq.Ver Seq.LM Seq.LM_in_M (k+4)
  exact LM_length_ge2
  exact Ord_length_ge2
  --2 * k + Seq.Ver.length + 2 ≤ m / pr
  rw[Seq.hlengthVer]
  calc
    _≤ 2 * (k + 4) + (Seq.Ord.length) + 2:= by
      gcongr
      simp
    _≤ 2 * (k + 4) + (4*k+100) + 2:= by
      gcongr
    _≤  m / pr:= by
      exact ineq2

  --

rcases ex_pairs with ⟨S, E, hS, hE, hSE, hSVer, hEVer, hSNoDup, hENoDup, hSInLM, hEInLM⟩


have ex_HS:_:=by
  apply add_Ver_to_M_list_starts_alt iI iV iSub H Seq.Ord Seq.Ver S Seq.LM Seq.LM_in_M Seq.VerInOrd (k+1)
  intro i hi
  apply hSInLM
  exact Nat.lt_succ_of_lt hi
  exact LM_length3--exact LM_length
  exact Ord_length4--exact Ord_length2
  exact Ver_length2--exact Ver_length
  rw[hS]
  ring_nf
  gcongr
  apply Nat.lt_of_sub_eq_succ;  simp;  exact rfl
  exact γ
  exact κPositive
  exact pPositive
  exact mPositive



have ex_HE:_:=by
  apply add_Ver_to_M_list iI iV iSub  H Seq.Ord Seq.Ver E Seq.LM Seq.LM_in_M Seq.VerInOrd (k+1)
  intro i hi
  apply hEInLM
  calc
    i < k+1:= by exact hi
    _< k+4:= by gcongr; exact Nat.one_lt_succ_succ 2
  exact LM_length2--exact LM_length
  exact Ord_length3--exact Ord_length2
  exact Ver_length1--exact Ver_length
  rw[hE]
  ring_nf
  gcongr
  apply Nat.lt_of_sub_eq_succ;  simp;  exact rfl
  exact γ
  exact κPositive
  exact pPositive
  exact mPositive


rcases ex_HS with ⟨HS, hHS_length, hcutdenseS, hVer_in_HS, hS_in_HS, HSinH⟩

rcases ex_HE with ⟨HE, hHE, hcutdenseE, hVer_in_HE, hE_in_HE, HEinH⟩


let Fb: Set V:= {v: V|v∈ E}

let S':=S.take (k)
let E':=E.take (k)
let Ver':=Seq.Ver.take (k)

have Ver_get_ineq: ∀ (i: ℕ ), i< k+1→i<Seq.Ver.length:= by
  intro i hi
  exact Nat.lt_of_lt_of_le hi Ver_length

have Ver_get: ∀ (i: ℕ ), (hi:i< k+1)→Seq.Ver.get! i=Seq.Ver.get ⟨i, Ver_get_ineq i hi⟩:= by
  intro i hi
  simp
  apply List.getD_eq_get

have Ver_get_in_Ver:∀ (i: ℕ ), (hi:i< k+1)→Seq.Ver.get! i∈ Seq.Ver:= by
  intro i hi
  rw[Ver_get i hi]
  exact List.get_mem Seq.Ver i (Ver_get_ineq i hi)

have Ver_get_in_Ver_set:∀ (i: ℕ ), (hi:i< k+1)→Seq.Ver.get! i∈ {v:V|v∈ Seq.Ver}:= by
  intro i hi
  simp only [Set.mem_setOf_eq]
  apply Ver_get_in_Ver i hi




have S_get_ineq: ∀ (i: ℕ ), i< k+1→i<S.length:= by
  intro i hi
  rw[hS]
  calc
    i < k+1:= by exact hi
    _< k+4:= by gcongr; exact Nat.one_lt_succ_succ 2


have S_get: ∀ (i: ℕ ), (hi:i< k+1)→S.get! i=S.get ⟨i, S_get_ineq i hi⟩:= by
  intro i hi
  simp
  apply List.getD_eq_get

have S_get_in_S:∀ (i: ℕ ), (hi:i< k+1)→S.get! i∈ S:= by
  intro i hi
  rw[S_get i hi]
  exact List.get_mem S i (S_get_ineq i hi)



have Stail_get_ineq: ∀ (i: ℕ ), i< k+1→i<S.tail.length:= by
  intro i hi
  rw [@List.length_tail]
  rw[hS]
  simp
  calc
    i < k+1:= by exact hi
    _< k+3:= by gcongr; exact Nat.one_lt_succ_succ 1

have Stail_get: ∀ (i: ℕ ), (hi:i< k+1)→S.tail.get! i=S.tail.get ⟨i, Stail_get_ineq i hi⟩:= by
  intro i hi
  simp
  apply List.getD_eq_get

have Stail_get_in_Stail:∀ (i: ℕ ), (hi:i< k+1)→S.tail.get! i∈ S.tail:= by
  intro i hi
  rw[Stail_get i hi]
  exact List.get_mem S.tail i (Stail_get_ineq i hi)

have Stail_get_in_S:∀ (i: ℕ ), (hi:i< k+1)→S.tail.get! i∈ S:= by
  intro i hi
  have h1: S.tail⊆ S:=by
    exact List.tail_subset S
  exact h1 (Stail_get_in_Stail i hi)


have Srotate_get_ineq: ∀ (i: ℕ ), i< k→i<(S'.rotate 1).length:= by
  intro i hi
  rw [List.length_rotate]
  dsimp[S']
  simp
  constructor
  exact hi
  rw[hS]
  calc
    i < k:= by exact hi
    _< k+4:= by simp

have Srotate_get: ∀ (i: ℕ ), (hi:i< k)→(S'.rotate 1).get! i=(S'.rotate 1).get ⟨i, Srotate_get_ineq i hi⟩:= by
  intro i hi
  simp
  apply List.getD_eq_get

have Srotate_get_in_S:∀ (i: ℕ ), (hi:i< k)→(S'.rotate 1).get! i∈ S:= by
  intro i hi
  have h1: S'⊆ S:= by
    dsimp[S']
    exact List.take_subset k S
  rw[Srotate_get]
  have h2: (S'.rotate 1).get ⟨i, Srotate_get_ineq i hi⟩∈ {v:V|v∈ (S'.rotate 1)}:= by
    simp only [Set.mem_setOf_eq]
    apply List.get_mem
  simp at h2
  refine h1 h2
  exact hi


have S'Sublist: List.Sublist S' S:= by
    dsimp[S']
    exact List.take_sublist k S
have hS'NoDup: S'.Nodup:= by
    exact List.Nodup.sublist S'Sublist hSNoDup

have E_get_ineq: ∀ (i: ℕ ), i< k+1→i<E.length:= by
  intro i hi
  rw[hE]
  calc
    i < k+1:= by exact hi
    _< k+4:= by gcongr; exact Nat.one_lt_succ_succ 2

have E_get: ∀ (i: ℕ ), (hi:i< k+1)→E.get! i=E.get ⟨i, E_get_ineq i hi⟩:= by
  intro i hi
  simp
  apply List.getD_eq_get

have E_get_in_S:∀ (i: ℕ ), (hi:i< k+1)→E.get! i∈ E:= by
  intro i hi
  rw[E_get i hi]
  exact List.get_mem E i (E_get_ineq i hi)


have LM_get: ∀ (i: ℕ ), (hi:i< k+1)→  (Seq.LM.get! i)∈ (Seq.Ord.get! i).M:= by
    intro i hi
    have hi': i< Seq.Ord.length:= by
      calc
        i< k+1:= by exact hi
        _<  Seq.Ord.length:= by exact Ord_length3

    have h34:_:=by exact Seq.LM_in_M i hi'
    simp
    simp at h34
    have h12: Seq.LM.getD i default=Seq.LM.get ⟨i, ?_⟩ := by
      refine List.getD_eq_get Seq.LM default ?_
    have h13: Seq.LM.getD i ⊥=Seq.LM.get ⟨i, ?_⟩:= by
      refine List.getD_eq_get Seq.LM ⊥ ?_
    rw[h13] at h34
    rw[h12]
    exact h34
    calc
        i< k+1:= by exact hi
        _<  Seq.LM.length:= by exact LM_length2



have hF1Ex: _:= by
  apply path_forest_specified_ends_simplified_prefix iV iSub iSP H Seq.Ver (S'.rotate 1) HS  (k)  m Fb _ _ _ _ _ _ _
  --vertex_list_outside_set iV Seq.Ver Fb (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  dsimp[Fb]
  exact id (List.Disjoint.symm hEVer) (Ver_get_in_Ver i hi)
  --vertex_list_outside_set iV S Fb (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  dsimp[Fb]
  exact hSE (Srotate_get_in_S i hi2)
  --Ver.Nodup
  exact Seq.VerNoDup
  --S.Nodup
  have subl: List.Sublist S.tail S:= by
    exact List.tail_sublist S
  exact List.nodup_rotate.2  hS'NoDup
  --cut_dense
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  apply hcutdenseS _ hi
  --small_intersection_list
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  --simp
  calc
    _
    =
    8 * γ * (Fb ∩ (HS.get! i).verts).toFinset.card + (m + 8 * γ * (2 * (k )))
    :=by
      simp
    _≤
    8 * γ * (Fb).toFinset.card + (m + 8 * γ * (2 * (k ))):= by
      gcongr
      simp
    _≤ 8 * γ * (k+4)+ (m + 8 * γ * (2 * (k ))):= by
      gcongr
      dsimp[Fb]
      have h1: {v | v ∈ E}.toFinset= E.toFinset:= by
        ext v
        simp
      rw[h1]
      simp
      calc
        E.toFinset.card≤  E.length:= by exact List.toFinset_card_le E
        _= k+4:= by exact hE
    _≤ (HS.get! i).verts.toFinset.card:=by sorry

  --exact γPositive
  --vertex_list_in_graph_list iV iSub Seq.Ver HS (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  apply hVer_in_HS i hi
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi2
  rw[get_rotate_tail]
  dsimp[S']
  rw[get_take_tail]
  apply hS_in_HS
  have hi: i< k+1:= by
    calc
      i<k-1:= by exact hi2
      _≤ k+1:= by simp; ring_nf; simp
  exact hi
  exact hi2
  dsimp[S']
  simp
  rw [hS]
  simp
  exact hi2
  --Disjointness
  have h23: S'⊆ S:= by dsimp[S']; exact List.take_subset k S
  apply disjoint_1_rotate
  apply List.disjoint_of_subset_right
  exact h23
  exact hSVer
  --lengths
  exact Ver_length_ge
  simp;  dsimp[S']; simp; rw[hS]; simp
  rw[hHS_length]; simp
  --∀ i < k + 1, HS.get! i ≤ H (add this to lemma giving HS)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  apply HSinH i hi








rcases hF1Ex with ⟨F1, hF1S, hF1E, hF1k, hF1P_length, hF1_avoids, hFcard, S1length, E1length⟩


let Fb2: Set V:= /-{v: V|v∈ S}∪-/ ({v:V| v∈ Path_forest_support iV iSP F1}\ {v: V| v∈ Seq.Ver.take (k)})


have hF2Ex: _:= by
  apply path_forest_specified_ends_simplified_prefix iV iSub iSP H E Seq.Ver HE  k  m Fb2 _ _ _ _ _ _ _
  --vertex_list_outside_set iV Seq.Ver Fb (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  dsimp[Fb2]
  have h43: E.get! i ∉ Path_forest_support iV iSP F1 := by
    unfold Path_forest_avoids! at hF1_avoids
    dsimp [Fb] at hF1_avoids
    unfold Path_forest_support
    rw[path_forest_support_iff_neg iV iSP F1]
    intro j hj

    have hdisj1: Disjoint {v | v ∈ (F1.P.get! j).Pa.Wa.support} {v | v ∈ E}:= by
      apply hF1_avoids j
      rw[hF1P_length.symm]
      exact hj
    have Eget_set:E.get! i∈ {v:V|v∈ E}:= by
      simp only [ Set.mem_setOf_eq]
      exact E_get_in_S i hi
    exact
      set_disjoint_right (E.get! i) {v | v ∈ (F1.P.get! j).Pa.Wa.support} {v | v ∈ E} hdisj1
        (E_get_in_S i hi)
  have h65: Path_forest_support iV iSP F1 \ {v | v ∈ Seq.Ver}⊆ Path_forest_support iV iSP F1 := by
    exact  Set.diff_subset (Path_forest_support iV iSP F1) {v | v ∈ Seq.Ver}
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not]
  intro h99
  exfalso
  exact h43 h99
  --vertex_list_outside_set iV S Fb (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  dsimp[Fb2]
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not]
  intro h99
  rw[Ver_get i hi]
  have hia : i < List.length (Seq.Ver):= by
    calc
      i < k+1:= by exact hi
      _< Seq.Ver.length:= by exact Ver_length1
  rw[ List.get_take (Seq.Ver) hia hi2]
  apply List.get_mem (List.take (k) Seq.Ver) i


  --E.Nodup
  exact hENoDup
  --Ver.Nodup
  exact Seq.VerNoDup

  --cut_dense
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  apply hcutdenseE _ hi
  --small_intersection_list
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  calc
    _
    =
    8 * γ * (Fb2 ∩ (HE.get! i).verts).toFinset.card + (m + 8 * γ * (2 * (k )))
    :=by
      simp
    _≤
    8 * γ * (Fb2).toFinset.card + (m + 8 * γ * (2 * (k ))):= by
      gcongr
      simp
    _≤ 8 * γ * (41 * γ * k)+ (m + 8 * γ * (2 * (k ))):= by
      gcongr
      dsimp[Fb2]
      calc
        (Path_forest_support iV iSP F1 \ {v | v ∈ Seq.Ver.take (k)}).toFinset.card
        ≤ (Path_forest_support iV iSP F1).toFinset.card:=by
          gcongr
          simp
          exact Set.diff_subset (Path_forest_support iV iSP F1) _
        _≤ 41 * γ * k:= by exact hFcard
    _≤ (HE.get! i).verts.toFinset.card:=by sorry

  --exact γPositive
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  apply hE_in_HE i hi
  --vertex_list_in_graph_list iV iSub Seq.Ver HS (k + 1)
  intro i hi2
  have hi: i< k+1:= by
    calc
      i<k-1:= by exact hi2
      _≤ k+1:= by simp; ring_nf; simp
  apply hVer_in_HE i hi
  --Disjointness
  exact hEVer
  --lengths
  rw[hE];  simp
  exact Ver_length_ge
  rw[hHE]; simp
  --∀ i < k + 1, HS.get! i ≤ H (add this to lemma giving HS)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  apply HEinH i hi

rcases hF2Ex with ⟨F2, hF2S, hF2E, hF2k, hF2P_length, hF2_avoids, hF2card, S2lenght, E2length⟩




let Fb3: Set V:=  ({v:V| v∈ Path_forest_support iV iSP F1}∪ {v:V| v∈ Path_forest_support iV iSP F2})\ ({v: V| v∈ (S.take (k))∨ v∈ (E.take (k))})





have hF3Ex: _:= by
  apply long_path_forest_specified_ends_simplified_altnum iV iSub iSP H S E Seq.LM  k  m γ pr Fb3
  --LMSparse
  exact Seq.LM_Sparse
  --LMgeMfamily
  unfold HOrder_ge_m_Family
  intro M hM
  have h123: _:= by exact Seq.LM_in_M
  simp at hM
  unfold M_list_in_clump_list at h123
  have jex: ∃ (j: Fin (Seq.LM.length)), Seq.LM.get j=M:= by
    exact List.mem_iff_get.mp hM
  rcases jex with ⟨j, hj⟩
  have hget!: Seq.LM.getD ↑j ⊥=Seq.LM.get j:= by
    apply List.getD_eq_get
  have h78: M∈  (Seq.Ord.get! j).M:= by
    rw[hj.symm, hget!.symm]
    have h:_:= by exact h123 j
    simp at h
    simp
    apply h
    rw[Seq.hlengthM.symm]
    exact j.isLt
  apply near_regular_vertices_lower_bound
  apply (Seq.Ord.get! ↑j).M_Near_Regular
  apply h78
   -- using lower bound on size of graphs in M here (which is m/pr) currently
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi
  apply hSInLM i;
  calc
    i < k +0:= by simp; exact hi
    _< k + 4:= by gcongr; exact Nat.zero_lt_succ 3
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi
  apply hEInLM i
  calc
    i < k +0:= by simp; exact hi
    _< k + 4:= by gcongr; exact Nat.zero_lt_succ 3
  --Disjointness
  exact hSE
  --lengths
  rw[hS]; simp
  rw[hE]; simp
  exact LM_length_ge
  -- ∀ i < k + 1, Seq.LM.get! i ≤ H
  exact LM_in_H
  --vertex_list_outside_set iV S Fb3 (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  dsimp[Fb3]
  simp only [ Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, not_or, not_and,
    Decidable.not_not]
  intro h99 h87
  have hin: S.get! i ∈   List.take (k ) S:=by
    rw[S_get i hi]
    rw[ List.get_take (S) _ hi2]
    apply List.get_mem (List.take (k) S) i
  exfalso
  exact h87 hin
  --vertex_list_outside_set iV E Fb3 (k + 1)
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  dsimp[Fb3]
  simp only [ Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, not_or, not_and,
    Decidable.not_not]
  intro h99 h87
  rw[E_get i hi]
  rw[ List.get_take (E) _ hi2]
  apply List.get_mem (List.take (k) E) i
  --Snodup
  exact hSNoDup
  --Enodup
  exact hENoDup
  --LMnodup
  exact Seq.LM_NoDup
  --- should be part of path sequence definition
  --cut_dense
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  have h23: (Seq.LM.get! i)∈ (Seq.Ord.get! i).M:= by
    apply LM_get i hi
  --now apply that M graphs are gut dense
  have hcd: G.cut_dense (Seq.LM.get! i) pr:= by
    apply ((Seq.Ord.get! i).M_Near_Regular (Seq.LM.get! i) h23).2
    --

  apply Cut_Dense_monotone
  exact prllγ
  exact hcd
  --

  --small_intersection_list
  intro i hi2
  have hi: i< k+1:= by exact Nat.lt_add_right 1 hi2
  calc
    _
    =
    8 * γ * (Fb3 ∩ (Seq.LM.get!  i).verts).toFinset.card + (m/(2*pr) + 8 * γ * (2 * (k )))
    :=by
      simp
    _≤
    8 * γ * (Fb3).toFinset.card + (m/(2*pr) + 8 * γ * (2 * (k ))):= by
      gcongr
      simp
    _≤ 8 * γ * (82 * γ * k)+ (m/(2*pr) + 8 * γ * (2 * (k ))):= by
      gcongr
      dsimp[Fb3]
      calc
        ((Path_forest_support iV iSP F1 ∪ Path_forest_support iV iSP F2) \ {v | v ∈ (S.take (k)) ∨ v ∈ (E.take (k))}).toFinset.card
        ≤ ((Path_forest_support iV iSP F1 ∪ Path_forest_support iV iSP F2)).toFinset.card:=by
          gcongr
          simp
        _= ((Path_forest_support iV iSP F1).toFinset ∪ (Path_forest_support iV iSP F2).toFinset).card:= by
          congr
          simp
        _≤ (Path_forest_support iV iSP F1).toFinset.card+ (Path_forest_support iV iSP F2).toFinset.card:= by
          exact
            card_union_le (Path_forest_support iV iSP F1).toFinset
              (Path_forest_support iV iSP F2).toFinset

        _≤ 41 * γ * k+41 * γ * k:= by
          gcongr
        _=82 * γ * k:= by ring_nf
    _≤ m/pr:= by
      calc
        8 * γ * (82 * γ * k) + (m / (2 * pr) + 8 * γ * (2 * k))
        =8 * γ *(82 * γ * k+2*k)+(m / (2 * pr) ):= by
          ring_nf
        _≤ (m / (2 * pr) )+(m / (2 * pr) ):= by
          gcongr

        _= 2*(m/(2*pr)):= by ring_nf
        _≤ (2*m)/(2*pr):= by
          exact Nat.mul_div_le_mul_div_assoc 2 m (2 * pr)
        _=(2*m/2/pr):= by
          exact (Nat.div_div_eq_div_mul (2 * m) 2 pr).symm
        _= m / pr:= by
          congr
          rw [Nat.mul_div_cancel_left m (Nat.le.step Nat.le.refl)]

    _≤ (Seq.LM.get! i).verts.toFinset.card:=by
      have h23: (Seq.LM.get! i)∈ (Seq.Ord.get! i).M:= by
        apply LM_get i hi        --now use that M-graphs are big
      apply near_regular_vertices_lower_bound
      apply (Seq.Ord.get! i).M_Near_Regular
      exact h23

  exact γPositive








  --

--rcases hF3Ex with ⟨F3, hF3a, hF3b, hF3c, hF3d, hF3e⟩
rcases hF3Ex with ⟨F3, hF3S, hF3E, hF3k, hF3P_length, hF3_avoids, hF3card, S3length, E3length⟩
/-have F3_ge_k:F3.k≥ k:= by
    calc
    F3.k = k:= by exact hF3k
    _≥ k:= by exact Nat.le_refl k

have F2_ge_k:F2.k≥ k:= by
  calc
    F2.k = k:= by exact hF2k
    _≥ k:= by exact Nat.le_refl k

have F1_ge_k:F1.k≥ k:= by
  calc
    F1.k = k:= by exact hF1k
    _≥ k:= by exact Nat.le_refl k-/

have F3_ge_k:F3.k≥ k-2:= by
    calc
    F3.k = k:= by exact hF3k
    _≥ k-2:= by simp

have F2_ge_k:F2.k≥ k-2:= by
  calc
    F2.k = k:= by exact hF2k
    _≥ k-2:= by simp

have F1_ge_k:F1.k≥ k-2:= by
  calc
    F1.k = k:= by exact hF1k
    _≥ k-2:= by simp


have F2avoids': Path_forest_avoids! iV iSP F1 {v:V|v∈ Path_forest_support iV iSP F2 ∧ v∉ F1.S} k:= by

  apply Fb_disj_symm2
  exact hF1k
  exact hF2k
  rw[hF2E, hF1S]
  exact hF2_avoids
  rw[hF2E]
  dsimp[Fb2]
  ext v; simp
  exact rfl


have Fb3Cont1: {v:V| v∈ Path_forest_support iV iSP F1}\ {v: V| v∈ (S.take (k))}⊆ Fb3:= by
  dsimp[Fb3]
  intro x hx
  simp
  simp at hx
  constructor
  left
  exact hx.1
  constructor
  exact hx.2
  dsimp[Fb] at hF1_avoids
  unfold Path_forest_avoids! at hF1_avoids
  unfold Path_forest_support at hx
  simp at hx
  rcases hx.1 with ⟨P2, hP2a, hP2b⟩
  have jex: ∃ (j: Fin (F1.P.length) ),  F1.P.get j=P2:= by
    apply List.mem_iff_get.1
    exact hP2a
  rcases jex with ⟨j, hj⟩
  have jget: F1.P.get j =F1.P.get! j:= by
    simp
    symm
    apply List.getD_eq_get
  rw[hj.symm, jget] at hP2b
  have hdis: Disjoint {v | v ∈ (F1.P.get! j).Pa.Wa.support} {v | v ∈ E}:= by
    apply hF1_avoids
    calc
      j< F1.P.length:= by exact j.isLt
      _= k:= by exact hF1P_length
  have xin: x∈ {v | v ∈ (F1.P.get! ↑j).Pa.Wa.support}:= by
    simp
    exact hP2b
  have  hxnin: x ∉ {v | v ∈ E}:= by
    by_contra cont
    have h5:¬ (Disjoint {v | v ∈ (F1.P.get! ↑j).Pa.Wa.support} {v | v ∈ E}):= by
      apply Set.not_disjoint_iff.mpr
      use x
      repeat assumption
    exact h5 hdis
  simp at hxnin
  have hcont: List.take (k) E⊆ E:= by
    exact List.take_subset (k) E
  exact fun a ↦ hxnin (hcont a)
let Fb3_1:Set V:={v:V| v∈ Path_forest_support iV iSP F1}\ {v: V| v∈ (S.take (k))}
have hF3_avoids1 : Path_forest_avoids! iV iSP F3 Fb3_1 k:= by
  unfold Path_forest_avoids!
  intro i hi
  apply Set.disjoint_of_subset_right
  exact Fb3Cont1
  apply hF3_avoids
  exact hi



have SinFb2: {v:V|v∈ List.take (k) S}⊆ Fb2:= by
  have h1: {v:V|v∈ List.take (k) S}={v:V|v∈ F1.E.take F1.k}:= by
    --have h3: {v:V|v∈ List.take (k) S}={v:V|v∈ List.take (k) (S'.rotate 1)}
    have h2:  List.take (k) (S'.rotate 1)=F1.E.take F1.k:= by
      rw[hF1E, hF1k]
      symm
      apply (List.take_length_le)
      exact List.length_take_le k (S'.rotate 1)
    rw[h2.symm]
    dsimp[S']
    ext v
    simp
    nth_rewrite 2 [List.take_length_le]
    simp
    rw [@List.length_rotate]
    exact List.length_take_le k S
  rw[h1]
  dsimp[Fb2]
  have h2:  {v | v ∈ List.take F1.k F1.E} ⊆ Path_forest_support iV iSP F1:= by
    apply Path_forest_ends_contained
  have h3: Disjoint {v | v ∈ List.take F1.k F1.E}   {v | v ∈ List.take k Seq.Ver} := by
    rw[h1.symm]
    rw [@Set.disjoint_right]
    intro a ha
    simp
    simp at ha
    by_contra cont
    have aS:a∈ S:= by
      have h2: List.take k S⊆ S:= by
        exact List.take_subset k S
      exact h2 cont
    have aV: a∈ Seq.Ver:= by
      have h2: List.take k Seq.Ver⊆ Seq.Ver:= by
        exact List.take_subset k Seq.Ver
      exact h2 ha
    have ndis: ¬(List.Disjoint (Seq.Ver) S):= by
      exact fun a_1 ↦ hSVer aV aS
    exact hSVer aV aS
  refine Set.subset_diff.mpr ?_
  constructor
  exact h2
  exact h3




have Fb3Cont2: {v:V| v∈ Path_forest_support iV iSP F2}\ {v: V| v∈ (E.take (k))}⊆ Fb3:= by
  dsimp[Fb3]
  intro x hx
  simp
  simp at hx
  constructor
  right
  exact hx.1
  constructor
  dsimp[Fb] at hF1_avoids
  unfold Path_forest_avoids! at hF2_avoids
  unfold Path_forest_support at hx
  simp at hx
  rcases hx.1 with ⟨P2, hP2a, hP2b⟩
  have jex: ∃ (j: Fin (F2.P.length) ),  F2.P.get j=P2:= by
    apply List.mem_iff_get.1
    exact hP2a
  rcases jex with ⟨j, hj⟩
  have jget: F2.P.get j =F2.P.get! j:= by
    simp
    symm
    apply List.getD_eq_get
  rw[hj.symm, jget] at hP2b
  have hdis: Disjoint {v | v ∈ (F2.P.get! j).Pa.Wa.support} Fb2:= by
    apply hF2_avoids
    calc
      j< F2.P.length:= by exact j.isLt
      _= k:= by exact hF2P_length
  have xin: x∈ {v | v ∈ (F2.P.get! ↑j).Pa.Wa.support}:= by
    simp
    exact hP2b
  have  hxnin: x ∉ Fb2:= by
    by_contra cont
    have h5:¬ (Disjoint {v | v ∈ (F2.P.get! ↑j).Pa.Wa.support} Fb2):= by
      apply Set.not_disjoint_iff.mpr
      use x
      repeat assumption
    exact h5 hdis
  exact fun a ↦ hxnin (SinFb2 a)
  exact hx.2
let Fb3_2:Set V:={v:V| v∈ Path_forest_support iV iSP F2}\ {v: V| v∈ (E.take (k))}
have hF3_avoids2 : Path_forest_avoids! iV iSP F3 Fb3_2 (k):= by
  unfold Path_forest_avoids!
  intro i hi
  apply Set.disjoint_of_subset_right
  exact Fb3Cont2
  apply hF3_avoids
  exact hi


have F2avoids'': Path_forest_avoids! iV iSP F2 {v:V|v∈ Path_forest_support iV iSP F3 ∧ v∉ F2.S} k:= by

  apply Fb_disj_symm2
  exact hF2k
  exact hF3k
  rw[hF2S, hF3E]
  exact hF3_avoids2
  rw[hF3E]
  dsimp[Fb3_2]
  ext v; simp
  exact rfl


have VerTakeNodup:(List.take k Seq.Ver).Nodup:= by
  have subl: List.Sublist (List.take k Seq.Ver) Seq.Ver:= by
    exact List.take_sublist k Seq.Ver
  have nd: Seq.Ver.Nodup:= by
    exact Seq.VerNoDup
  exact List.Nodup.sublist subl nd


have hF1S_length: F1.S.length=k:= by
  rw[hF1S]
  have h1: Seq.Ver.length ≥ k:= by exact Ver_length_ge
  rw[(List.takeD_eq_take _ h1).symm]
  apply List.takeD_length
  exact default

have hF2S_length: F2.S.length=k:= by
  rw[hF2S]
  have h1: E.length ≥ k:= by rw[hE]; simp
  rw[(List.takeD_eq_take _ h1).symm]
  apply List.takeD_length
  exact default

have hF3S_length: F3.S.length=k:= by
  rw[hF3S]
  have h1: S.length ≥ k:= by rw[hS]; simp
  rw[(List.takeD_eq_take _ h1).symm]
  apply List.takeD_length
  exact default

have hF1E_length: F1.E.length=k:= by
  rw[hF1E]
  have h1: (S'.rotate 1).length ≥ k:= by dsimp[S']; simp; rw[hS]; simp
  rw[(List.takeD_eq_take _ h1).symm]
  apply List.takeD_length
  exact default

have hF2E_length: F2.E.length=k:= by
  rw[hF2E]
  have h1: Seq.Ver.length ≥ k:= by exact Ver_length_ge
  rw[(List.takeD_eq_take _ h1).symm]
  apply List.takeD_length
  exact default

have hF3E_length: F3.E.length=k:= by
  rw[hF3E]
  have h1: E.length ≥ k:= by rw[hE]; simp
  rw[(List.takeD_eq_take _ h1).symm]
  apply List.takeD_length
  exact default


have Path_ex: _:= by
  apply join_three_forests_tail_disjoint iV iSP H F3 F2 F1 _ _ _ (k-3) (k-2)
  --∀ (i j : ℕ), i < j → j < k → tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)
  apply single_path_forest_tail_disjoint;
  exact F3_ge_k
  -- ∀ (i j : ℕ), i < j → j < k → tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)
  apply single_path_forest_tail_disjoint;
  exact F2_ge_k
  --∀ (i j : ℕ), i < j → j < k → tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)
  apply single_path_forest_tail_disjoint;
  exact F1_ge_k
  -- ∀ (i j : ℕ), i < k → j < k → tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)
  apply set_disjoint_to_tail_disjoint_forward
  exact F3_ge_k
  exact F2_ge_k
  rw[hF2k, hF2S_length]
  apply path_forest_avoids_monotone!
  exact F2avoids''
  simp
  exact rfl
  rw[hF3k, hF3S_length]
  -- ∀ (i j : ℕ), i < k → j < k → tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)
  apply set_disjoint_to_tail_disjoint_forward
  exact F2_ge_k
  exact F1_ge_k
  rw[hF1k, hF1S_length]
  apply path_forest_avoids_monotone!
  exact F2avoids'
  simp
  exact rfl
  rw[hF2k, hF2S_length]





  --∀ (i j : ℕ), i < k → j < k → tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)
  apply set_disjoint_to_tail_disjoint_forward
  exact F1_ge_k
  exact F3_ge_k
  rw[hF3k, hF3S_length]
  apply path_forest_avoids_monotone!
  exact hF3_avoids1
  simp
  dsimp[Fb3_1]
  rw[hF3S]
  ext v; simp
  rw[hF1k, hF1S_length]
  --∀ (i j : ℕ), i < k → j < k → i ≠ j → tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)
  apply set_disjoint_to_internal_disjoint_reverse_taildisj_symm2
  exact F3_ge_k
  exact F2_ge_k
  rw[hF2k, hF2S_length]
  rw[hF3k, hF3E_length]
  rw[hF3E, hF2S]
  rw[hF2S]
  apply @List.Nodup.sublist _ (List.take k E) E
  exact List.take_sublist k E
  exact hENoDup
  apply path_forest_avoids_monotone!
  exact F2avoids''
  simp
  exact rfl
  rw[hF3k, hF3S_length]
  --∀ (i j : ℕ), i < k → j < k → i ≠ j + 1 → tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)
  apply set_disjoint_to_internal_disjoint_reverse_taildisj_symm2_tailaligned2
  exact F1_ge_k
  exact F3_ge_k
  rw[hF3k, hF3S_length]
  rw[hF1k, hF1E_length]
  rw[hF1E, hF3S]
  have hRoteq: List.take k (S'.rotate 1) = (List.take k S).rotate 1:= by
    dsimp[S']
    nth_rewrite 1 [List.take_length_le]
    exact rfl
    rw [List.length_rotate]
    exact List.length_take_le k S
  exact hRoteq
  rw[hF3E]
  apply @List.Nodup.sublist _ (List.take k E) E
  exact List.take_sublist k E
  exact hENoDup
  apply path_forest_avoids_monotone!
  exact hF3_avoids1
  simp
  rw[hF3S]
  dsimp[Fb3_1]
  ext v;simp
  rw[hF1k, hF1S_length]


  --∀ (i j : ℕ), i < k → j < k → i ≠ j → tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)
  apply set_disjoint_to_internal_disjoint_reverse_taildisj_symm2
  exact F2_ge_k
  exact F1_ge_k
  rw[hF1k, hF1S_length]
  rw[hF2k, hF2E_length]
  rw[hF2E, hF1S]
  rw[hF1S]
  exact VerTakeNodup
  apply path_forest_avoids_monotone!
  exact F2avoids'
  simp
  exact rfl
  rw[hF2k, hF2S_length]




  rw[hF3S_length]
  apply Nat.sub_lt
  exact kPositive
  simp
  apply Nat.sub_lt_sub_left
  exact kLarge
  simp
  rw[hF3k]
  apply Nat.sub_lt
  exact kPositive
  simp
  rw[hF2k]
  apply Nat.sub_lt
  exact kPositive
  simp
  rw[hF1k]
  apply Nat.sub_lt
  exact kPositive
  simp
  rw[hF3E, hF2S]
  rw[hF2E, hF1S]
  rw[hF1E, hF3S]
  dsimp[S']
  have h1: ((List.take k S).rotate 1)=((List.take k S).rotate 1)++[]:= by
    simp
  nth_rewrite 1 [h1]
  have h2:k= ((List.take k S).rotate 1).length:= by
    simp
    symm
    apply min_eq_iff.2
    left
    constructor
    exact rfl
    rw[hS]
    simp
  nth_rewrite 1 [h2]
  apply List.take_left


  --

rcases Path_ex with ⟨P, hP1⟩







  --


sorry





/-lemma add_Ver_to_M_list_starts_alt
(Ord: List (Clump G p m κ pr h))
(Ver S: List V)

(LM: List (Subgraph G))
(LM_in_M: M_list_in_clump_list iI LM Ord)
(VerInOrd:Vertex_list_in_clump_list_BSetPlusM iI iV Ord Ver)
(k:ℕ )

(hSML: ∀ (i: ℕ ), i<k+1+1→ (S.get! i)∈ (LM.get! i).verts)

(LM_length: LM.length> k+1+1)
(Ord_length: Ord.length> k+1+1)
(Ver_length: Ver.length> k+1)
(S_length: S.length> k+1+1)
:
∃ (HL: List  (Subgraph G)),
(HL.length=k)
∧ (cut_dense_list! iSub HL γ (k))
∧ (∀ (i: ℕ ), i<k→ (Ver.get! i)∈ (HL.get! (i)).verts)
∧ (∀ (i: ℕ ), i<k→ (S.tail.get! (i))∈ (HL.get! i).verts)

-/


/-
lemma set_disjoint_to_tail_disjoint_fixed
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1}\ {v:V|v∈ F2.S}⊆ Fb)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by

intro i j hi hj
unfold tail_disjoint_imp

apply Fb_disj_to_tail_disj

exact (F2.P.get! j).Pa.Wa_Is_Path
calc
  {v | v ∈ (F1.P.get! i).Pa.Wa.support} \ {(F2.P.get! j).s}
  --⊆ {v | v ∈ (F1.P.get! i).Pa.Wa.support} := by
    --exact Set.diff_subset {v | v ∈ (F1.P.get! i).Pa.Wa.support} {(F2.P.get! j).s}
  ⊆ {v:V| v∈ Path_forest_support iV iSP F1}\ {v:V|v∈ F2.S}:= by
    simp
    unfold Path_forest_support

    intro a ha
    have h78:F1.P.get! i ∈ F1.P:= by
      simp
      have h2: F1.P.getD i default=F1.P.get ⟨ i,_⟩:= by
        refine List.getD_eq_get F1.P default ?_
        rw[F1.P_length ]
        exact Nat.lt_of_lt_of_le hi F1k
      rw[h2]
      exact
        List.get_mem F1.P i
          (Eq.mpr (id (congrArg (fun _a ↦ i < _a) F1.P_length)) (Nat.lt_of_lt_of_le hi F1k))
    simp
    simp at ha

    use F1.P.get! i
  _⊆ Fb:= by
    exact F1_in_Fb

apply F2_avoids_Fb
exact hj
-/
