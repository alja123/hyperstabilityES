import MyProject

import MyProject.path_forests_clump_sequence_preparation
import MyProject.tail_disj_join
import MyProject.path_forest_clump_sequence
--C:\Users\alja1\Downloads\pro\my_project\MyProject\path_forests_clump_sequence_preparation.lean
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats  100000

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




lemma clump_path_sequence_gives_path2
(H: Subgraph G)
(KFam: Finset (Clump G p m κ pr h))
(Seq: ClumpPathSequence iI iV α KFam)
(k: ℕ )
(Ord_length: Seq.Ord.length>k+1)
:
∃  (u v: V), ∃  (P: SubgraphPath H u v), P.Wa.length ≥  (k*m)

--Has_length_d_path (Clump_Family_Union KFam) (h*m)
:=by

have Ord_length2: Seq.Ord.length>k:= by
  exact Nat.lt_of_succ_lt Ord_length

have LM_length: Seq.LM.length>k:= by
  rw[Seq.hlengthM]
  exact Nat.lt_of_succ_lt Ord_length
have Ver_length: Seq.Ver.length> k:= by
  rw[Seq.hlengthVer]
  exact Nat.lt_sub_of_add_lt Ord_length
have LM_length_ge: Seq.LM.length≥ k:= by
  exact Nat.le_of_succ_le LM_length
have Ord_length_ge: Seq.Ord.length≥ k:= by
  calc
  Seq.Ord.length ≥ k+1:=by exact Nat.le_of_succ_le Ord_length
  _≥  k:= by exact Nat.le_add_right k 1


have ex_pairs: _:= by
  apply find_pairs_in_M_list iI iV iSub Seq.Ord Seq.Ver Seq.LM Seq.LM_in_M (k+1)
  sorry--exact LM_length_ge
  sorry--exact Ord_length_ge
  --2 * k + Seq.Ver.length + 2 ≤ m / pr
  sorry
  --

rcases ex_pairs with ⟨S, E, hS, hE, hSE, hSVer, hEVer, hSNoDup, hENoDup, hSInLM, hEInLM⟩


have ex_HS:_:=by
  apply add_Ver_to_M_list_starts_alt iI iV iSub Seq.Ord Seq.Ver S Seq.LM Seq.LM_in_M Seq.VerInOrd (k+1)
  sorry --exact fun i a ↦ hSInLM i a
  sorry--exact LM_length
  sorry--exact Ord_length2
  sorry--exact Ver_length
  sorry
  exact γ
  exact κPositive
  exact pPositive
  exact mPositive



have ex_HE:_:=by
  apply add_Ver_to_M_list iI iV iSub Seq.Ord Seq.Ver E Seq.LM Seq.LM_in_M Seq.VerInOrd (k+1)
  exact fun i a ↦ hEInLM i a
  sorry--exact LM_length
  sorry--exact Ord_length2
  sorry--exact Ver_length
  sorry
  exact γ
  exact κPositive
  exact pPositive
  exact mPositive


rcases ex_HS with ⟨HS, hHS_length, hcutdenseS, hVer_in_HS, hS_in_HS⟩

rcases ex_HE with ⟨HE, hHE, hcutdenseE, hVer_in_HE, hE_in_HE⟩


let Fb: Set V:= {v: V|v∈ E}


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
  sorry



have S_get_ineq: ∀ (i: ℕ ), i< k+1→i<S.length:= by
  intro i hi
  sorry

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
  sorry

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




have E_get_ineq: ∀ (i: ℕ ), i< k+1→i<E.length:= by
  intro i hi
  sorry

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
      sorry
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
    sorry



have hF1Ex: _:= by
  apply path_forest_specified_ends_simplified_prefix iV iSub iSP H Seq.Ver S.tail HS  k  m Fb _ _ _ _ _ _ _
  --vertex_list_outside_set iV Seq.Ver Fb (k + 1)
  intro i hi
  dsimp[Fb]
  exact id (List.Disjoint.symm hEVer) (Ver_get_in_Ver i hi)
  --vertex_list_outside_set iV S Fb (k + 1)
  intro i hi
  dsimp[Fb]
  exact hSE (Stail_get_in_S i hi)
  --Ver.Nodup
  exact Seq.VerNoDup
  --S.Nodup
  have subl: List.Sublist S.tail S:= by
    exact List.tail_sublist S
  exact List.Nodup.sublist subl hSNoDup
  --cut_dense
  exact hcutdenseS
  --small_intersection_list
  intro i hi
  --simp
  calc
    _
    =
    8 * γ * (Fb ∩ (HS.get! i).verts).toFinset.card + (m + 8 * γ * (2 * (k + 1)))
    :=by
      simp
    _≤
    8 * γ * (Fb).toFinset.card + (m + 8 * γ * (2 * (k + 1))):= by
      gcongr
      simp
    _≤ 8 * γ * (k+1)+ (m + 8 * γ * (2 * (k + 1))):= by
      gcongr
      dsimp[Fb]
      have h1: {v | v ∈ E}.toFinset= E.toFinset:= by
        ext v
        simp
      rw[h1]
      simp
      rw [← hE]
      exact List.toFinset_card_le E
    _≤ (HS.get! i).verts.toFinset.card:=by sorry

  --exact γPositive
  --vertex_list_in_graph_list iV iSub Seq.Ver HS (k + 1)
  intro i hi
  apply hVer_in_HS i hi
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi
  apply hS_in_HS i hi
  --Disjointness
  have h23: S.tail⊆ S:= by exact List.tail_subset S
  exact
    List.Disjoint.symm
      ((fun {α} {l₁ l₂} ↦ List.disjoint_left.mpr) fun ⦃a⦄ a_1 ↦
        id (List.Disjoint.symm hSVer) (h23 a_1))
  --lengths
  exact Ver_length
  sorry
  sorry
  --∀ i < k + 1, HS.get! i ≤ H (add this to lemma giving HS)
  sorry








rcases hF1Ex with ⟨F1, hF1S, hF1E, hF1k, hF1P_length, hF1_avoids, hFcard, S1length, E1length⟩


let Fb2: Set V:= /-{v: V|v∈ S}∪-/ ({v:V| v∈ Path_forest_support iV iSP F1}\ {v: V| v∈ Seq.Ver.take k})


have hF2Ex: _:= by
  apply path_forest_specified_ends_simplified_prefix iV iSub iSP H E Seq.Ver HE  k  m Fb2 _ _ _ _ _ _ _
  --vertex_list_outside_set iV Seq.Ver Fb (k + 1)
  intro i hi
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
  sorry--reduce k by 1--exact fun a ↦ h43 (h65 a)
  --vertex_list_outside_set iV S Fb (k + 1)
  intro i hi
  dsimp[Fb2]
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_and, Decidable.not_not]
  intro h99
  sorry -- reduce k by 1--exact Ver_get_in_Ver i hi
  --E.Nodup
  exact hENoDup
  --Ver.Nodup
  exact Seq.VerNoDup

  --cut_dense
  exact hcutdenseE
  --small_intersection_list
  intro i hi
  calc
    _
    =
    8 * γ * (Fb2 ∩ (HE.get! i).verts).toFinset.card + (m + 8 * γ * (2 * (k + 1)))
    :=by
      simp
    _≤
    8 * γ * (Fb2).toFinset.card + (m + 8 * γ * (2 * (k + 1))):= by
      gcongr
      simp
    _≤ 8 * γ * (41 * γ * k)+ (m + 8 * γ * (2 * (k + 1))):= by
      gcongr
      dsimp[Fb2]
      calc
        (Path_forest_support iV iSP F1 \ {v | v ∈ Seq.Ver.take k}).toFinset.card
        ≤ (Path_forest_support iV iSP F1).toFinset.card:=by
          gcongr
          simp
          exact Set.diff_subset (Path_forest_support iV iSP F1) _
        _≤ 41 * γ * k:= by exact hFcard
    _≤ (HE.get! i).verts.toFinset.card:=by sorry

  --exact γPositive
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi
  apply hE_in_HE i hi
  --vertex_list_in_graph_list iV iSub Seq.Ver HS (k + 1)
  intro i hi
  apply hVer_in_HE i hi

  --Disjointness
  exact hEVer
  --lengths
  sorry
  sorry
  sorry
  --∀ i < k + 1, HS.get! i ≤ H (add this to lemma giving HS)
  sorry

rcases hF2Ex with ⟨F2, hF2S, hF2E, hF2k, hF2P_length, hF2_avoids, hF2card, S2lenght, E2length⟩




let Fb3: Set V:=  ({v:V| v∈ Path_forest_support iV iSP F1}∪ {v:V| v∈ Path_forest_support iV iSP F2})\ ({v: V| v∈ (S.take k)∨ v∈ (E.take k)})




have hF3Ex: _:= by
  apply long_path_forest_specified_ends_simplified iV iSub iSP H S E Seq.LM  k  m γ Fb3
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
  sorry -- using lower bound on size of graphs in M here (which is m/pr) currently
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi
  apply hSInLM i hi
  --vertex_list_in_graph_list iV iSub S HS (k + 1)
  intro i hi
  apply hEInLM i hi  --
  --Disjointness
  exact hSE
  --lengths
  sorry
  sorry
  sorry
  -- ∀ i < k + 1, Seq.LM.get! i ≤ H
  sorry
  --vertex_list_outside_set iV S Fb3 (k + 1)
  intro i hi
  dsimp[Fb3]
  simp only [ Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, not_or, not_and,
    Decidable.not_not]
  intro h99 h87
  sorry--exact (h87 (S_get_in_S i hi)).elim
  --vertex_list_outside_set iV E Fb3 (k + 1)
  intro i hi
  dsimp[Fb3]
  simp only [ Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, not_or, not_and,
    Decidable.not_not]
  intro h99 h87
  sorry--exact E_get_in_S i hi
  --Snodup
  exact hSNoDup
  --Enodup
  exact hENoDup
  --LMnodup
  sorry --- should be part of path sequence definition
  --cut_dense
  intro i hi
  have h23: (Seq.LM.get! i)∈ (Seq.Ord.get! i).M:= by
    apply LM_get i hi
  --now apply that M graphs are gut dense
  sorry

  --small_intersection_list
  intro i hi
  calc
    _
    =
    8 * γ * (Fb3 ∩ (Seq.LM.get!  i).verts).toFinset.card + (m + 8 * γ * (2 * (k + 1)))
    :=by
      simp
    _≤
    8 * γ * (Fb3).toFinset.card + (m + 8 * γ * (2 * (k + 1))):= by
      gcongr
      simp
    _≤ 8 * γ * (82 * γ * k)+ (m + 8 * γ * (2 * (k + 1))):= by
      gcongr
      dsimp[Fb3]
      calc
        ((Path_forest_support iV iSP F1 ∪ Path_forest_support iV iSP F2) \ {v | v ∈ (S.take k) ∨ v ∈ (E.take k)}).toFinset.card
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
    _≤ (Seq.LM.get! i).verts.toFinset.card:=by
      have h23: (Seq.LM.get! i)∈ (Seq.Ord.get! i).M:= by
        apply LM_get i hi        --now use that M-graphs are big
      sorry
  exact γPositive








  --

--rcases hF3Ex with ⟨F3, hF3a, hF3b, hF3c, hF3d, hF3e⟩
rcases hF3Ex with ⟨F3, hF3S, hF3E, hF3k, hF3P_length, hF3_avoids, hF3card, S3length, E3length⟩


have F3_ge_k:F3.k≥ k:= by
    calc
    F3.k = k:= by exact hF3k
    _≥ k:= by exact Nat.le_refl k

have F2_ge_k:F2.k≥ k:= by
  calc
    F2.k = k:= by exact hF2k
    _≥ k:= by exact Nat.le_refl k

have Path_ex: _:= by
  apply join_three_forests_tail_disjoint iV iSP H F3 F2 F1 _ _ _ k k
  --∀ (i j : ℕ), i < j → j < k → tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)
  apply single_path_forest_tail_disjoint;
  exact F3_ge_k
  -- ∀ (i j : ℕ), i < j → j < k → tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)
  apply single_path_forest_tail_disjoint;
  exact F2_ge_k
  --∀ (i j : ℕ), i < j → j < k → tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)
  apply single_path_forest_tail_disjoint;
  calc
    F1.k = k:= by exact hF1k
    _≥ k:= by exact Nat.le_refl k
  -- ∀ (i j : ℕ), i < k → j < k → tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)
  apply set_disjoint_to_tail_disjoint_forward
  exact F3_ge_k
  exact F2_ge_k
  sorry
  exact hF2_avoids
  dsimp[Fb2]
  sorry
  sorry
  -- ∀ (i j : ℕ), i < k → j < k → tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)

  sorry;sorry;sorry;sorry;sorry;
  sorry;sorry;sorry;sorry;sorry;
  --F1.E = F2.S
  rw[hF3E, hF2S]
  rw[hF2E, hF1S]
  rw[hF1E, hF3S]
  sorry

  --

rcases Path_ex with ⟨P, hP1⟩

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
