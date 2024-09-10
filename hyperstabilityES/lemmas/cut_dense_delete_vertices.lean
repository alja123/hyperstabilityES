--import MyProject

import hyperstabilityES.lemmas.expansion_cut_dense
  --import hyperstabilityES.lemmas.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

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

/-def cut_dense (G : SimpleGraph V)(H: Subgraph G)(k : ℕ ): Prop :=
∀ (A B: Finset V), (H.verts.toFinset= A ∪ B)→  k*(Rel.interedges H.Adj A B).card ≥ A.card*B.card

#check cut_dense
--set_option maxHeartbeats 600000
--set_option diagnostics true
--jjjk
lemma Cut_Dense_monotone
{H:   Subgraph G}
(a: ℕ)
{b: ℕ}
(hab: a≤ b)
(hcut_dense: cut_dense G H a)
: cut_dense G H b:= by
intro A B hUnion
calc
b * (Rel.interedges H.Adj A B).card ≥
a * (Rel.interedges H.Adj A B).card:= by
  gcongr
_≥ A.card * B.card:= by
  exact hcut_dense A B hUnion
-/

lemma cut_dense_delete_vertices1
(H: Subgraph G)
(cutdense:  cut_dense G H p)
(S: Set V)
(A B: Finset V)
(hUnion: (H.deleteVerts S).verts.toFinset = A ∪ B)
(S_small: 4*p*S.toFinset.card ≤ H.verts.toFinset.card)
(SinH: S ⊆ H.verts)
(Abig: 3*A.card ≥ H.verts.toFinset.card)
:
4 * p * (Rel.interedges (H.deleteVerts S).Adj A B).card ≥ A.card * B.card:=by
--unfold cut_dense
--intro A B hUnion
--let S: Set V:= S2\ B
let A':Finset V:= A ∪ (S.toFinset)


have SBdisj: (S.toFinset) ∩ B=∅:= by
  simp at hUnion
  have h2: B⊆ A ∪ B:= by
    exact subset_union_right A B
  rw[hUnion.symm] at h2
  refine disjoint_iff_inter_eq_empty.mp ?_
  apply Disjoint.symm-- ((fun {α} {s t} ↦ disjoint_left.mpr) ?_)
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  have h3: a∈ H.verts.toFinset \ S.toFinset:= by
    exact h2 ha
  by_contra cont
  have h4: a∈ S.toFinset:= by
    simp
    exact cont
  have h5: a∉ H.verts.toFinset \ S.toFinset:= by
    exact not_mem_sdiff_of_mem_right h4
  exact h5 (h2 ha)





have hUnionH: H.verts.toFinset= A' ∪ B:= by
  dsimp[A']
  simp
  simp at hUnion
  calc
   H.verts.toFinset =( H.verts.toFinset \ S.toFinset)∪ S.toFinset:= by
     simp
     exact SinH
    _=A∪ B∪ S.toFinset:= by
      rw [hUnion]
    _= A ∪ (S.toFinset ∪ B):=by
      simp
      aesop

have hint: p * (Rel.interedges (H).Adj A' B).card ≥ A'.card * B.card:=by
  exact cutdense A' B hUnionH


have hint2: 4*p * (Rel.interedges (H).Adj (S.toFinset) B).card ≤  H.verts.toFinset.card * B.card:=by
  calc
    4*p * (Rel.interedges (H).Adj (S.toFinset) B).card
    ≤ 4*p * (S.toFinset.card * B.card):= by
      gcongr
      exact Rel.card_interedges_le_mul H.Adj S.toFinset B
    _= (4*p * S.toFinset.card) * B.card:=by ring_nf
    _≤  H.verts.toFinset.card * B.card:=by
      gcongr



have hAcont1: A⊆ H.verts.toFinset:= by
  have hAcont1: A⊆ (H.verts\ S).toFinset:= by
    simp at hUnion
    have h2:A⊆ A∪ B:= by  exact subset_union_left A B
    simp_all only [gt_iff_lt,
      Set.toFinset_card,
      Fintype.card_ofFinset,
      union_assoc,
      ge_iff_le,
      Set.toFinset_diff,
      A']
  simp at hAcont1
  have h3: A ⊆ A ∪ (S.toFinset ∪ B):= by
    exact subset_union_left A (S.toFinset ∪ B)
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    union_assoc,
    Subgraph.induce_verts,
    Set.toFinset_diff,
    ge_iff_le,
    A']

have hAcont2: B⊆ H.verts.toFinset:= by
  have hAcont1: B⊆ (H.verts\ S).toFinset:= by
    simp at hUnion
    have h2:B⊆ A∪ B:= by  exact subset_union_right A B
    simp_all only [gt_iff_lt,
      Set.toFinset_card,
      Fintype.card_ofFinset,
      union_assoc,
      ge_iff_le,
      Set.toFinset_diff,
      A']
  simp at hAcont1
  have h3: B ⊆ A ∪ (S.toFinset ∪ B):= by
    rw[←Finset.union_assoc]
    exact subset_union_right (A ∪ S.toFinset) B
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    union_assoc,
    Subgraph.induce_verts,
    Set.toFinset_diff,
    ge_iff_le,
    A']






have hcont : (Rel.interedges (H).Adj A' B)\  (Rel.interedges (H).Adj (S.toFinset) B)⊆ (Rel.interedges (H.deleteVerts S).Adj A B) := by
  dsimp[A']
  intro ⟨ x,y⟩  hx
  simp at hUnion

  unfold Rel.interedges
  simp
  unfold Rel.interedges at hx
  simp at hx
  simp at hAcont1
  simp at hAcont2
  constructor
  simp_all only [gt_iff_lt,
    Set.toFinset_card,
    Fintype.card_ofFinset,
    union_assoc,
    ge_iff_le,
    A']
  unhygienic
    with_reducible
      aesop_destruct_products
  simp_all only [not_true_eq_false,
    imp_false]
  unhygienic
    aesop_cases
      left_1
  ·
    simp_all only [not_true_eq_false,
      imp_false,
      and_self]
  ·
    simp_all only [not_true_eq_false,
      imp_false]

  have hy: y ∈ B:= by
    simp_all only [gt_iff_lt,
      Set.toFinset_card,
      Fintype.card_ofFinset,
      union_assoc,
      ge_iff_le,
      A']
    unhygienic
      with_reducible
        aesop_destruct_products
    simp_all only [not_true_eq_false,
      imp_false]
    unhygienic
      aesop_cases
        left_1
    ·
      simp_all only [not_true_eq_false,
        imp_false]
    ·
      simp_all only [not_true_eq_false,
        imp_false]

  have hy2: y∈ H.verts:= by
    exact hAcont2 hy

  have hx2: x∈ A ∨ x∈ S:= by
    simp_all only [gt_iff_lt,
      Set.toFinset_card,
      Fintype.card_ofFinset,
      union_assoc,
      ge_iff_le,
      and_true,
      true_implies,
      A']

  have hx3: x∈ H.verts:= by
    simp_all only [gt_iff_lt,
      Set.toFinset_card,
      Fintype.card_ofFinset,
      union_assoc,
      ge_iff_le,
      and_true,
      true_and,
      true_implies,
      A']
    unhygienic
      with_reducible
        aesop_destruct_products
    simp_all only [not_true_eq_false,
      imp_false,
      or_false]
    apply
      hAcont1
    simp_all only [mem_coe]
  by_contra cont
  have h3: y∈ S:= by
    simp_all only [gt_iff_lt,
      Set.toFinset_card,
      Fintype.card_ofFinset,
      union_assoc,
      ge_iff_le,
      and_true,
      true_and,
      true_implies,
      not_and,
      Decidable.not_not,
      A']
    unhygienic
      with_reducible
        aesop_destruct_products
    simp_all only [not_true_eq_false,
      imp_false,
      not_false_eq_true]
  have h5: y∈ S.toFinset:= by
    simp
    exact h3
  have h6: y∈ S.toFinset∩ B:= by
    exact mem_inter_of_mem h5 hy
  have h4: ¬ ((S.toFinset) ∩ B=∅):= by
    exact ne_empty_of_mem h6

  exact h4 SBdisj


have hcont4: (Rel.interedges (H).Adj (S.toFinset) B)⊆ (Rel.interedges (H).Adj A' B):= by

  dsimp[A']
  refine interedges_subset G ?hA fun ⦃a⦄ a ↦ a
  exact subset_union_right A S.toFinset



calc
4 * p * (Rel.interedges (H.deleteVerts S).Adj A B).card
≥ 4*p*((Rel.interedges (H).Adj A' B)\  (Rel.interedges (H).Adj (S.toFinset) B)).card:= by
  gcongr
_= 4*p*((Rel.interedges (H).Adj A' B).card-  (Rel.interedges (H).Adj (S.toFinset) B).card):=by
  congr
  apply card_sdiff hcont4

_=4*p*(((Rel.interedges (H).Adj A' B).card))- 4*p*((Rel.interedges (H).Adj (S.toFinset) B).card):= by
  exact
    Nat.mul_sub_left_distrib (4 * p) (Rel.interedges H.Adj A' B).card
      (Rel.interedges H.Adj S.toFinset B).card
_=4*(p*((Rel.interedges (H).Adj A' B).card))- 4*p*((Rel.interedges (H).Adj (S.toFinset) B).card):= by
  ring_nf
_≥ 4*(A'.card * B.card)- ( H.verts.toFinset.card * B.card):= by
  gcongr

_≥ 4*(A'.card * B.card)- (3*A.card * B.card):= by
  gcongr
_=4*(A'.card * B.card)- 3*(A.card * B.card):= by
  ring_nf
_≥ 4*(A.card * B.card)- 3*(A.card * B.card):= by
  gcongr
  dsimp[A']
  exact subset_union_left A S.toFinset
_=(4-3)*(A.card * B.card):= by
  exact (Nat.mul_sub_right_distrib 4 3 (A.card * B.card)).symm
_=1*(A.card * B.card):= by
  congr
_= A.card * B.card:= by
  ring_nf






lemma cut_dense_delete_vertices2
(H: Subgraph G)
(cutdense:  cut_dense G H p)
(S: Set V)
(S_small: 4*p*S.toFinset.card ≤ H.verts.toFinset.card)
(SinH: S ⊆ H.verts)
 :
cut_dense G (H.deleteVerts S) (4*p)
:=by
unfold cut_dense
intro A B hUnion

by_cases abig: 3*A.card ≥ H.verts.toFinset.card
exact cut_dense_delete_vertices1 H cutdense S A B hUnion S_small SinH abig

have sum: A.card+ B.card≥ (H.deleteVerts S).verts.toFinset.card:=by
  rw [hUnion]
  exact card_union_le A B

have h2:  ( S.toFinset ⊆ H.verts.toFinset):= by
  simp
  exact SinH

have sum: B.card≥ H.verts.toFinset.card-S.toFinset.card-A.card:=by
  calc
    H.verts.toFinset.card-S.toFinset.card-A.card
    =
    (H.deleteVerts S).verts.toFinset.card-A.card:= by
      congr
      simp only [Subgraph.induce_verts, Set.toFinset_diff]
      exact (card_sdiff h2).symm
    _≤ B.card:= by
      exact Nat.sub_le_iff_le_add'.mpr sum


have sum2: H.verts.toFinset.card≤ A.card+S.toFinset.card+B.card:=by
  rw[Nat.sub_le_iff_le_add'.symm]
  calc
  H.verts.toFinset.card - (A.card + S.toFinset.card)
  =H.verts.toFinset.card-S.toFinset.card-A.card:=by
    exact Nat.Simproc.sub_add_eq_comm H.verts.toFinset.card A.card S.toFinset.card


  _≤ B.card:= by
    exact sum
   --B.card+A.card+S.toFinset.card≥ H.verts.toFinset.card-S.toFinset.card-A.card+A.card+S.toFinset.card:= by
   -- gcongr
  --_=H.verts.toFinset.card-S.toFinset.card-A.card+A.card+S.toFinset.card


have sum3: 2*H.verts.toFinset.card+3*B.card≥ 3*H.verts.toFinset.card:= by
  calc
    2*H.verts.toFinset.card+3*B.card
    =
    H.verts.toFinset.card+H.verts.toFinset.card+3*B.card:= by
      ring_nf
    _≥  3*A.card+3*S.toFinset.card+3*B.card:= by
      gcongr
      simp only [ge_iff_le, not_le] at abig
      exact Nat.le_of_succ_le abig
      calc
        3 * S.toFinset.card ≤ 4 * S.toFinset.card:= by
          gcongr
          exact Nat.le_of_ble_eq_true rfl
        _≤4* S.toFinset.card*p:= by
          exact Nat.le_mul_of_pos_right (4 * S.toFinset.card) pPositive
        _=4*p*S.toFinset.card:= by
          ring_nf
        _≤  H.verts.toFinset.card:= by
          exact S_small


    _=3*(A.card+S.toFinset.card+B.card):= by
      ring_nf
    _≥ 3*H.verts.toFinset.card:= by
      gcongr

have bbig: 3*B.card≥ H.verts.toFinset.card:= by
  calc
    H.verts.toFinset.card
    =1*H.verts.toFinset.card:= by
      ring_nf
    _=(3-2)* H.verts.toFinset.card:=by
      exact rfl
    _=3*H.verts.toFinset.card-2* H.verts.toFinset.card:= by
      exact Nat.mul_sub_right_distrib 3 2 H.verts.toFinset.card
    _≤ 3*B.card:= by
      exact Nat.sub_le_iff_le_add'.mpr sum3


rw[union_comm] at hUnion
have h:_:= by exact cut_dense_delete_vertices1 H cutdense S B A hUnion S_small SinH bbig
calc
4 * p * (Rel.interedges (H.deleteVerts S).Adj A B).card
=4 * p * (Rel.interedges (H.deleteVerts S).Adj B A).card:= by
  congr 1
  exact Rel.card_interedges_comm (fun ⦃x y⦄ a ↦ id (Subgraph.adj_symm (H.deleteVerts S) a)) A B
_≥ B.card * A.card:= by
  exact h
_= A.card * B.card:= by
  exact Nat.mul_comm B.card A.card



lemma cut_dense_delete_vertices
(H: Subgraph G)
(cutdense:  cut_dense G H p)
(S: Set V)
(S_small: 4*p*S.toFinset.card ≤ H.verts.toFinset.card)
:
cut_dense G (H.deleteVerts S) (4*p)
:= by
--let S': Set V:= S∩ H.verts

have h3: ∃ (S': Set V), (S'⊆ S)∧ (S'⊆ H.verts)∧  (H.deleteVerts S'=H.deleteVerts S):= by
  let S':= S∩ H.verts
  use S'
  constructor
  exact Set.inter_subset_left S H.verts
  constructor
  exact Set.inter_subset_right S H.verts
  exact Subgraph.deleteVerts_inter_verts_set_right_eq

rcases h3 with ⟨S', ⟨ hS'1, ⟨ hS'2, hS'3⟩ ⟩ ⟩

have h1: S'⊆ H.verts:= by exact hS'2
have h2: 4*p*S'.toFinset.card ≤ H.verts.toFinset.card:= by
  calc
    4*p*S'.toFinset.card
    ≤ 4*p*S.toFinset.card:= by
      gcongr
      simp
      exact hS'1
    _≤ H.verts.toFinset.card
    := by
      exact S_small

have h3: H.deleteVerts S'=H.deleteVerts S:= by
  exact hS'3




rw[h3.symm]
apply cut_dense_delete_vertices2
repeat assumption

/-have sum2: 3*B.card≥ H.verts.toFinset.card:=by
  calc
    3*B.card
    ≥  3*(H.verts.toFinset.card-S.toFinset.card-A.card):= by
      gcongr
    _≥
-/

/-
have hcont : (Rel.interedges (H.deleteVerts S).Adj A B)⊆ (Rel.interedges (H).Adj A' B)∪ (Rel.interedges (H).Adj (S.toFinset) B):= by
  dsimp[A']
  intro ⟨ x,y⟩  hx
  simp
  unfold Rel.interedges
  simp
  unfold Rel.interedges at hx
  simp at hx
  aesop

calc
2 * p * (Rel.interedges (H.deleteVerts S).Adj A B).card
γ

_≥ A.card * B.card:= by

-/
