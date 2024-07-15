import MyProject

import MyProject.cut_dense_basics


open Classical
open Finset
--open scoped BigOperators

namespace SimpleGraph


universe u
variable {V : Type u} (G : SimpleGraph V)
variable [Fintype V] [DecidableRel G.Adj]
variable (n: ℕ )
variable (d:ℕ )
variable [Fintype (Sym2 V)]

theorem cut_dense_union (H: Subgraph G)(K: Subgraph G)(p q:ℚ)(HCutDense: cut_dense G H p)(KCutDense: cut_dense G H p)(hq: q= (p* (H.verts ∩ K.verts).toFinset.card)/(4*(H.verts ∪ K.verts).toFinset.card)):cut_dense G (H⊔K) q:= by
sorry

lemma subgraph_preserves_adj  (H K: Subgraph G)(hHK:H≤ K)(v w:V):( H.Adj v w → K.Adj v w):= by
have h1: (H.verts ⊆ K.verts) ∧ (∀ (v w : V), H.Adj v w → K.Adj v w):= by exact hHK
apply h1.2

theorem interedges_subgraph_leq (H K: Subgraph G)(hHK:H≤ K):(Rel.interedges H.Adj A B⊆  Rel.interedges K.Adj A B):= by
intro e he
let (x, y):=e
have h: x∈ A∧ y∈ B ∧ H.Adj x y := by exact Rel.mk_mem_interedges_iff.mp he
have hxy:H.Adj x y:= h.2.2
have kxy: K.Adj x y:= by exact subgraph_preserves_adj G H K hHK x y hxy
--have hx:x∈ K.verts:= by exact K.edge_vert kxy
--have hy:x∈ K.verts:= by exact K.edge_vert kxy
have hxy': x∈ A∧ y∈ B ∧ K.Adj x y := by
  constructor
  exact h.1
  constructor
  exact h.2.1
  exact kxy
exact Rel.mk_mem_interedges_iff.mpr hxy'

--theorem interedges_subsets_leq (H: Subgraph G)(A B A' B':Finset V)(hA: A'⊆ A)(hB: B'⊆ B):Rel.interedges H.Adj A' B'⊆ Rel.interedges H.Adj A B:=by
--exact?

lemma gt_implies_gte_rational (a  b: ℚ )(ha:(b<a)):  (b≤ a):= by
  have h1: (b≤ a) ∧ (b≠ a):= by exact lt_iff_le_and_ne.mp ha
  exact h1.1

theorem cut_dense_union_after_wlog (H: Subgraph G)(K: Subgraph G)(hNonempty: Nonempty (H∪ K).verts)(p q:ℚ)(hp:p≥ 0)(HCutDense: cut_dense G H p)(KCutDense: cut_dense G H p)
(hq: q= (p* ((H.verts ∩ K.verts).toFinset.card:ℚ ))/((4*(H.verts ∪ K.verts).toFinset.card):ℚ))
 (I A B:Finset V)(hunion: (H.verts∪ K.verts).toFinset= A∪ B)
 (hI: I=(H.verts ∩ K.verts).toFinset)(Iwlog: ((I∩ A).card:ℚ) ≥ I.card/2)
 (hBwlog: ((H.verts.toFinset ∩ B).card:ℚ)  ≥ B.card/2)
 :(Rel.interedges (H⊔ K).Adj A B).card ≥ q*A.card*B.card:= by

have contHunion: H≤ H⊔ K := by exact SemilatticeSup.le_sup_left H K
have cont1: Rel.interedges H.Adj A B⊆ Rel.interedges (H ⊔ K).Adj A B:= by exact interedges_subgraph_leq G H (H ⊔ K) contHunion
let A':=A∩ H.verts.toFinset
let B':=B∩ H.verts.toFinset
have hunion2:H.verts ∪ K.verts=(H⊔ K).verts:= by exact rfl
have Hunion: A'∪ B'=H.verts.toFinset:= by calc
  A'∪ B'=(A∩ H.verts.toFinset)∪ (B∩ H.verts.toFinset):= by exact rfl
  _=(A∪ B)∩ H.verts.toFinset:= by exact (union_inter_distrib_right A B H.verts.toFinset).symm
  _=(H.verts ∪ K.verts).toFinset ∩ H.verts.toFinset:= by exact    congrFun (congrArg Inter.inter (id hunion.symm)) H.verts.toFinset
  _= H.verts.toFinset:= by simp
have hA':A'⊆ A:= by exact inter_subset_left A H.verts.toFinset
have hB':B'⊆ B:= by exact inter_subset_left B H.verts.toFinset
have cont2:Rel.interedges H.Adj A' B'⊆Rel.interedges (H ⊔ K).Adj A B:= by calc
  Rel.interedges H.Adj A' B'⊆ Rel.interedges H.Adj A B:= by exact Rel.interedges_mono hA' hB'
  _⊆ Rel.interedges (H⊔ K).Adj A B:= by exact cont1

have ineq1:  (Rel.interedges (H ⊔ K).Adj A B).card ≥ (Rel.interedges H.Adj A' B').card:= by exact  card_le_of_subset cont2


let AI:= A∩ I
have hAicont:AI⊆ A':= by calc
  AI=A∩(H.verts ∩ K.verts).toFinset:= by rw[hI.symm]
  _=A∩H.verts.toFinset ∩ K.verts.toFinset:= by simp
  _⊆ A':= by exact inter_subset_left (A ∩ H.verts.toFinset) K.verts.toFinset

have AIeq: AI= I∩ A:= by exact inter_comm A I
rw [AIeq.symm] at Iwlog
--have Iwlog: (AI.card:ℚ)≥ (I.card / 2:ℚ)  := by exact?

have B'eq:B'=(H.verts.toFinset ∩ B):= by exact inter_comm B H.verts.toFinset
rw [B'eq.symm] at hBwlog

have hAcont: A⊆ (H.verts ∪ K.verts).toFinset:= by calc
 A⊆A∪ B:= by exact subset_union_left A B
 _=(H.verts ∪ K.verts).toFinset:= by exact id hunion.symm
have aAcontcard:A.card≤  (H.verts ∪ K.verts).toFinset.card:= by exact card_le_of_subset hAcont


have hNonempty:None (H.verts ∪ K.verts)

have h1pos: (H.verts ∩ K.verts).toFinset.card≥0:= by exact   Nat.zero_le (H.verts ∩ K.verts).toFinset.card
have h2pos: (H.verts ∪ K.verts).toFinset.card> 0:= by sorry
have h3pos: 0<4*(H.verts ∪ K.verts).toFinset.card:= by exact Nat.succ_mul_pos 3 h2pos
have h1pos: ((H.verts ∩ K.verts).toFinset.card:ℚ)≥0:= by exact Nat.cast_nonneg (H.verts ∩ K.verts).toFinset.card
have h3pos: 0<((4*(H.verts ∪ K.verts).toFinset.card):ℚ):= by apply Nat.cast_pos.2
have h3pos: (1/(4*(H.verts ∪ K.verts).toFinset.card):ℚ)> 0:= by exact one_div_pos.mpr h3pos
have h3pos: (1/(4*(H.verts ∪ K.verts).toFinset.card):ℚ)≥ 0:= by exact  gt_implies_gte_rational   (1/(4*(H.verts ∪ K.verts).toFinset.card)) 0  h3pos
#check Nat.cast_pos.2
--have _: (a:ℕ)→ (0< a)→ (0< (a:ℚ)):= by exact?
have h4pos:((H.verts ∩ K.verts).toFinset.card:ℚ  )*(1/ ((4 * (H.verts ∪ K.verts).toFinset.card):ℚ))≥ 0:= by
  exact  Rat.mul_nonneg h1pos h3pos
have h4pos:p*(((H.verts ∩ K.verts).toFinset.card:ℚ  )*(1/ ((4 * (H.verts ∪ K.verts).toFinset.card):ℚ)))≥ 0:= by exact  Rat.mul_nonneg hp h4pos

have h5eq: p*((H.verts ∩ K.verts).toFinset.card:ℚ  )*(1/ ((4 * (H.verts ∪ K.verts).toFinset.card):ℚ))=q:= by rw [hq]; calc
  p * ↑(H.verts ∩ K.verts).toFinset.card * (1 / (4 * ↑(H.verts ∪ K.verts).toFinset.card)) =(p * ↑(H.verts ∩ K.verts).toFinset.card * 1) / (4 * ↑(H.verts ∪ K.verts).toFinset.card):= by exact
    (mul_div_assoc (p * ↑(H.verts ∩ K.verts).toFinset.card) 1
        (4 * ↑(H.verts ∪ K.verts).toFinset.card)).symm
  _=(p * ↑(H.verts ∩ K.verts).toFinset.card) / (4 * ↑(H.verts ∪ K.verts).toFinset.card):= by simp
 -- exact?
--exact?
--have _: (a b : ℚ)→ (a≥0)→ (b≥  0)→ (a*b≥ 0):= by exact fun a b a_1 a_2 ↦Rat.mul_nonneg a_1 a_2


have hqpos:q≥0:= by rw[hq];

calc
  ((Rel.interedges (H ⊔ K).Adj A B).card:ℚ ) ≥ ((Rel.interedges H.Adj A' B').card:ℚ ):= by gcongr
  _≥ p * A'.card * B'.card := by exact HCutDense A' B' (id Hunion.symm)
  _≥ p * AI.card *B'.card:= by
    have h1: A'.card≥ AI.card:= by exact card_le_of_subset hAicont;
    gcongr
  _=(p  *B'.card)* AI.card:= by exact mul_right_comm p ↑AI.card ↑B'.card
  _≥ (p*B'.card)* (I.card/2):= by gcongr
  _=(p* (I.card/2))*B'.card:= by exact (mul_right_comm p (↑I.card / 2) ↑B'.card).symm
  _≥ (p* (I.card/2)) * (B.card/2):= by gcongr
  _=q*(H.verts ∪ K.verts).toFinset.card*B.card:= by sorry
  _≥ q*A.card*B.card:= by gcongr;
