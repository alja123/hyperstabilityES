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

--theorem cut_dense_union (H: Subgraph G)(K: Subgraph G)(p q:ℚ)(HCutDense: cut_dense G H p)(KCutDense: cut_dense G H p)(hq: q= (p* (H.verts ∩ K.verts).toFinset.card)/(4*(H.verts ∪ K.verts).toFinset.card)):cut_dense G (H⊔K) q:= by


lemma nat_self_div (a:ℕ)(ha:0<a): (a/a=1):= by
have h0: a≤ a:= by exact Nat.le_refl a
have h1:a/a=(a-a)/a+1:= by exact Nat.div_eq_sub_div ha h0
exact Nat.div_self ha

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

lemma gt_cast_N_Q (a:ℕ)(ha:0< a): (0< (a:ℚ)):=
by exact Nat.cast_pos.mpr ha


theorem cut_dense_union_after_wlog (H: Subgraph G)(K: Subgraph G)(hNonempty: Nonempty (H⊔ L).verts )(k :ℕ )
(HCutDense: cut_dense G H k)(KCutDense: cut_dense G K k)
--(hl: l= (4*k* ((H.verts ∪  K.verts).toFinset.card ))/(((H.verts ∩ K.verts).toFinset.card)))
 (I A B:Finset V)(hunion: (H.verts∪ K.verts).toFinset= A∪ B)
 (hI: I=(H.verts ∩ K.verts).toFinset)(Iwlog: 2*((I∩ A).card) ≥ I.card)
 (hBwlog: 2*((H.verts.toFinset ∩ B).card)  ≥ B.card)
 :4*k* ((H.verts ∪  K.verts).toFinset.card )*(Rel.interedges (H⊔ K).Adj A B).card ≥ A.card*B.card* ((H.verts ∩  K.verts).toFinset.card ):= by

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



#check HCutDense A' B' (id Hunion.symm)
#check cut_dense
calc
  4*k* ((H.verts ∪  K.verts).toFinset.card )*((Rel.interedges (H ⊔ K).Adj A B).card) ≥ 4*k* ((H.verts ∪  K.verts).toFinset.card )*((Rel.interedges H.Adj A' B').card ):= by gcongr;
  _=4*((H.verts ∪  K.verts).toFinset.card )*(k*((Rel.interedges H.Adj A' B').card )):= by
    simp;
    ring_nf
  _≥ 4*((H.verts ∪  K.verts).toFinset.card )* (A'.card * B'.card) := by
    have _:(k*((Rel.interedges H.Adj A' B').card ))≥ (A'.card * B'.card):= by exact      HCutDense A' B' (id Hunion.symm)
    gcongr--exact HCutDense A' B' (id Hunion.symm)
  _≥ 4*((H.verts ∪  K.verts).toFinset.card )* (AI.card *B'.card):= by
    have h1: A'.card≥ AI.card:= by exact card_le_of_subset hAicont;
    gcongr
  _=2*((H.verts ∪  K.verts).toFinset.card )*B'.card* (2*AI.card):= by
    ring_nf--exact mul_right_comm p ↑AI.card ↑B'.card
  _≥ 2*((H.verts ∪  K.verts).toFinset.card )*B'.card * I.card:= by
    gcongr--gcongr
  _=((H.verts ∪  K.verts).toFinset.card )* (I.card)*(2*B'.card):= by
    ring_nf--exact (mul_right_comm p (↑I.card / 2) ↑B'.card).symm
  _≥ ((H.verts ∪  K.verts).toFinset.card )* (I.card) * (B.card):= by
    gcongr
  _≥ (A.card )* (I.card) * (B.card):= by
    gcongr
  _= (A.card) * (B.card) * (I.card ):= by
    ring_nf
  _= A.card * B.card * (H.verts ∩ K.verts).toFinset.card:= by
    congr



lemma incl_excl_corollary (X Y Z: Finset V)(hsubset:X⊆ Y∪ Z): (Y∩ X).card +(Z∩ X).card ≥ (X).card:= by
have incl_excl: X.card=(Y∩ X).card+(Z∩ X).card-(X∩  Y∩ Z).card:= by calc
  X.card=((Y∩ X)∪ (Z∩ X)).card:= by
    have h1: ((Y∩ X)∪ (Z∩ X))=X:= by calc
      ((Y∩ X)∪ (Z∩ X))=(Y∪ Z)∩ X:= by exact (union_inter_distrib_right Y Z X).symm
      _=X:= by exact inter_eq_right.mpr hsubset
    exact congrArg card (id h1.symm)
  _=(Y∩ X).card+(Z∩ X).card-((Y∩ X)∩ (Z∩ X)).card:= by exact card_union (Y ∩ X) (Z ∩ X)
  _=(Y∩ X).card+(Z∩ X).card-(X∩  Y∩ Z).card:= by
    have h1:((Y∩ X)∩ (Z∩ X))=(X∩  Y∩ Z):= by calc
      ((Y∩ X)∩ (Z∩ X))=(Y∩ X∩  Z∩ X):= by simp
      _=(Y∩ X∩  X∩ Z):= by exact inter_right_comm (Y ∩ X) Z X
      _=Y∩ (X∩ Z):=by simp
      _=X∩ (Y∩ Z):=by exact inter_left_comm Y X Z
      _=X∩ Y∩ Z:= by simp;
    rw[h1]

calc
(Y∩ X).card+(Z∩ X).card≥ (Y∩ X).card+(Z∩ X).card-(X∩  Y∩ Z).card:= by exact  Nat.sub_le ((Y ∩ X).card + (Z ∩ X).card) (X ∩ Y ∩ Z).card
_=X.card:= by exact id incl_excl.symm

lemma incl_excl_corollary2 (X Y Z: Finset V)(hsubset:X⊆ Y∪ Z): (2*(Y∩ X).card ≥ (X).card)∨ (2*(Z∩ X).card ≥ (X).card):= by
by_contra h
simp at h
have h1: 2 * ((Y ∩ X).card +  (Z ∩ X).card) < 2*X.card:= by calc
  2 * ((Y ∩ X).card +  (Z ∩ X).card) = 2 * (Y ∩ X).card +  2* (Z ∩ X).card:= by exact    Nat.mul_add 2 (Y ∩ X).card (Z ∩ X).card
  _< 2 * (Y ∩ X).card + X.card:= by gcongr; exact h.2
  _<  X.card+ X.card:= by gcongr; exact h.1
  _= 2* X.card:= by exact (Nat.two_mul X.card).symm
have h2:  ((Y ∩ X).card +  (Z ∩ X).card) ≥  X.card:= by exact  incl_excl_corollary X Y Z hsubset
have h2: 2*(((Y ∩ X).card +  (Z ∩ X).card)) ≥  2*X.card:=by exact Nat.mul_le_mul_left 2 h2
have h3:  2 * ((Y ∩ X).card + (Z ∩ X).card)+2*X.card<2 * ((Y ∩ X).card + (Z ∩ X).card)+2*X.card:= by
  exact  lt_imp_lt_of_le_imp_le (fun a ↦ h2) h1
exact (lt_self_iff_false (2 * ((Y ∩ X).card + (Z ∩ X).card) + 2 * X.card)).mp h3

theorem cut_dense_union (H: Subgraph G)(K: Subgraph G)(p q:ℕ )(HCutDense: cut_dense G H p)(KCutDense: cut_dense G K p)(hq: q= (8*k* (H.verts ∪  K.verts).toFinset.card)/((H.verts ∪ K.verts).toFinset.card)):cut_dense G (H⊔K) q:= by
intro A B hAB
let I:= (H.verts ∩ K.verts).toFinset
have _:(A∩ I)∪ (B∩ I)=I:= by
sorry
