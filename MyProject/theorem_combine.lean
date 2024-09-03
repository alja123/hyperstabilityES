import MyProject

import MyProject.theorem
import MyProject.brooms
import MyProject.locally_dense_find
import MyProject.long_path_avoiding

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 0

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
--variable {p m κ pr h α : ℕ}
/-variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}-/
--variable {γPositive: γ >0}
--variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
/-
variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )
variable (κggα: κ ≥ gg1 α )
variable (αggh: α ≥ h)
-/


lemma clumps_nonempty
(m κ  pr p h: ℕ)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
(κPositive: κ>0)
(pPositive: p>0)
(hPositive: h>0)
(prPositive: pr>0)
{L: Subgraph G}
(hLorderm: L.verts.toFinset.card ≥ m)
(hLorderhm: L.verts.toFinset.card ≤  h*m)
(hL: cut_dense G L p)
:
Nonempty (Clump G p m κ pr h)
:= by
have hex: ∃ (X: Clump G p m κ pr h), graph_forms_clump L X:= by
  apply initial_clump_construction_2
  repeat assumption
  --
rcases hex with ⟨X, hX⟩
exact Nonempty.intro X

theorem average_degree_implies_min_degree_3
(hd: d>0)
(H: Subgraph G)
(order: H.verts.toFinset.card ≥ 1)
(hAverageDeg:  (H.edgeSet.toFinset.card)≥ d*(H.verts.toFinset.card))
:
∃ (K: Subgraph G),
(∀ (v:V),(v∈ K.verts)
→  (K.degree v)≥d  )
∧ (K≤ H)
∧ (Nonempty K.verts):= by
apply average_degree_implies_min_degree_subgraph
assumption
have h1: Fintype.card H.verts=(H.verts.toFinset.card-1)+1:= by
  rw [Nat.sub_add_eq_max]
  have h2:  max H.verts.toFinset.card 1=H.verts.toFinset.card := by
    exact Nat.max_eq_left order
  rw[h2]
  simp
exact h1
rw [Nat.sub_one_add_one_eq_of_pos order]
simp at hAverageDeg
simp
exact hAverageDeg

theorem average_degree_implies_min_degree_4
(d p: ℕ )
(pPositive: p >0)
(hd: d≥2*p)
(H: Subgraph G)
(order: H.verts.toFinset.card ≥ 1)
(hAverageDeg:  p*(H.edgeSet.toFinset.card)≥ d*(H.verts.toFinset.card))
:
∃ (K: Subgraph G),
(K≤ H)∧ (K.verts.Nonempty) ∧
(∀ (v:V),(v∈ K.verts)
→  2*p*(K.degree v)≥d  )
:= by
have hd: d≥p:= by
  calc
    d≥ 2*p:= by assumption
    _≥ 1*p:= by gcongr;simp
    _=_:=by ring_nf

have h1: (H.edgeSet.toFinset.card)≥ (d/p)*(H.verts.toFinset.card):= by
  calc
    (H.edgeSet.toFinset.card)=p*(H.edgeSet.toFinset.card)/p:= by
      exact (Nat.mul_div_right H.edgeSet.toFinset.card pPositive).symm

    _≥ d*(H.verts.toFinset.card)/p:= by
      gcongr
    _=  ((H.verts.toFinset.card)*d)/p:= by
      ring_nf
    _≥(H.verts.toFinset.card)*(d/p):= by
      exact Nat.mul_div_le_mul_div_assoc H.verts.toFinset.card d p
    _=_:= by ring_nf


have h2: ∃ (K: Subgraph G),
(∀ (v:V),(v∈ K.verts)
→  (K.degree v)≥d/p  )
∧ (K≤ H)
∧ (Nonempty K.verts):= by
    apply average_degree_implies_min_degree_3
    exact Nat.div_pos hd pPositive
    exact order
    exact h1
rcases h2 with ⟨K, hK, hK2, hK3 ⟩
use K
constructor
--K≤ H (need to add this to original lemma)
exact hK2
constructor
--K.verts.Nonempty
exact Set.nonempty_of_nonempty_subtype
intro v hv
calc
  2 * p * K.degree v ≥
  2 * p * (d / p):= by
    gcongr
    apply hK
    assumption
  _≥  d:= by
    refine twice_times_fraction_ge d p pPositive ?hm
    assumption





theorem version3
(H: Subgraph G)
(ε d: ℕ )
--(dggε: d ≥ gg2 (gg1 (gg1 (gg2 (gg1 ε)))) * gg1 (gg2 (gg1 ε)))
(εPositive: ε >0)
(dPositive: d>0)
(no_paths: ¬ Has_length_d_path (H) (d))
(HNonempty: H.edgeSet.toFinset.card>0)
(Hedges: ε *H.edgeSet.toFinset.card ≥ d*H.verts.toFinset.card)
:
∃(Sub: Subgraph G), ∃ (Com Cov: List (Set V)),
Components_cover_graph Sub Com
∧
Components_disjoint Com
∧
No_edges_between_components Sub Com
∧
Components_covered_by_covers Sub Com Cov
∧
Covers_small (gg1 (gg1 (gg2 (gg1 ε)))) d Cov
∧
(ε *Sub.edgeSet.toFinset.card+ H.edgeSet.toFinset.card≥ ε *H.edgeSet.toFinset.card)
/-∃ (f: V→ Set V), ∃ (Sub: Subgraph G),
(∀ (x: V), Sub.neighborSet x ⊆  f x)
∧ (∀ ( x y: V), f x ≠ f y → (Disjoint (f x) (f y)))
∧ (∀ (x: V), (f x).toFinset.card≤ ((gg2 ε)*d))
∧ (ε *Sub.edgeSet.toFinset.card+H.edgeSet.toFinset.card≥ ε *H.edgeSet.toFinset.card)
-/:=by


--have p:ℕ := by sorry
--have pr:ℕ := by sorry
--have h:ℕ := by sorry
--have κ :ℕ := by sorry
have num_ex: ∃ (p pr h κ α : ℕ),  p≥ 20 ∧ pr ≥ gg2 p ∧ h ≥ gg1 pr ∧ κ ≥ gg1 h∧ κ ≥ gg1 α ∧ α ≥ h∧ p≥ gg1 ε ∧ d≥gg2 κ *h ∧ (gg1 (gg1 (gg2 (gg1 ε))))= κ:= by
  let p: ℕ := gg1 ε
  let pr: ℕ := gg2 p
  let h: ℕ := gg1 pr
  let κ: ℕ := gg1 h
  --let α : ℕ := h
  use p
  use pr
  use h
  use κ
  use h
  constructor
  calc
    p≥ 10000:= by
      dsimp[p]
      apply gg1_large
      repeat assumption
    _≥ 20:= by simp
  constructor

  dsimp[pr]
  apply Nat.le_refl
  constructor

  dsimp[h]
  apply Nat.le_refl
  constructor

  dsimp[κ]
  apply Nat.le_refl
  constructor

  dsimp[κ]
  apply Nat.le_refl
  constructor

  apply Nat.le_refl

  constructor
  dsimp[p]
  apply Nat.le_refl

  constructor
  dsimp[κ, h, pr, p]
  sorry--exact dggε

  dsimp[κ, h, pr, p]




rcases num_ex with ⟨p,pr,h,κ,α, pLarge, prggp, hggp,κggh, κggα, αggh, pggε, dgg, κeq⟩
--let p: ℕ := gg1 ε
--let pr: ℕ := gg2 p
--let h: ℕ := gg1 pr
--let κ: ℕ := gg1 h
let m: ℕ :=(p*d/h+1)

/-variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )
variable (κggα: κ ≥ gg1 α )
variable (αggh: α ≥ h)
-/

have pPositive: p >0:= by
  calc
    p≥ 10000:= by
      apply gg1_large2
      exact εPositive
      repeat assumption
    _>0:= by simp


have prPositive: pr >0:= by
  calc
    pr ≥ gg2 p:= by
      assumption
    _>0:= by
      apply gg2_pos
      repeat assumption
have hPositive: h >0:= by
  calc
    h ≥ gg1 pr:= by
      assumption
    _>0:= by
      apply gg1_pos
      repeat assumption
have κPositive: κ >0:= by
  calc
    κ  ≥ gg1 h:= by
      assumption
    _>0:= by
      apply gg1_pos
      repeat assumption

have hd2': d≥ p*64:= by
  calc
    d≥ gg2 κ *h:= by assumption
    _≥ κ *10000:= by
      gcongr
      apply gg2_ge
      apply Nat.le.refl
      repeat assumption
      apply gg1_large2
      exact prPositive
      assumption
    _≥ h *10000:= by
      gcongr
      apply gg1_ge
      repeat assumption
    _≥ pr*64:= by
      gcongr
      apply gg1_ge
      repeat assumption
      simp
    _≥ p*64:= by
      gcongr
      apply gg2_ge
      repeat assumption
have hd2: d≥ 16*p:= by
  rw[mul_comm]
  calc
    d ≥ p*64:= by assumption
    _≥ _:= by   gcongr;  simp
have hd1: d≥ 16*ε:= by
  calc
    d≥ 16*p:= by
      assumption
    _≥ _:= by
      gcongr
      apply gg1_ge
      repeat assumption

have hp2: p ≥ ε ^ 16 * 75557863725914323419136 :=by
  apply gg1_4
  repeat assumption--

have hd4: d≥  ε ^ 8 * 10995116277760  := by
  calc
    d≥ 16*p:= by assumption
    _≥ 1*p:= by gcongr; simp
    _=p:= by ring_nf
    _≥  _:=by exact hp2
    _≥ _:= by
      gcongr
      assumption
      simp
      simp

have hd3: d≥ 128*ε^2:= by
  rw [mul_comm]
  calc
    d≥ 16*p:= by assumption
    _≥ 1*p:= by gcongr; simp
    _=p:= by ring_nf
    _≥  _:=by exact hp2
    _≥ _:= by
      gcongr
      assumption
      simp
      simp

have hp1: p≥ 4*ε :=by
  calc
    p≥ _:= by exact hp2
    _≥  ε^1 *4:= by
      gcongr
      assumption
      simp
      simp
    _=_:=by ring_nf



--have pLarge: p≥ 20:= by sorry
--have prggp: pr ≥ gg2 p:= by sorry
--have hggp: h ≥ gg1 pr:= by sorry
--have κggh: κ ≥ gg1 h:= by sorry
have mggκ :m≥ gg2 κ := by
  dsimp[m]
  calc
  p * d / h + 1 ≥p * d / h:= by
    simp
  _≥  gg2 κ:= by
    refine (Nat.le_div_iff_mul_le hPositive).mpr ?_
    calc
      p*d≥ 1*d:= by
        gcongr
        assumption
      _=d:= by ring_nf
      _≥ gg2 κ *h:= by
        assumption

have mPositive: m >0:= by
  calc
    m≥ gg2 κ:= by
      assumption
    _>0:= by
      apply gg2_pos
      repeat assumption


have dm1:  h*m ≥ p*d:= by
  calc
    h*m=h* (p*d/h)+h:= by dsimp[m] ; ring_nf
    _≥ h*(p*d)/h:= by
      apply @div_assoc_le2 h (p*d) h
      exact hPositive

    _=p*d:= by exact Nat.mul_div_right (p * d) hPositive


have dm2:  m * p * 32 ≤ d:= by
  calc
    m * p * 32= (p*32)*((p*d)/h)+p*32:= by
      dsimp[m]
      ring_nf
    _≤ (p*32)*(p*d)/h+p*32:= by
      gcongr
      exact Nat.mul_div_le_mul_div_assoc (p * 32) (p * d) h
    _≤ (p*32)*(p*d)/((p^2*32)*2)+p*32:= by
      gcongr
      calc
        h≥ pr:= by
          apply gg1_ge
          repeat assumption
        _≥ 10000*p^3:= by
          apply gg1_1
          apply gg2_gg1
          repeat assumption
        _≥ 64*p^2:= by
          gcongr
          simp
          assumption
          simp
        _=_:= by
          ring_nf
    _=(p^2*32)*(d)/((p^2*32)*2)+p*32:= by
      ring_nf
    _=(p^2*32)*(d)/(p^2*32)/2+p*32:= by
      congr 1
      exact (Nat.div_div_eq_div_mul (p ^ 2 * 32 * d) (p ^ 2 * 32) 2).symm
    _=d/2+p*32:= by
      congr
      refine Nat.mul_div_right d ?_
      apply mul_pos
      exact Nat.pos_pow_of_pos 2 pPositive
      simp

    _≤ d/2+d/2:=by
      gcongr
      rw [propext (Nat.le_div_iff_mul_le' (Nat.le.step Nat.le.refl))]
      ring_nf
      assumption

    _=2*(d/2):= by ring_nf
    _≤ d:=by
      exact Nat.mul_div_le d 2


have dm3:  m ≤ d:= by
  calc
    d≥ m * p * 32:= by assumption
    _≥ m*1*1:= by
      gcongr
      assumption
      simp
    _=m:= by ring_nf


have hLex: ∃ (L : Locally_Dense G p m h),
  ∃ (R: Subgraph G),
  L.Gr⊔ R =  H
  ∧ (∀ (D: Subgraph G), (D ≤ R)→ (D.verts.toFinset.card≥ m)→ (D.verts.toFinset.card≤   h*m)→ (¬ (cut_dense G D p )))
  := by
    apply locally_dense_find
    exact κPositive
    exact pPositive
    exact hPositive
    exact prPositive
    exact prggp
    exact hggp
    exact κggh
    exact mggκ

rcases hLex with ⟨ L,Rex⟩
rcases Rex with ⟨R, hLR1, hLR2⟩

let δ:ℕ :=8*ε*ε
have δPositive: δ>0:= by
  dsimp[δ ]
  repeat rw[mul_pos]
  simp
  repeat assumption
have Rsparse:δ *R.edgeSet.toFinset.card≤  d*R.verts.toFinset.card:= by
  by_cases case: R.verts.toFinset.card= 0
  calc
    δ *R.edgeSet.toFinset.card=δ *0:= by
      congr
      simp only [ card_eq_zero]
      rw [@Set.toFinset_eq_empty]
      refine Set.eq_empty_of_forall_not_mem ?_
      intro e
      rw [@card_eq_zero] at case
      rw [@Set.toFinset_eq_empty] at case
      have hex: ∃ (x y: V), e=s(x,y):= by
        exact Sym2_to_tuple e
      rcases hex with ⟨x,y, hxy ⟩
      rw[hxy]
      simp
      by_contra cont
      have h2:x∈ R.verts:= by
        exact R.edge_vert cont
      have h3:¬ (R.verts=∅):= by
        exact ne_of_mem_of_not_mem' h2 fun a ↦ a
      exact h3 case

    _=0:= by ring_nf
    _≤ d*R.verts.toFinset.card:= by
      exact Nat.zero_le (d * R.verts.toFinset.card)

  have hnonz: R.verts.toFinset.card≥ 1:= by
    exact Nat.one_le_iff_ne_zero.mpr case
  by_contra cont
  have mindegex:∃ (K: Subgraph G),
    (K≤ R) ∧ (K.verts.Nonempty) ∧
    (∀ (v:V),(v∈ K.verts)
    →  2*δ *(K.degree v)≥d  )
    := by
      apply average_degree_implies_min_degree_4
      exact δPositive
      dsimp[δ]
      ring_nf
      calc
        d ≥ 128*ε ^ 2 := by assumption
        _≥ 16*ε ^2:= by gcongr; simp
        _=_:= by ring_nf

      --d ≥ 2 * p
      exact hnonz
      exact Nat.le_of_not_ge cont
  rcases mindegex with ⟨K, hK1, hK2, hK3 ⟩
  have no_dense_subgraphs: ¬ (∃ (D : Subgraph G), D≤ K∧ D.verts.toFinset.card≤ 2*d∧ 64*(2*δ )^2*D.edgeSet.toFinset.card≥  d^2):= by
    by_contra cont2
    rcases cont2 with ⟨ D, hD1, hD2, hD3⟩
    have hDlarge: D.verts.toFinset.card > d/((64*δ )):= by
      --ring_nf
      --rw[mul_comm]
      by_contra cont3
      simp only [not_lt] at cont3
      have ineq4: D.edgeSet.toFinset.card≥  d^2/(64*(2*δ )^2):= by
        exact Nat.div_le_of_le_mul hD3
      have ineq5: D.edgeSet.toFinset.card≤ (d/(64*δ ))^2:= by
        calc
          D.edgeSet.toFinset.card≤ D.verts.toFinset.card^2:= by
            exact lower_bound_vertices_by_edges_weaker D
          _≤ (d/(64*δ ))^2:= by
            gcongr
      have ineq6: ¬ ((d/(64*δ ))^2≥  d^2/(64*(2*δ )^2)):= by
        simp
        --ring_nf
        calc
          _=(d / (δ  * 64))*(d / (δ  * 64)):=by
            ring_nf
          _<(d / (δ  * 16))*(d / (δ * 16)):=by
            have h1: d / (δ* 64) < d / (δ * 16):= by
                refine (Nat.div_lt_iff_lt_mul ?_).mpr ?_
                apply mul_pos
                assumption
                simp

                calc
                  d / (δ * 16) * (δ * 64)
                  =4*(δ*16)*(d / (δ * 16)) :=by ring_nf
                  _>2*(δ*16)*(d / (δ * 16)):= by
                    gcongr
                    refine Nat.div_pos ?a0.hba ?a0.hb
                    --δ * 16 ≤ d
                    dsimp[δ]
                    ring_nf
                    calc
                      d ≥ 128*ε ^ 2 := by assumption
                      _=_:= by ring_nf
                    apply mul_pos
                    assumption
                    simp
                    simp



                  _≥ ((δ*16)*d) / (δ * 16):= by
                    apply @div_assoc_le1 (δ*16) d (δ*16)
                    apply mul_pos
                    assumption
                    simp
                    --δ * 16 ≤ d
                    dsimp[δ]
                    ring_nf
                    calc
                      d ≥ 128*ε ^ 2 := by assumption
                      _=_:= by ring_nf
                  _=_:=by
                    apply Nat.mul_div_right
                    apply mul_pos
                    assumption
                    simp

            gcongr
                     --

          _≤
          (d *d) / ((δ*16) *(δ*16))
          :=by
            exact Nat.div_mul_div_le d (δ * 16) d (δ * 16)
            --
          _= _:=by ring_nf

      have ineq7: (d/(64*δ))^2≥  d^2/(64*(2*δ)^2):= by
        calc
          (d/(64*δ))^2≥ D.edgeSet.toFinset.card:= by
            exact ineq5
          _≥ _:= by exact ineq4
      exact ineq6 ineq7

    have hlarge2: D.verts.toFinset.card ≥ d / 32 / (2 * δ):=by
      calc
        _≥  d/((64*δ)):= by exact Nat.le_of_succ_le hDlarge
        _= d / 32 / (2 * δ):= by
          rw [Nat.div_div_eq_div_mul]
          ring_nf
    have hlarge3: D.verts.toFinset.card ≥ (d/(32))/(2 * (4 * 64 * (2 * δ) ^ 2)):=by
      calc
        _≥  d/((64*δ)):= by exact Nat.le_of_succ_le hDlarge
        _= d / 32 / (2 * δ):= by
          rw [Nat.div_div_eq_div_mul]
          ring_nf
        _≥ (d/(32))/(2 * (4 * 64 * (2 * δ) ^ 2)):= by
          gcongr
          calc
            4 * 64 * (2 * δ) ^ 2
            =4 * 64 * (2 * δ) *(2*δ):= by
              ring_nf
            _≥ 1*1*(1*δ )*(1*1):= by
              gcongr;
              repeat simp
              assumption
            _=δ := by ring_nf

    have neg: ¬(∀ D ≤ R, D.verts.toFinset.card ≥ m → D.verts.toFinset.card ≤ h * m → ¬G.cut_dense D p):= by
      push_neg
      have hex2: ∃ (D': Subgraph G), D' ≤ D ∧ (D'.verts.toFinset.card≥ (d/(32))/(p)) ∧ cut_dense G D' (p ):= by
        apply cut_dense_existence5
        have hppos: 4*64 * (2 * δ) ^ 2 >0:= by
          calc
            4 * 64 * (2 * δ) ^ 2
            =4 * 64 * (2 * δ) *(2*δ):= by
              ring_nf
            _≥ 1*1*(1*1 )*(1*1):= by
              gcongr;
              repeat simp
              assumption
              simp
              assumption
            _=1 := by ring_nf
            _>0:= by simp
        exact hppos
        exact iSub
        exact hlarge3
        calc
          (4*64 * (2 * δ) ^ 2 ) * D.edgeSet.toFinset.card
          =(64 * (2 * δ) ^ 2 ) * D.edgeSet.toFinset.card*4:= by
            ring_nf
          _≥ d^2*4:= by
            gcongr

          _= (2*d)^2:=by
            ring_nf
          _≥ D.verts.toFinset.card ^ 2:= by
            gcongr
        --
        --p ≥ 4096 * (4 * 64 * (2 * δ) ^ 2) ^ 4
        dsimp[δ ]
        ring_nf
        --

        exact hp2
        --d / 32 ≥ 80 * (4 * 64 * (2 * δ) ^ 2) ^ 2
        dsimp[δ]
        ring_nf
        refine (Nat.le_div_iff_mul_le ?hm.k0).mpr ?hm.a
        simp
        ring_nf

        exact hd4


      rcases hex2 with ⟨CD, hCD1, hCD2, hCD3 ⟩
      have hCDgem:CD.verts.toFinset.card≥ m:= by
        calc
          CD.verts.toFinset.card
          ≥ (d/(32))/(p):= by
            exact hCD2
          _≥ m:= by
            refine (Nat.le_div_iff_mul_le pPositive).mpr ?_
            refine (Nat.le_div_iff_mul_le ?k0).mpr ?_
            simp
            -- m * p * 32 ≤ d
            assumption
      use CD
      constructor
      calc
        CD≤ D:=by assumption
        _≤ K:= by assumption
        _≤ R := by assumption
      constructor


      exact hCDgem

      constructor
      --CD.verts.toFinset.card ≤ h * m
      by_contra cont4
      simp only [  not_le] at cont4
      have hzex: ∃ (z:V), z∈ CD.verts.toFinset:= by
        have h1: CD.verts.toFinset.card>0:= by
          calc
            _≥ m:= by exact hCDgem
            _>0:= by assumption
        exact Multiset.card_pos_iff_exists_mem.mp h1
      rcases hzex with ⟨z, hz⟩
      simp at hz
      have pathex: ∃ (v: V), ∃ (P: SubgraphPath CD z v), P.Wa.length+1= d+1:= by
        apply Cut_dense_long_path
        exact pPositive
        repeat assumption
        calc
        CD.verts.toFinset.card> h * m := by assumption
        h*m ≥ p*d := by assumption

      rcases pathex with ⟨v, P, hP⟩
      simp at hP
      have haspath: Has_length_d_path H d:= by
        use z
        use v
        have PinH: P.Wa.toSubgraph≤ H:= by
          calc
            P.Wa.toSubgraph≤ CD:= by exact P.Wa_In_H
            _≤ R:= by exact le_implies_le_of_le_of_le hCD1 hK1 hD1
            _≤ H:= by rw[hLR1.symm]; simp
        let P':SubgraphPath H z v:= ⟨P.Wa, P.Wa_Is_Path, PinH ⟩
        use P'
        dsimp[P']
        simp
        exact Nat.le_of_eq (id hP.symm)--


      exact no_paths haspath

      exact hCD3
    exact neg hLR2
  --have Rnonemp: R.verts.toFinset.Nonempty:= by
  --  exact card_ne_zero.mp case
  rcases hK2 with ⟨v, hv ⟩
  have pathex: _
    :=by
      apply long_path_in_sparse_graph  K v _ d d _ hK3
      exact no_dense_subgraphs
      --d ≥ 2 * p * 8
      ring_nf
      ring_nf at hd3
      assumption
      apply mul_pos
      simp
      repeat assumption

      simp
  rcases pathex with ⟨w,P,hP1 , hP2⟩
  have ex: Has_length_d_path H d:= by
    unfold Has_length_d_path
    use v
    use w
    have PinH: P.Wa.toSubgraph≤ H:= by
          calc
            P.Wa.toSubgraph≤ K:= by exact P.Wa_In_H
            _≤ R:= by exact hK1
            _≤ H:= by rw[hLR1.symm]; simp
    let P':SubgraphPath H v w:= ⟨P.Wa, P.Wa_Is_Path, PinH ⟩
    use P'
    dsimp[P']
    simp
    exact Nat.le_of_eq (id hP1.symm)
  exact no_paths ex

have Lnonempty: L.H.Nonempty:= by
    by_contra cont6
    have h1: L.Gr.verts=∅ :=by
      rw[L.H_Partition_K.symm]
      simp
      intro Hi hHi
      have hcon:L.H.Nonempty:= by
        use Hi
      exfalso
      exact cont6 hcon
    have h2: L.Gr.verts.toFinset.card=0 :=by
      rw[h1]
      simp
    have h3: L.Gr.edgeSet=∅ := by
      by_contra cont7
      simp at cont7
      rw [@Set.eq_empty_iff_forall_not_mem] at cont7
      push_neg at cont7
      rcases cont7 with ⟨e, he⟩
      have hex: ∃ (x y: V), e=s(x,y):= by
        exact Sym2_to_tuple e
      rcases hex with ⟨x,y, hxy ⟩
      rw[hxy] at he
      simp at he
      have h4: x∈ L.Gr.verts:= by
        exact L.Gr.edge_vert he
      have h5: ¬ (L.Gr.verts=∅):= by

        exact ne_of_mem_of_not_mem' h4 fun a ↦ a
      exact h5 h1

    have h4: L.Gr.edgeSet.toFinset.card=0 :=by
      rw[h3]
      simp
    have h5: L.Gr=⊥ := by
      refine (Subgraph.ext ⊥ L.Gr (id h1.symm) ?Adj).symm
      ext x y
      simp
      by_contra cont8
      have h6: x∈ L.Gr.verts:= by
        exact L.Gr.edge_vert cont8
      have h5: ¬ (L.Gr.verts=∅):= by
        exact ne_of_mem_of_not_mem' h6 fun a ↦ a
      exact h5 h1
      --
    rw[h5] at hLR1
    simp at hLR1
    rw[hLR1] at Rsparse
    have h9: δ * H.edgeSet.toFinset.card≤ ε *H.edgeSet.toFinset.card:= by
      calc
        δ * H.edgeSet.toFinset.card≤d*H.verts.toFinset.card:= by assumption
        _≤ ε *H.edgeSet.toFinset.card:= by assumption
    have h10: ¬ (δ * H.edgeSet.toFinset.card≤ ε *H.edgeSet.toFinset.card):= by
      simp only [ not_le]
      gcongr
      dsimp[δ]
      calc
        8 * ε * ε≥ 8*1*ε :=by
          gcongr;
          assumption
        _>1*1*ε :=by
          gcongr;
          simp
        _=ε :=by ring_nf


    exact h10 h9

have clumpsnonemp: Nonempty (Clump G p m κ pr h):= by
  sorry
  --

inhabit (Clump G p m κ pr h)

have Ldec:
  ∃(Sub: Subgraph G), ∃ (Com Cov: List (Set V)),
  Components_cover_graph Sub Com
  ∧
  Components_disjoint Com
  ∧
  No_edges_between_components Sub Com
  ∧
  Components_covered_by_covers Sub Com Cov
  ∧
  Covers_small κ m Cov
  ∧
  (p*Sub.edgeSet.toFinset.card+ L.Gr.edgeSet.toFinset.card≥ p*L.Gr.edgeSet.toFinset.card)
  := by
    apply version2
    exact κPositive
    exact pPositive
    exact mPositive
    exact hPositive
    exact prPositive
    exact inhabited_h
    repeat assumption
    --L.H.Nonempty

    --¬Has_length_d_path L.Gr (h * m)
    by_contra cont5
    rcases cont5 with ⟨v, w, hvw ⟩
    rcases hvw with ⟨P, hP1⟩
    have ex: Has_length_d_path H d:= by
      unfold Has_length_d_path
      use v
      use w
      have PinH: P.Wa.toSubgraph≤ H:= by
            calc
              P.Wa.toSubgraph≤ L.Gr:= by exact P.Wa_In_H
              _≤ H:= by rw[hLR1.symm]; simp
      let P':SubgraphPath H v w:= ⟨P.Wa, P.Wa_Is_Path, PinH ⟩
      use P'
      dsimp[P']
      simp
      calc
        P.Wa.length ≥ h * m:= by exact hP1
        h * m≥ d:= by
          calc
            h*m≥ p*d:= by assumption
            _≥ 1*d:= by gcongr; assumption
            _=d:= by ring_nf

    exact no_paths ex


rcases Ldec with ⟨Sub, Com, Cov, hf1, hf2, hf3, hf4, hf5, hSub ⟩
use Sub
use Com
use Cov

constructor
assumption
constructor
assumption
constructor
assumption
constructor
assumption
constructor
--small covers
intro i hi
calc
   (Cov.get! i).toFinset.card ≤κ *m :=by
    apply hf5
    exact hi
  _≤ κ *d:= by
    gcongr
  _=_:= by rw[κeq]



--ε * Sub.edgeSet.toFinset.card + H.edgeSet.toFinset.card ≥ ε * H.edgeSet.toFinset.card




have hfin: p*ε * Sub.edgeSet.toFinset.card + p*H.edgeSet.toFinset.card ≥ p*ε * H.edgeSet.toFinset.card:= by
  calc
    p*ε * Sub.edgeSet.toFinset.card
    + p*H.edgeSet.toFinset.card
    = p*ε * Sub.edgeSet.toFinset.card
    + (p-ε +ε )*H.edgeSet.toFinset.card:= by
      congr
      refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
      --p ≥ ε
      calc
        p≥ 4*ε:= by assumption
        _≥ 1*ε:= by gcongr; simp
        _=ε:= by ring_nf
    _=
     p*ε * Sub.edgeSet.toFinset.card
    + ((p-ε )*H.edgeSet.toFinset.card
    +ε *H.edgeSet.toFinset.card):= by
      congr
      apply  Nat.add_mul
    _=
    ε *(p * Sub.edgeSet.toFinset.card+H.edgeSet.toFinset.card)
    +(p-ε )*H.edgeSet.toFinset.card:= by
      ring_nf
    _≥
    ε *(p * Sub.edgeSet.toFinset.card+L.Gr.edgeSet.toFinset.card)
    +(p-ε )*H.edgeSet.toFinset.card:= by
      gcongr
      simp
      rw[hLR1.symm]
      simp
    _≥ ε *(p *L.Gr.edgeSet.toFinset.card)
    +((p/(4*ε))*ε) *H.edgeSet.toFinset.card:= by
      gcongr
      calc
         p / (4 * ε) * ε
         =ε *(p / (4 * ε)):= by
          ring_nf
         _≤(ε *p)  / (4 * ε) := by
          exact Nat.mul_div_le_mul_div_assoc ε p (4 * ε)
         _=(ε *p)  / ( ε*4) := by
          ring_nf
         _=(ε *p)  / ε /4:= by
          exact (Nat.div_div_eq_div_mul (ε * p) ε 4).symm
         _=((ε/ε )*p)/4:=by
          congr
          refine (Nat.div_eq_iff_eq_mul_left ?_ ?_).mpr ?_
          assumption
          simp
          rw[Nat.div_self]
          ring_nf
          assumption
         _=p/4:= by
          rw[Nat.div_self]
          ring_nf
          assumption
         _≤ p - ε:= by
          refine Nat.div_le_of_le_mul ?_
          rw [Nat.mul_sub_left_distrib]
          apply Nat.le_sub_of_add_le
          rw[add_comm]
          apply  Nat.add_le_of_le_sub
          calc
           4*p≥ 1*p:= by gcongr; simp
           _=p:= by ring_nf
          calc
            4*p-p=4*p-1*p:= by ring_nf
            _=(4-1)*p:= by exact (Nat.mul_sub_right_distrib 4 1 p).symm
            _=3*p:=by simp
            _≥ 1*p:= by gcongr; simp
            _=p:=by ring_nf
            p≥ 4*ε := by assumption





    _=  ε *(p *L.Gr.edgeSet.toFinset.card)
    +(p/(4*ε))*(ε *H.edgeSet.toFinset.card):=by
      ring_nf
    _≥ ε *(p *L.Gr.edgeSet.toFinset.card)
    +(p/(4*ε))*(d *H.verts.toFinset.card):=by
      gcongr
    _≥ ε *(p *L.Gr.edgeSet.toFinset.card)
    +(p/(4*ε))*(d *R.verts.toFinset.card):=by
      gcongr
      rw[hLR1.symm]
      simp
    _≥ε *(p *L.Gr.edgeSet.toFinset.card)
    +(p/(4*ε))*(δ   *R.edgeSet.toFinset.card):= by
      gcongr ε *(p *L.Gr.edgeSet.toFinset.card) +(p/(4*ε))*?_
      --
    _=ε *(p *L.Gr.edgeSet.toFinset.card)
    +(p/(4*ε)*δ   *R.edgeSet.toFinset.card):= by
      ring_nf
    _≥ ε *(p *L.Gr.edgeSet.toFinset.card)
    +(p* ε *R.edgeSet.toFinset.card):= by
      gcongr ε *(p *L.Gr.edgeSet.toFinset.card) +(?_ *R.edgeSet.toFinset.card)
      dsimp[δ]
      calc
        p / (4 * ε) * (8 * ε * ε)=(2*(4*ε ))*(p/(4*ε))*ε:= by
          ring_nf
        _≥ ((4*ε )*p)/(4*ε)*ε:= by
          gcongr ?_*ε
          apply @div_assoc_le1 (4*ε ) p (4*ε )
          apply mul_pos
          simp
          assumption
          --p ≥ 4 * ε
          assumption
        _=p*ε := by
          congr
          refine Nat.mul_div_right p ?_
          apply mul_pos
          simp
          assumption
        _=_:= by ring_nf

    _= ε *p *(L.Gr.edgeSet.toFinset.card
    + R.edgeSet.toFinset.card):= by
      ring_nf
    _≥ ε *p *(H.edgeSet.toFinset.card):= by
      gcongr
      have h1: H.edgeSet.toFinset=L.Gr.edgeSet.toFinset ∪ R.edgeSet.toFinset:= by
        rw[hLR1.symm]
        simp
      rw[h1]
      exact card_union_le L.Gr.edgeSet.toFinset R.edgeSet.toFinset

    _=_:=by ring_nf






by_contra cont9
simp only [not_le] at cont9
have h1:  ¬ (p * ε * Sub.edgeSet.toFinset.card + p * H.edgeSet.toFinset.card ≥  p * ε * H.edgeSet.toFinset.card):= by
  simp only [not_le]
  calc
    p * ε * Sub.edgeSet.toFinset.card + p * H.edgeSet.toFinset.card
    =p*(ε * Sub.edgeSet.toFinset.card +H.edgeSet.toFinset.card):=by
      ring_nf
    _<p * (ε * H.edgeSet.toFinset.card):= by
      gcongr
    _=_:= by ring_nf
exact h1 hfin




/-



lemma initial_clump_construction_2
{L: Subgraph G}
(hLorderm: L.verts.toFinset.card ≥ m)
(hLorderhm: L.verts.toFinset.card ≤  h*m)
(hL: cut_dense G L p)
--(pLarge: p≥ 20)
--(mggpr: m≥ gg1 pr)
(prggp: pr ≥ gg2 p)
(hggp: h ≥ gg1 pr)
(κggh: κ ≥ gg1 h)
(mggκ :m≥ gg2 κ )
:
∃ (X: Clump G p m κ pr h), graph_forms_clump L X



lemma Cut_dense_long_path
(H: Subgraph G)
(H_cut_dense: cut_dense G H p)
(u: V)
(u_in_H: u ∈ H.verts)
(d: ℕ)
(hd: p*d < H.verts.toFinset.card)
:
∃ (v: V), ∃ (P: SubgraphPath H u v), P.Wa.length+1= d+1



theorem average_degree_implies_min_degree_subgraph (hd: d>0)(n: ℕ ): (H: Subgraph G)→ (hOrder: Fintype.card (H.verts)=n+1)→  (hAverageDeg: Fintype.card (H.edgeSet)≥ d*(n+1))→ ( ∃ (K: Subgraph G), (∀ (v:V),(v∈ K.verts)→ Fintype.card (K.neighborSet v)≥d  )):= by



 lemma long_path_in_sparse_graph
(H: Subgraph G)
(v: V)

(hv: v∈ H.verts)
(k d: ℕ )
(hk:k ≤ d)
(min_degree: ∀ v : V, v∈ H.verts → p*H.degree v ≥ d)
(no_dense_subgraphs: ¬ (∃ (D : Subgraph G), D≤ H∧ D.verts.toFinset.card≤ 2*d∧ 64*p^2*D.edgeSet.toFinset.card≥  d^2))
(dggp: d≥ p*8)
--∀ (D : Subgraph G), D≤ H→ D.verts.toFinset.card≤ 2*d→ γ*D.edgeSet.toFinset.card≤ d^2)
:
∃ (w: V), ∃ (P: SubgraphPath H v w),
P.Wa.length=k
∧
4*p*((H.neighborSet w)\ {x:V| x∈ P.Wa.support}).toFinset.card ≥ d
:


lemma locally_dense_find
(H: Subgraph G)
:
∃ (L : Locally_Dense G p m h),
∃ (R: Subgraph G),
L.Gr⊔ R =  H
∧ (∀ (D: Subgraph G), (D ≤ R)→ (D.verts.toFinset.card≥ m)→ (D.verts.toFinset.card≤   h*m)→ (¬ (cut_dense G D p )))
:= by


theorem version2
(L: Locally_Dense G p m h)
(LNonempty: L.H.Nonempty )
(no_paths: ¬ Has_length_d_path (L.Gr) (h*m))
:
∃ (f: V→ Set V), ∃ (Sub: Subgraph G),
(∀ (x: V), Sub.neighborSet x ⊆  f x)
∧ (∀ ( x y: V), f x ≠ f y → (Disjoint (f x) (f y)))
∧ (∀ (x: V), (f x).toFinset.card≤ (κ *m))
∧ (p*Sub.edgeSet.toFinset.card+ L.Gr.edgeSet.toFinset.card≥ p*L.Gr.edgeSet.toFinset.card)
:=by
sorry
-/
