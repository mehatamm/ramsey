import order.monotone.basic
import init.data.fin.basic
import order.hom.basic
import tactic
import set_theory.cardinal.finite
import combinatorics.pigeonhole
import finramsey

noncomputable theory 
open finset

variables {α : Type*} [linear_order α]



@[reducible] def p_edge (C : finset α) (p : ℕ):= powerset_len p C

lemma p_edge_card {C : finset α} {p : ℕ} {edge: finset α} (h: edge ∈ p_edge C p) : edge.card = p:=
begin
  apply (finset.mem_powerset_len.1 h).2,
end

@[reducible] def p_edge_in_ss (C : finset α) (ss : finset α) (p : ℕ)
: finset (finset α):=
finset.filter (λ e, e ⊆ ss) (p_edge C p)
--{e ∈ p_edge C p | e ⊆ ss}

lemma p_edge_in_ss_subset (C : finset α) (ss : finset α) (p : ℕ):
p_edge_in_ss C ss p ⊆ p_edge C p:=
begin
  apply finset.filter_subset, 
end


lemma p_edge_in_ss_card {C : finset α} {ss : finset α} {p : ℕ} {edge : finset α} (h: edge ∈ p_edge_in_ss C ss p):
edge.card = p:= p_edge_card ((p_edge_in_ss_subset C ss p) h)

lemma p_nonempty (C : finset α) (ss : finset α) {p : ℕ} (h: 0 < p) : ∀ edge ∈ p_edge_in_ss C ss p, finset.nonempty edge:=
begin
  intros e einss, have:= p_edge_in_ss_card einss, apply finset.card_pos.1, linarith,
end

def p_edge_from_in_ss (C : finset α) (ss : finset α) (p : ℕ) (v : α) (h: ∀ edge ∈ p_edge_in_ss C ss p, finset.nonempty edge):
finset (finset α):= -- all p-edges from a given vertex within a subset
finset.filter (λ edge, if mem: edge ∈ p_edge_in_ss C ss p then finset.min' edge (h edge mem) = v else false) (p_edge_in_ss C ss p)

lemma p_edge_from_ss_ss {C : finset α} {ss : finset α} {p : ℕ} {ppos: 0 < p} {v : α} {edge : finset α}
(h: edge ∈ p_edge_from_in_ss C ss p v (p_nonempty C ss ppos)): edge ⊆ ss:=
begin
  cases finset.mem_filter.1 h with edge_in_ss prop, cases finset.mem_filter.1 edge_in_ss, exact right,
end


lemma p_edge_from_card {C : finset α} {ss : finset α} {p : ℕ} {ppos: 0 < p} {v : α} {edge : finset α}
(h: edge ∈ p_edge_from_in_ss C ss p v (p_nonempty C ss ppos)): edge.card = p:=
begin
  cases mem_filter.1 h with edge_in_ss edge_min_v, exact p_edge_in_ss_card edge_in_ss,
end

lemma edge_nonempty {C : finset α} {ss : finset α} {p : ℕ} {edge : finset α} (ppos : 0 < p)
(h: edge ∈ p_edge_in_ss C ss p): edge.nonempty:=
begin
  apply finset.card_pos.1, have:= p_edge_in_ss_card h, linarith,
end

lemma p_edge_from_mem {C : finset α} {ss : finset α} {p : ℕ} {ppos : 0 < p} {v : α} {edge : finset α}
(h: edge ∈ p_edge_from_in_ss C ss p v (p_nonempty C ss ppos)): v ∈ edge:=
begin
  cases mem_filter.1 h with edge_in_ss edge_min_v, 
  rw dif_pos edge_in_ss at edge_min_v, rw ← edge_min_v, 
  exact finset.min'_mem edge (edge_nonempty ppos edge_in_ss),
end

lemma p_edge_from_min {C : finset α} {ss : finset α} {p : ℕ} {ppos: 0 < p} {v : α} {edge : finset α}
(h: edge ∈ p_edge_from_in_ss C ss p v (p_nonempty C ss ppos)) (edge_none: edge.nonempty):edge.min' edge_none = v:=
begin
  cases mem_filter.1 h with edge_in_ss edge_min_v, 
  rw dif_pos edge_in_ss at edge_min_v, apply edge_min_v, 
end

lemma p_edge_in_ss_from_v_in_ss {C : finset α} {ss : finset α} {p : ℕ} {ppos : 0 < p} {edge : finset α}
(h: edge ∈ p_edge_in_ss C ss p):
∃ v ∈ ss, edge ∈ p_edge_from_in_ss C ss p v (p_nonempty C ss ppos):=
begin
  have edge_none:=edge_nonempty ppos h,
  use finset.min' edge edge_none, refine ⟨(finset.mem_filter.1 h).2 (finset.min'_mem edge edge_none), _⟩,
  apply finset.mem_filter.2, refine ⟨h, _⟩, rw dif_pos h, 
end

lemma p_edge_from_ss_edge_from_ss {C : finset α} {ss_1 : finset α} {ss_2 : finset α} {p : ℕ} {ppos : 0 < p} {v : α}
(h_ss: ss_1 ⊆ ss_2) {edge : finset α} (h: edge ∈ p_edge_from_in_ss C ss_1 p v (p_nonempty C ss_1 ppos)):
edge ∈ p_edge_from_in_ss C ss_2 p v (p_nonempty C ss_2 ppos):=
begin
  apply finset.mem_filter.2, cases mem_filter.1 h with edge_in_ss edge_min_v, rw dif_pos edge_in_ss at edge_min_v,
  have: edge ∈ p_edge_in_ss C ss_2 p, apply finset.mem_filter.2, cases mem_filter.1 edge_in_ss, 
  exact ⟨left, finset.subset.trans right h_ss⟩, simp [this, edge_min_v],
end


def p_fav_in_ss (C : finset α) (ss : finset α) {p : ℕ} {c : ℕ} (f : finset α → fin c) (ppos: 0 < p) (v : α):=
∃ color : fin c, ∀ edge ∈ p_edge_from_in_ss C ss p v (p_nonempty C ss ppos), f edge = color

lemma f_aux_match {c : ℕ} (f: finset α → fin c) {edge: finset α} {v_1 : α} (v_1_in_edge: v_1 ∈ edge) (color : fin c):
(λ edge : finset α, f (insert v_1 edge)) (edge.erase v_1) = color → f edge = color:=
begin
  dsimp, rw finset.insert_erase v_1_in_edge, simp,
end


lemma genprocession (p k c : ℕ)
(ramsey: ∀ k : ℕ, ∃ (n₀ : ℕ), ∀ (C : finset α), n₀ ≤ C.card → ∀ (f : finset α → fin c),
 ∃ (color : fin c) (clique : finset α) (H : clique ⊆ C),
  k ≤ clique.card ∧ ∀ (edge : finset α), edge ∈ p_edge_in_ss C clique p → f edge = color)
: --write fav first
∃ n₀ : ℕ, ∀ C : finset α, n₀ ≤ C.card → ∀ f : finset α → fin c, ∃ Y ⊆ C,
Y.card = k ∧ ∀ v ∈ Y, p_fav_in_ss C Y f (nat.zero_lt_succ p) v:=
begin
  induction k with k ih, 
  {
    use 0, intros C Ccard f, use finset.empty, 
    refine ⟨finset.empty_subset C, finset.card_empty, _⟩, intros v vinempty,
    have:= finset.not_mem_empty v, contradiction,
  },
  cases ih with n₁ hn₁, cases ramsey n₁ with n₀ hn₀, use n₀+1, intros C Ccard f,
  have C_none: C.nonempty, apply finset.card_pos.1, linarith,
  set v_1:= C.min' C_none, set C_right:= C.erase (v_1),
  have C_right_card: n₀ ≤ C_right.card,
  linarith[finset.card_erase_of_mem (finset.min'_mem C C_none), le_tsub_of_add_le_right Ccard],
  set f_aux: finset α → fin c:= λ edge, f (insert v_1 edge),
  rcases hn₀ C_right C_right_card f_aux with ⟨color, clique, ⟨clique_ss, clique_card, clique_color⟩⟩,
  rcases hn₁ clique clique_card f with ⟨favs, favs_ss, favs_card, favs_colors⟩,
  have favs_ss_C_right: favs ⊆ C_right:= λ x xinf, (clique_ss (favs_ss xinf)),
  have favs_ss_C: favs ⊆ C:= λ x xinf, (finset.mem_erase.1 (favs_ss_C_right xinf)).2,
  set procession:=finset.cons v_1 favs (finset.not_mem_mono favs_ss_C_right (finset.not_mem_erase v_1 C)),
  use procession, have proc_ss_C:=finset.cons_subset.2 ⟨finset.min'_mem C C_none, favs_ss_C⟩,
   refine ⟨proc_ss_C, _, _⟩,
  rw ← favs_card, apply finset.card_cons _, intros v vinp,
  cases finset.mem_cons.1 vinp with v_v1 v_favs, rw v_v1, use color, intros edge edge_from_proc_v,
  have emv_card: (edge.erase(v_1)).card = p,{
    have edge_card:= p_edge_from_card edge_from_proc_v, 
    have:= finset.card_erase_of_mem (p_edge_from_mem edge_from_proc_v), rw this, rw edge_card,
    exact nat.succ_sub_one p,
  },
  have emv_in_p_C_right: edge.erase(v_1) ∈ p_edge_in_ss C_right clique p, apply finset.mem_filter.2, 
  split, {
    apply finset.mem_powerset_len.2, refine ⟨_, emv_card⟩,
    exact finset.erase_subset_erase v_1 (finset.subset.trans (p_edge_from_ss_ss edge_from_proc_v) proc_ss_C),
  },
  have proc_erase_ss_clique: procession.erase(v_1) ⊆ clique, apply finset.subset.trans _ favs_ss, apply finset.subset_of_eq,
  apply finset.erase_cons _, apply finset.subset.trans _ proc_erase_ss_clique, 
  exact finset.erase_subset_erase v_1 (p_edge_from_ss_ss edge_from_proc_v),
  exact f_aux_match f (p_edge_from_mem edge_from_proc_v) color (clique_color (edge.erase v_1) emv_in_p_C_right),
  cases favs_colors v v_favs with v_color h_v_color, use v_color, intros edge edge_in_proc,
  have edge_card:= p_edge_from_card edge_in_proc, have edge_ss_proc:= p_edge_from_ss_ss edge_in_proc,
  have edge_none: edge.nonempty, apply finset.card_pos.1, rw edge_card, exact nat.zero_lt_succ _,
  have v_min:= p_edge_from_min edge_in_proc edge_none,
  have v_1_not_mem: v_1 ∉ edge, 
  {
    intros v_1_edge,  
    have v_1_lt_v: v_1 < v := finset.min'_lt_of_mem_erase_min' C C_none (favs_ss_C_right v_favs),
    apply absurd v_1_edge (finset.not_mem_of_lt_min v_1_lt_v _), 
    rw ←finset.coe_min' edge_none, rw v_min, 
  },
  have edge_ss_favs: edge ⊆ favs,
  {
    intros v v_edge, cases finset.mem_cons.1 (edge_ss_proc v_edge) with v_eq_v_1 v_favs,
    rw v_eq_v_1 at v_edge, contradiction, exact v_favs,
  },
  have edge_in_from_favs: edge ∈ p_edge_from_in_ss clique favs p.succ v (p_nonempty _ _ (nat.zero_lt_succ p)),
  {
    apply finset.mem_filter.2, have e_in_favs : edge ∈ p_edge_in_ss clique favs p.succ,
    {
      apply finset.mem_filter.2, split, apply finset.mem_powerset_len.2,
      refine ⟨finset.subset.trans edge_ss_favs favs_ss, edge_card⟩, exact edge_ss_favs,
    },
    rw dif_pos e_in_favs, exact ⟨e_in_favs, v_min⟩,
  },
  exact h_v_color edge edge_in_from_favs,
end

#check p_edge_in_ss_from_v_in_ss

theorem genramsey: 
∀ p c k : ℕ, ∃ n₀ : ℕ, ∀ C : finset α, n₀ ≤ C.card → ∀ f : finset α → fin c, ∃ color : fin c,
∃ clique ⊆ C, (k ≤ clique.card ∧ ∀ edge ∈ p_edge_in_ss C clique p, f edge = color):=
begin
  intros p c, cases nat.eq_zero_or_eq_succ_pred c with c0 cp, 
  {
    intro k, use 0, rw c0, intros C C_card f, have:=f C, apply fin_zero_elim this, 
  },
  haveI: inhabited (fin c), rw cp, apply fin.inhabited,
  haveI: nonempty (fin c), apply nonempty_of_inhabited,
  induction p with p hp, intro k, use k,
  intros C card f, set fe:= f ∅,
  use fe, use C, refine ⟨finset.subset.refl C, card, _⟩, intros edge einss,
  rw finset.card_eq_zero.1 (p_edge_in_ss_card einss),  
  intro k, cases genprocession p (c*k) c hp with n₀ hn₀, use n₀, intros C C_card f, 
  rcases hn₀ C C_card f with ⟨Y, Y_ss, Y_card, Y_fav⟩,
  have y2finc: fintype.card (fin c) * k ≤ Y.card, rw fintype.card_fin c, linarith,
  choose! fn h_fn using Y_fav, 
  cases finset.exists_le_card_fiber_of_mul_le_card_to_type fn y2finc with color hc,
  set clique:= finset.filter (λ (x : α), fn x = color) Y,
  have csuby: clique ⊆ Y:= finset.filter_subset (λ (x : α), fn x = color) Y,
  use [color, clique], refine ⟨finset.subset.trans csuby Y_ss, hc, _⟩, intros edge edge_in_clique,
  rcases p_edge_in_ss_from_v_in_ss edge_in_clique with ⟨v, vclique, hv⟩, swap, exact nat.zero_lt_succ p,
  rw finset.mem_filter at vclique, rw ←vclique.2, exact h_fn v vclique.1 edge (p_edge_from_ss_edge_from_ss csuby hv),
end
