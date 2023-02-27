import order.monotone.basic
import init.data.fin.basic
import order.hom.basic
import tactic
import set_theory.cardinal.finite
import combinatorics.pigeonhole
import finramsey

noncomputable theory 
open finset

variables {α : Type*} [preorder α]



@[reducible] def p_edge (c : finset α) (p : ℕ):= powerset_len p c

lemma p_edge_card {c : finset α} {p : ℕ} (edge ∈ p_edge c p) : edge.card = p:=
begin
  apply (finset.mem_powerset_len.1 H).2, 
end

def p_edge_in_ss (c : finset α) (ss : finset α) (p : ℕ)
: finset (finset α):=
{e ∈ p_edge c p | e ⊆ ss}

lemma p_edge_in_ss_subset (c : finset α) (ss : finset α) (p : ℕ):
p_edge_in_ss c ss p ⊆ p_edge c p:=
begin
  apply finset.filter_subset, 
end

theorem genramsey {α : Type*} [preorder α]: 
∀ p s t : ℕ, ∃ n₀ : ℕ, ∀ c : finset α, n₀ ≤ c.card → ∀ f : finset α → fin 2,
∃ clique ⊆ c, (s = clique.card ∧ ∀ edge ∈ p_edge_in_ss c clique p, f edge = 0) ∨ (t = clique.card ∧ ∀ edge ∈ p_edge_in_ss c clique p, f edge = 1):=
begin
  intros p s t, induction p with p hp, use max s t,
  intros c card f, cases mem_fin_2 (f finset.empty), have:= le_of_max_le_left card, 
  rcases exists_smaller_set c s this with ⟨clique, cliquess, cliquecard⟩,  
  refine ⟨clique, cliquess, _⟩, left, refine ⟨cliquecard.symm, _⟩, intros edge einss,
  rw ← h, congr, apply finset.card_eq_zero.1 (p_edge_card edge (p_edge_in_ss_subset c clique 0 einss)),
  have:= le_of_max_le_right card, 
  rcases exists_smaller_set c t this with ⟨clique, cliquess, cliquecard⟩,  
  refine ⟨clique, cliquess, _⟩, right, refine ⟨cliquecard.symm, _⟩, intros edge einss,
  rw ← h, congr, apply finset.card_eq_zero.1 (p_edge_card edge (p_edge_in_ss_subset c clique 0 einss)),
  
   
end
