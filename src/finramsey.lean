import order.monotone.basic
import init.data.fin.basic
import order.hom.basic
import tactic
import set_theory.cardinal.finite
import combinatorics.pigeonhole


#check order_embedding

noncomputable theory 
open_locale classical 
variables {α β γ : Type*} [preorder α] [preorder β] [preorder γ]

def order_embedding.refl : α ↪o α:=
  (order_iso.refl α).to_order_embedding

def order_embedding.comp (f: α ↪o β) (g: β ↪o γ)
: α ↪o γ:=
{ to_fun := g ∘ f,
  inj' := function.injective.comp g.inj' f.inj',
  map_rel_iff' := by simp }

@[simp] lemma order_embedding.comp_apply (f: α ↪o β) (g: β ↪o γ) (x : α) :
  f.comp g x = g (f x) :=
by {unfold order_embedding.comp, refl}

@[simp] lemma order_embedding.refl_comp (f: α ↪o β):
  order_embedding.refl.comp f = f :=
begin
  ext, refl,
end

def order_embedding.of_is_empty {a b : Type*} [preorder a] [preorder b] [is_empty a] : a ↪o b :=
⟨function.embedding.of_is_empty, is_empty_elim⟩


instance order_embedding.fintype [fintype α] [fintype β] : fintype (α ↪o β) := 
@fintype.of_finite (α ↪o β)
  (@finite.of_injective (α ↪o β) (α → β) _ (λ f, (f : α → β)) (fun_like.coe_injective))

@[simp] lemma order_embedding.comp_refl (f: α ↪o β):
  f.comp order_embedding.refl = f :=
begin
  ext, refl,
end

lemma mem_fin_2 (x : fin 2) : x = 0 ∨ x = 1 :=
begin
  cases x, cases x_val, left, refl,
  cases x_val, right, refl,
  exfalso, repeat {rw nat.succ_lt_succ_iff at x_property}, norm_num at x_property,
end

instance embedding_unique_of_linear_order {k : ℕ} : unique (fin k ↪o fin k):=
begin
  refine ⟨⟨order_embedding.refl⟩, _⟩, intro a, apply fin.order_embedding_eq, repeat {rw function.surjective.range_eq},
  all_goals{ apply finite.injective_iff_surjective.1 _, apply fintype.finite, apply fin.fintype, exact (_ : fin k ↪o fin k).inj', },
end

@[reducible] def E (n : ℕ): Type := fin 2 ↪o fin n --no longer used

--instance edge_order {n : ℕ} : linear_order (E n):= sorry

variables {η ζ : Type*}
theorem finset.exists_le_card_fiber_of_mul_le_card_to_type [decidable_eq ζ] [fintype ζ] [nonempty ζ] {s : finset η} (f : η → ζ) {n : ℕ} (hn : fintype.card ζ * n ≤ s.card) :
∃ (y : ζ), n ≤ (finset.filter (λ (x : η), f x = y) s).card:=
begin
  set t: finset ζ:= finset.univ with t_def, have hf: ∀ a: η, a ∈ s → f a ∈ t:= by simp, 
  have ht: t.nonempty, rw finset.nonempty, simp, 
  rw ← finset.card_univ at hn, rw ← t_def at hn,
  rcases finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hf ht hn with ⟨y, h, hy⟩,
  use y, apply hy,
end


def order_embedding_equiv_finset {α : Type*} [linear_order α] (k : ℕ) : 
  {s : finset α // s.card = k} ≃ (fin k ↪o α) := 
{ to_fun := λ p, finset.order_emb_of_fin p.1 p.2,
  inv_fun := λ f, ⟨(set.range f).to_finset, 
  begin
    convert fintype.card_range (f.to_embedding) using 1, swap, simp, 
    simp only [set.to_finset_range, rel_embedding.coe_fn_to_embedding, fintype.card_of_finset], 
    congr, 
    ext, simp, 
  end ⟩   ,
  left_inv := begin
    rintro ⟨s, hs⟩, simp, 
  end ,
  right_inv := begin
    intro f, 
    simp only [set.to_finset_range], 
    rw ←finset.order_emb_of_fin_unique', simp, 
  end  } 

@[reducible] def edge : Type:= fin 2 ↪o ℕ

def edge_of {i j : ℕ} (h : i < j) : edge:= --disgusting, do not use definitionally
{ to_fun := λ x, if xe0: x = 0 then i else j,
  inj' := begin
    intros x y xyeq, cases mem_fin_2 x, {
      cases mem_fin_2 y, 
      {
        simp[h_1, h_2],
      },
      simp only [h_1, h_2, eq_self_iff_true, dite_eq_ite, if_true, fin.one_eq_zero_iff, nat.succ_succ_ne_one, if_false] at xyeq,
      apply absurd xyeq (ne_of_lt h),
    },
    cases mem_fin_2 y,
    {
      simp only [h_1, h_2, eq_self_iff_true, dite_eq_ite, if_true, fin.one_eq_zero_iff, nat.succ_succ_ne_one, if_false] at xyeq,
      apply absurd xyeq.symm (ne_of_lt h),
    },
    simp [h_1, h_2],
  end,
  map_rel_iff' := begin
    intros x y, cases mem_fin_2 x,{
      cases mem_fin_2 y, 
      {
        simp [h_1, h_2],
      },
      simp [h_1, h_2, h, le_of_lt], 
    },
    cases mem_fin_2 y,
    {
      simp [h_1, h_2, h, le_of_lt],
    },
    simp [h_1, h_2],
  end}

theorem edge_of_0 {i j : ℕ} (h : i < j) : (edge_of h) 0 = i:=
begin
  rw edge_of, simp,
end

theorem edge_of_1 {i j : ℕ} (h : i < j) : (edge_of h) 1 = j:=
begin
  rw edge_of, simp,
end

instance edges_from_finset_fin (Y: finset ℕ) (v : ℕ) : fintype {e : edge | e 0 = v ∧ e 1 ∈ Y} :=
begin
  set f : {e : edge | e 0 = v ∧ e 1 ∈ Y} → Y := λ e, ⟨e.1 1, e.2.2⟩ with hfdef, 
  have hf : f.injective, 
  { rintros ⟨x,⟨hx,hx'⟩⟩ ⟨y,⟨hy,hy'⟩⟩ hxy, simp [hfdef] at hxy, ext a, cases mem_fin_2 a, rw h, simp [hx, hy], rw h, simp [hxy], },
  apply fintype.of_injective f hf,
end 

@[reducible] def edges_from_finset (Y: finset ℕ) (v : ℕ) : finset edge := 
  set.to_finset {e : edge | e 0 = v ∧ e 1 ∈ Y}


lemma edges_from_finset_subset (Y s: finset ℕ) (v : ℕ) (hs: s ⊆ Y) : edges_from_finset s v ⊆ edges_from_finset Y v:=
begin
  intros e esv, rw set.mem_to_finset at esv ⊢, use [esv.1, hs esv.2], 
end

-- example {α : Type} (f : α → β) (hf : f.injective) (s : finset β) (h : ∀ a, f a ∈ s) : finite α :=
-- begin
  
-- end  

lemma edges_from_finset_card (Y: finset ℕ) {v k : ℕ} (hvy : ∀ y ∈ (Y.erase v), v < y):
(Y.erase v).card ≤ (edges_from_finset Y v).card:=
begin
  set f : ℕ → edge := λ x, if h: x ∈ (Y.erase v) then edge_of (hvy x h) else edge_of (nat.lt_succ_self x) with f_def,
  apply @finset.card_le_card_of_inj_on _ _ (Y.erase v) (edges_from_finset Y v) f,
  {
    intros a aye, rw f_def, simp [aye],
    have e0:= edge_of_0 (hvy a aye), have e1:= edge_of_1 (hvy a aye), simp [e0, e1, aye], exact finset.mem_of_mem_erase aye,
  },
  intros a aye b bye fabeq, rw f_def at fabeq,
  simp [aye, bye] at fabeq, have a1:= edge_of_1 (hvy a aye), have b1:= edge_of_1 (hvy b bye),
  rw fabeq at a1, rw b1 at a1, exact a1.symm, 
end 

@[reducible] def has_fav (f : edge → fin 2) (Y : finset ℕ):= 
∀ y ∈ Y, ∃ c : fin 2,
∀ e ∈ (edges_from_finset Y y), f e = c

lemma favcolor_fixed (k : ℕ): 
∃ n₀: ℕ, ∀ X : finset ℕ, n₀ ≤ X.card  → ∀ f: edge → fin 2, ∃ Y ⊆ X,
Y.card = k ∧ has_fav f Y :=
begin
  induction k with k ih,
  {
    use 0, intros x xg f, use finset.empty, refine ⟨finset.empty_subset x, finset.card_empty, _⟩, 
    intros y yinf, apply absurd yinf (finset.not_mem_empty y),
  },
  cases ih with n₀ hn₀, use 2*n₀+1, intros X Xcge f,
  have xnone: X.nonempty, apply finset.card_pos.1, linarith,
  set xmin:= X.min' xnone,
  set xfmin:= edges_from_finset X xmin, 
  have xfc: (X.erase xmin).card ≤ xfmin.card, apply edges_from_finset_card X (λ y yxe, finset.min'_lt_of_mem_erase_min' X xnone yxe),
  exact xmin, rw (finset.card_erase_of_mem (finset.min'_mem X xnone)) at xfc,
  have xfcn: 2*n₀ ≤ xfmin.card, linarith [finset.card_pos.2 xnone], --finally fully proved cardinality!
  have pigeonhole: ∃ friends : (finset edge), friends ⊆ xfmin ∧ n₀ ≤ friends.card ∧ ∃ c : fin 2, ∀ e ∈ friends, f e = c,
  {
    cases finset.exists_le_card_fiber_of_mul_le_card_to_type f xfcn with y hy,
    use finset.filter (λ (x : edge), f x = y) xfmin,
    refine ⟨_, hy, _⟩, exact finset.filter_subset (λ (x : edge), f x = y) xfmin,
    use y, intros e emem, exact (finset.mem_filter.1 emem).2,
  },
  rcases pigeonhole with ⟨friends, fss, fcard, ⟨color, fcolor ⟩ ⟩,
  set friendvs:= finset.image (λ x : edge, x 1) friends,
  have vinj: set.inj_on (λ (x : edge), x 1) friends, {
    intros x xf y yf xyv, ext, cases mem_fin_2 x_1,
    have xfm: x ∈ xfmin, apply fss xf, have yfm: y ∈ xfmin, apply fss yf,
    rw h, simp at xfm yfm, simp [xfm, yfm], rw h, dsimp at xyv, rw xyv,
  },
  have fvcard : friendvs.card = friends.card := finset.card_image_of_inj_on vinj, rw ← fvcard at fcard,
  rcases hn₀ friendvs fcard f with ⟨y, yss, yc, yf⟩,
  have fvx: friendvs ⊆ X,
  {
    intros v vfvs, rw finset.mem_image at vfvs, rcases vfvs with ⟨a, af, ha⟩, 
    have a1x:= (set.mem_to_finset.1 (fss af)).2, rw ha at a1x, exact a1x,
  },
  have xmny: xmin ∉ y, 
  {
    intro xmy, rcases (finset.mem_image.1 (yss xmy)) with ⟨a, af, a1⟩, 
    have a0:=(set.mem_to_finset.1 (fss af)).1, rw ← a1 at a0, 
    apply absurd (a.inj' a0) zero_ne_one, 
  },
  set Z:= finset.cons xmin y xmny, use Z, refine ⟨_, _, _⟩,
  {
    refine finset.cons_subset.2 ⟨_, _⟩, exact finset.min'_mem X xnone,
    exact finset.subset.trans yss fvx, 
  },
  {
    rw finset.card_cons xmny, rw yc, 
  },
  {
    intros vertex vz, cases finset.mem_cons.1 vz, use color, intros e efz, rw h at efz, 
    apply fcolor e, cases (set.mem_to_finset.1 efz) with e0m e1z, cases finset.mem_cons.1 e1z with e1m e1y, 
    rw ← e0m at e1m, apply absurd (e.inj' e1m).symm zero_ne_one,
    rcases (finset.mem_image.1 (yss e1y)) with ⟨a, af, a1⟩, have aeqe: a = e, 
    { ext, cases mem_fin_2 x, rw h_1, rw (set.mem_to_finset.1 (fss af)).1,
      exact e0m.symm, rw h_1, exact a1,
    },
    rw ← aeqe, exact af,
    cases yf vertex h with c hc, use c, intros e efz, cases (set.mem_to_finset.1 efz) with e0m e1z,
    cases finset.mem_cons.1 e1z with e1m e1y, have e0x: e 0 ∈ X, rw e0m, exact fvx (yss h),
    have e1le0: e 1 ≤ e 0, rw e1m, apply finset.min'_le X (e 0) e0x, have:= e.map_rel_iff'.1 e1le0, 
    norm_num at this, have eefy: e ∈ edges_from_finset y vertex, apply set.mem_to_finset.2, 
    use [e0m, e1y], exact hc e eefy, 
  },
end



#check function.surjective.range_eq
#check finite.injective_iff_surjective
#check fin_zero_elim

#check fintype.exists_le_card_fiber_of_mul_le_card
#check finset.order_emb_of_fin

--@[reducible] def favcolorfun {y: finset ℕ} {f: edge → fin 2} (h: has_fav f y): ℕ → fin 2:=
--λ x, if hx: x ∈ y then classical.some (h x hx) else ⊥

#check edges_from_finset_subset

theorem finramsey: 
∀ k: ℕ,  ∃ n₀: ℕ, ∀ n : finset ℕ, n₀ ≤ n.card → 
∀ f: edge → fin 2,
∃ s ⊆ n, k ≤ s.card ∧
∃ c : fin 2, ∀ v ∈ s, ∀ e ∈ edges_from_finset s v, f e = c:=
begin
  intro k, cases favcolor_fixed (2*k) with n₀ hn₀, use n₀, intros n ncard f, 
  rcases hn₀ n ncard f with ⟨y, ysubn, yc, yfav⟩, 
  have ycfinc: fintype.card (fin 2) * k ≤ y.card, rw fintype.card_fin 2, linarith,
  set favcolorfun: ℕ → fin 2:= λ x, if hx: x ∈ y then classical.some (yfav x hx) else ⊥ with favcolorfun_def,
  cases finset.exists_le_card_fiber_of_mul_le_card_to_type (favcolorfun) ycfinc with color hc,
  set clique:= finset.filter (λ (x : ℕ), favcolorfun x = color) y,
  have csuby: clique ⊆ y:= finset.filter_subset (λ (x : ℕ), favcolorfun x = color) y,
  use clique, refine ⟨finset.subset.trans csuby ysubn, hc, _⟩,
  use color, intros v vclique e eefromsv, rw finset.mem_filter at vclique, cases vclique with vy vcolor,
  rw favcolorfun_def at vcolor, simp [vy] at vcolor, 
  have ecsy:= edges_from_finset_subset y clique v csuby,
  have spec:= classical.some_spec (yfav v vy) e (ecsy eefromsv), 
end