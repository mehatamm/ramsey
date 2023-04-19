import tactic.interactive
import .order_emb
import order.order_iso_nat
import data.finset.sort
import .seq_refine


noncomputable theory
open_locale classical

/-!
# The canonical Ramsey theorem
-/

/-!
### Vocabulary
-/

/-- An edge of the complete `d`-uniform hypergraph on `ℕ`. -/
@[reducible] def edge (d : ℕ) : Type* := fin d ↪o ℕ

instance edge_infinite {d : ℕ} : infinite (edge d.succ):=
begin
  set f: ℕ → edge d.succ:= λ x, rel_embedding.trans (@fin.add_nat d.succ x) (fin.coe_order_embedding (d.succ+x)) with f_def,
  have f_inj: f.injective, intros x y xyeq, rw rel_embedding.ext_iff at xyeq, simp [f_def] at xyeq, assumption,
  apply infinite.of_injective f f_inj,
end

instance : unique (edge 0):=
begin
  refine  ⟨⟨_⟩, _⟩, use λ x, fin_zero_elim x, intro a, apply fin_zero_elim a, intro a, apply fin_zero_elim a,
  intro a, ext, apply fin_zero_elim x,
end

instance {d : ℕ} : inhabited (edge d):=
begin
  refine ⟨_⟩, use λ x, x, intros a b abeq, rw fin.ext_iff, exact abeq, 
  intros a b, simp,
end

lemma edge_le_self {d : ℕ} {i : fin d} {e : edge d}: (i : ℕ) ≤ e i:=
begin
  suffices: ∀ (x : ℕ) (h: x < d), x ≤ e ⟨x, h⟩, have ile:= this i i.2, apply le_trans ile, 
  apply le_of_eq, congr, ext, refl, intro x, induction x with x h_x, intro h, apply nat.zero_le _,
  intro h, have ih:= h_x (nat.lt_of_succ_lt h), have:= e.map_rel_iff'.2 _, swap, exact ⟨x, nat.lt_of_succ_lt h⟩, swap,
  exact ⟨x.succ, h⟩, swap, rw fin.mk_le_mk, apply nat.le_succ, have:= lt_of_le_of_ne this _, 
  apply nat.succ_le_of_lt (lt_of_le_of_lt ih this), intro h_f, have:= e.inj' h_f, apply nat.succ_ne_self x, 
  symmetry, rw fin.mk_eq_mk at this, exact this,
end

@[reducible] def edge_force {d : ℕ} {i : fin d} (x : {n : ℕ // (i : ℕ) ≤ n}): edge d:=
{ to_fun := λ n, (x : ℕ) - (i : ℕ) + n,
  inj' := begin
    intros a b, rw fin.ext_iff, simp,
  end,
  map_rel_iff' := begin
    intros a b, simp,
  end }

@[simp] lemma edge_force_at {d : ℕ} {i : fin d} {x : {n : ℕ // (i : ℕ) ≤ n}}:
(edge_force x) i = x:=
begin
  simp, exact nat.sub_add_cancel x.2,
end

/--
A set of indices for endpoints of a generic edge, identified by their
relative positions with respect to the ordering on `ℕ`. For example,
"the 1st, 3rd, and 4th smallest vertices contained in the edge".
-/
@[reducible] def index_set (d : ℕ) : Type* := set (fin d)

/--
A colouring of the complete `d`-uniform hypergraph on `ℕ`,
with colours taken from `α`.
-/
@[reducible] def colouring (d : ℕ) (α : Type*) : Type* := edge d → α


/-!
### Notation
-/

variables {α β γ : Type*} {d : ℕ}

/--
The actual endpoints of a specific edge identified by an index set.
For example, the restriction of the 5-uniform edge (2, 3, 5, 7, 11)
to the index set "1st, 3rd, and 4th smallest" is (2, 5, 7).
-/
def edge.restrict (e : edge d) (I : index_set d) : I ↪o ℕ :=
rel_embedding.trans (order_embedding.subtype I) e

infix ` |e `:80 := edge.restrict

/--
For a given index set, the canonical colouring in which two edges have
the same colour iff they agree on that index set.
-/
def index_set.canonical (I : index_set d) : colouring d (I ↪o ℕ) :=
λ e, e |e I

def index_set.cast (I : index_set d) : index_set d.succ:= set.image (fin.succ) I


/--
The restriction of a colouring to the edges contained in a given
infinite subsequence of `ℕ`.
-/
def colouring.restrict (f : colouring d α) (S : subseq) : colouring d α :=
λ e, f (rel_embedding.trans e S)

infix ` |c `:80 := colouring.restrict

/--
Two colourings are isomorphic iff they induce the same partition on
the set of edges of the `d`-uniform hypergraph on `ℕ`.
-/
def colouring.iso (f : colouring d α) (g : colouring d β) : Prop :=
∀ e₁ e₂, (f e₁ = f e₂) ↔ (g e₁ = g e₂)

infix ` ≃c `:25 := colouring.iso

/-!
### Main statements
-/

/--
The (statement of the) canonical Ramsey theorem:
every colouring contains a canonical subcolouring.
-/
def ramsey.statement (f : colouring d α) : Prop :=
∃ (S : subseq) (I : index_set d), f |c S ≃c I.canonical

/-!
The next two lemmas show that `ramsey.statement` is best possible:
each canonical colouring is a distinct fixed point for the operation
of passing to an infinite subsequence of ℕ.
-/

/-- Every subcolouring of a canonical colouring is isomorphic. -/
def canonical_subseq_iso_self.statement (I : index_set d) (S : subseq) : Prop :=
I.canonical |c S ≃c I.canonical

/-- Isomorphic canonical colourings come from identical index sets. -/
def canonical_inj.statement (I J : index_set d) : Prop :=
I.canonical ≃c J.canonical → I = J

/-!
### Constructions and lemmas
-/

/- `≃c` is an equivalence relation. -/
namespace colouring.iso
variables {f : colouring d α} {g : colouring d β} {h : colouring d γ}

@[refl] lemma refl (f : colouring d α) : f ≃c f :=
λ x y, iff.rfl

@[symm] lemma symm : (f ≃c g) → (g ≃c f) :=
λ fg x y, (fg x y).symm

@[trans] lemma trans : (f ≃c g) → (g ≃c h) → (f ≃c h) :=
λ fg gh x y, (fg x y).trans (gh x y)

end /-namespace-/ colouring.iso

/--
A subsequence of a subsequence is a subsequence.
This order of arguments makes `colouring.restrict_restrict` hold.
-/
def subseq.restrict (S T : subseq) : subseq :=
rel_embedding.trans T S

infix ` |s `:80 := subseq.restrict

lemma colouring.restrict_restrict (f : colouring d α) (S T : subseq) :
  f |c S |c T = f |c (S |s T) := rfl

/-- The first `d` endpoints of a `(d+1)`-edge. -/
def edge.head (e : edge (d+1)) : edge d :=
rel_embedding.trans fin.cast_succ e

/-- The last endpoint of a `(d+1)`-edge. -/
def edge.last (e : edge (d+1)) : ℕ := e (fin.last d)

/--
The smallest natural number which is
strictly bigger than all endpoints.
-/
def edge.lub : ∀ {d : ℕ}, edge d → ℕ
| 0     _ := 0
| (d+1) e := (e (fin.last d)) + 1

lemma edge.lt_lub (e : edge d) (i : fin d) :
  e i < e.lub :=
begin
  cases d,
  { exact fin.elim0 i },
  calc e i ≤ e (fin.last d) : e.le_iff_le.mpr (fin.le_last i)
  ...      < e.lub          : lt_add_one (e (fin.last d)),
end

lemma edge.head_lub_le_last (e : edge (d+1)) :
  e.head.lub ≤ e.last :=
begin
  cases d,
  { exact zero_le _ },
  change edge (d+2) at e, change (e ⟨d, _⟩) < e ⟨d+1, _⟩,
  simp only [e.lt_iff_lt, fin.mk_lt_mk, lt_add_one],
end

lemma edge.lub_le_iff {n : ℕ} (e : edge d) : 
  e.lub ≤ n ↔ ∀ i, e i < n := 
begin
  refine ⟨λ h i, (e.lt_lub _).trans_le h,λ h, _⟩, 
  cases d, exact nat.zero_le _, 
  exact nat.lt_iff_add_one_le.mpr (h _), 
end    

lemma edge.le_of_lub_eq {n : ℕ} (e : edge d) :
  e.lub = n → ∀ i, e i < n :=
begin
  intro lub_eq, exact e.lub_le_iff.1 (le_of_eq lub_eq),
end


/--
The `(d+1)`-edge formed from a `d`-edge
by adding a new largest endpoint.
-/
def edge.of_lub_le (e : edge d) (n : ℕ) (h : e.lub ≤ n) : edge (d+1) :=
order_embedding.of_map_le_iff (@fin.last_cases _ (λ _, ℕ) n e)
begin
  rw [edge.lub_le_iff] at h,  
  refine @fin.last_cases _ _ _ (λ a, _), 
  all_goals {refine @fin.last_cases _ _ _ (λ b, _)},
  all_goals {simp only [fin.last_cases_last, fin.last_cases_cast_succ, fin.last_le_iff, rfl.le, 
    order_embedding.le_iff_le]}, 
  { exact iff_of_false (h _).not_le (b.cast_succ_lt_last.ne)}, 
  exact iff_of_true (h _).le (a.cast_succ_lt_last.le),   
end 
-- begin
--   intros i j,
--   obtain (h_last_le_i | h_i_lt_last) := le_or_lt (fin.last d) i,
--   {
--     rw fin.last_le_iff at h_last_le_i,
--     rw [h_last_le_i, fin.last_cases_last],
--     cases le_or_lt (fin.last d) j with h_last_le_j h_j_lt_last,
--     {
--       rw fin.last_le_iff at h_last_le_j,
--       rw [h_last_le_j, fin.last_cases_last],
--       exact iff_of_true (le_refl n) (le_refl (fin.last d)),
--     },
--     {
--       set j' : fin d := j.cast_lt h_j_lt_last,
--       have : j'.cast_succ = j := j.cast_succ_cast_lt _,
--       rw [←this, fin.last_cases_cast_succ],
--       apply iff_of_false; apply not_le_of_lt,
--       calc e j' < e.lub : e.lt_lub j'
--       ...       ≤ n     : h,
--       exact j'.cast_succ_lt_last,
--     },
--   },
--   {
--     set i' : fin d := i.cast_lt h_i_lt_last,
--     have : i'.cast_succ = i := (i.cast_succ_cast_lt _),
--     rw [←this, fin.last_cases_cast_succ],
--     cases le_or_lt (fin.last d) j with h_last_le_j h_j_lt_last,
--     {
--       rw fin.last_le_iff at h_last_le_j,
--       rw [h_last_le_j, fin.last_cases_last],
--       apply iff_of_true; apply le_of_lt,
--       calc e i' < e.lub : e.lt_lub i'
--       ...       ≤ n     : h,
--       exact i'.cast_succ_lt_last,
--     },
--     {
--       set j' : fin d := j.cast_lt h_j_lt_last,
--       have : j'.cast_succ = j := j.cast_succ_cast_lt _,
--       rw [←this, fin.last_cases_cast_succ],
--       simp_rw [order_embedding.le_iff_le],
--     },
--   },
-- end

@[simp] lemma edge.of_lub_le_head_eq (e : edge d) (n : ℕ) (h : e.lub ≤ n) :
  (edge.of_lub_le e n h).head = e :=
by {ext, simp [edge.of_lub_le, edge.head]}

@[simp] lemma edge.of_lub_le_last_eq (e : edge d) (n : ℕ) (h : e.lub ≤ n) :
  (edge.of_lub_le e n h) (fin.last d) = n :=
by {simp [edge.of_lub_le, edge.last]}

/-!
### Some API
-/



@[ext] lemma edge.ext {e₁ e₂ : edge d} (h : ∀ i, e₁ i = e₂ i) : e₁ = e₂ := 
by {ext, rw h}

@[simp] lemma index_set_apply (e : edge d) (I : index_set d) (i : I) :
  (e |e I) i = e i := rfl 

lemma iso_canonical_iff {I : index_set d} {f : colouring d α} :
  f ≃c I.canonical ↔ ∀ e₁ e₂, f e₁ = f e₂ ↔ ∀ (i : I), e₁ i = e₂ i := 
begin
  unfold colouring.iso index_set.canonical,
  simp_rw rel_embedding.ext_iff,
  refl, 
end 
 
def edge_one_equiv:  ℕ ≃ (edge 1):=
{ to_fun := λ x, finset.order_emb_of_fin {x} (finset.card_singleton x),
  inv_fun := λ x, x 0,
  left_inv := begin
    intro x, simp,
  end,
  right_inv := begin
    intro x, ext, simp,
  end }

lemma trans_range (e : edge d) (s : set ℕ) [infinite s]: 
set.range (rel_embedding.trans e (nat.order_embedding_of_set s)) ⊆ s:=
begin
  intros x xr, rw set.mem_range at xr, cases xr with y hy, 
  rw rel_embedding.trans_apply at hy, rw ← nat.order_embedding_of_set_range s,
  rw set.mem_range, use (e y), apply hy,
end

lemma trans_inj (a b : edge d) (S : subseq) (h: a ≠ b): rel_embedding.trans a S ≠rel_embedding.trans b S:=
begin
  intro req, rw rel_embedding.ext_iff at req, simp_rw [rel_embedding.trans_apply] at req, simp [S.inj'] at req, 
  rw ←rel_embedding.ext_iff at req, contradiction, 
end

lemma equiv_trans_mem_order_emb_set (s : set ℕ) [infinite s]:
∀ a : edge 1, edge_one_equiv.symm (rel_embedding.trans a (nat.order_embedding_of_set s)) ∈ s:=
begin
  intro a, unfold edge_one_equiv, simp, 
end

/-!
### Main proofs
-/

#check finite.exists_infinite_fiber
#check nat.order_embedding_of_set


theorem polychromatic_pigeonhole {α β : Type} [infinite α] (f : α → β):
(∃ y : β, (f ⁻¹' {y}).infinite) ∨ (set.range f).infinite:=
begin
  by_cases (set.range f).infinite, right, assumption,
  left, rw set.not_infinite at h,
  set f_aux : α → set.range f:= λ α, ⟨f α, set.mem_range_self α⟩,
  haveI r_f: finite (set.range f), apply @finite.of_fintype _ _, apply set.finite.fintype h,
  cases @finite.exists_infinite_fiber _ _ _ r_f f_aux with y hy, use y,
  have : f ⁻¹' {y} = f_aux ⁻¹' {y}, ext, simp [f_aux], split, intro fxy, ext, apply fxy, 
  intro fxy, have :f x ∈ set.range f, apply set.mem_range_self x, rw ← fxy, simp [this],
  rw this, apply set.infinite_coe_iff.1 hy,
end

--ended up being useful due to me making a bit of a planning error

lemma seq_mono_poly {α : Type} (f: colouring 1 α) : ∃ S: subseq, --ended up being quite long
(∀ a b : edge 1, (f |c S) a = (f |c S) b) ∨
(∀ a b : edge 1, a ≠ b → (f |c S) a ≠ (f |c S) b)
:=
begin
  rcases polychromatic_pigeonhole f with ⟨y, hy⟩, set pm:= {x: ℕ | edge_one_equiv x ∈ (f ⁻¹' {y})} with pm_def,
  haveI: infinite pm, set f_pm: pm → f ⁻¹' {y}:= λ x, ⟨edge_one_equiv x.val, x.property⟩ with f_pm_def,
  have f_pm_surj: f_pm.surjective, intro z, use edge_one_equiv.symm z.val, 
  simp only [subtype.val_eq_coe, set.mem_set_of_eq, equiv.apply_symm_apply, set.mem_preimage, set.mem_singleton_iff], 
  have:= set.mem_preimage.1 z.2, apply set.eq_of_mem_singleton this, rw f_pm_def, 
  simp only [subtype.val_eq_coe, equiv.apply_symm_apply, subtype.coe_eta],
  apply @infinite.of_surjective _ _ (set.infinite_coe_iff.2 hy) f_pm f_pm_surj,
  set S:= nat.order_embedding_of_set pm, use S, left, intros a b, 
  have fr: set.range (f |c S) = {y}, unfold colouring.restrict,
  ext, rw set.mem_singleton_iff, rw set.mem_range, have pm_y: ∀ (e : edge 1), set.range e ⊆ pm → f e = y,
  intros e epm, have e0pm:= epm (set.mem_range_self 0), rw [pm_def, set.mem_set_of] at e0pm,
  rw set.mem_preimage at e0pm, rw set.mem_singleton_iff at e0pm, have: f (edge_one_equiv (e 0))= f e, congr, unfold edge_one_equiv, ext,
  simp, rw ← this, exact e0pm,
  split, rintros ⟨z, hz⟩, rw ← hz, apply pm_y (rel_embedding.trans z S) (trans_range z pm),
  intros xeqy, rw xeqy, use a, apply pm_y (rel_embedding.trans a S) (trans_range a pm),
  suffices: ∀ e : edge 1, (f |c S) e = y, rw [this b, this a], intro e,
  rw ← set.mem_singleton_iff, rw ← fr, exact set.mem_range_self e,
  have f_range_choose: ∀ n ∈ set.range f, ∃ e : (edge 1), f e = n:= λ e ein, set.mem_range.1 ein,
  choose! fn h_fn using f_range_choose, set s:= {x : ℕ | edge_one_equiv x ∈ (fn '' (set.range f))}, 
  --have: ∀ x : s, f (edge_one_equiv x) ∈ 
  haveI s_inf: infinite s, set f_s: s → set.range f:= λ x, ⟨f (edge_one_equiv x), set.mem_range_self _⟩ with f_s_def,
  apply @infinite.of_surjective _ _ (set.infinite_coe_iff.2 h) f_s _, intro x, use edge_one_equiv.symm (fn x.val),
  rw set.mem_set_of, simp only [subtype.val_eq_coe, equiv.apply_symm_apply, set.mem_image,
  set.mem_range, exists_exists_eq_and], cases set.mem_range.1 x.prop with y hy, use y,
  rw hy, rw f_s_def, dsimp, ext, have: f (fn x)= x:= h_fn x x.2, simp [this],
  set S:= nat.order_embedding_of_set s, use S, right, intros a b aneb faefb,
  unfold colouring.restrict at faefb, have rel_ne:= trans_inj a b S aneb, 
  have equiv_mem:= equiv_trans_mem_order_emb_set s, 
  simp_rw [set.mem_set_of, set.mem_image] at equiv_mem, 
  simp only [set.mem_range, equiv.apply_symm_apply, exists_exists_eq_and] at equiv_mem, 
  cases equiv_mem a with a_1 ha_1, cases equiv_mem b with b_1 hb_1,
  rw [← ha_1, ← hb_1] at faefb, rw h_fn (f a_1) (set.mem_range_self a_1) at faefb,
  rw h_fn (f b_1) (set.mem_range_self b_1) at faefb, rw faefb at ha_1, rw hb_1 at ha_1,
  apply rel_ne, exact ha_1.symm, 
end


def edge.monochromatic {d : ℕ} (e: edge d) (f: colouring (d+1) α):=
(∀ a b : ℕ, ∀ h_a : e.lub ≤ a, ∀ h_b : e.lub ≤ b,    
f (e.of_lub_le a h_a) = f (e.of_lub_le b h_b))

def edge.monochromatic' {d : ℕ} (e : edge d) (f : colouring (d+1) α):=
∃ y, ∀ a (ha : e.lub ≤ a), f (e.of_lub_le a ha) = y

lemma edge.monochromatic_equiv {d : ℕ} {e : edge d} {f : colouring (d+1) α}:
e.monochromatic f ↔ e.monochromatic' f:=
begin
  unfold edge.monochromatic, unfold edge.monochromatic', split,
  {
    intro h, use f (e.of_lub_le e.lub (le_refl _)), intros a h_a, exact h a e.lub h_a (le_refl _),
  },
  {
    intro h, cases h with y h_y, intros a b h_a h_b, rw h_y a h_a, rw h_y b h_b,
  },
end

def edge.polychromatic {d : ℕ} (e: edge d) (f: colouring (d+1) α):=
(∀ a b : ℕ, ∀ h_a : e.lub ≤ a, ∀ h_b : e.lub ≤ b, a ≠ b →
f (e.of_lub_le a h_a) ≠ f (e.of_lub_le b h_b)) 

lemma edge.lub_map {d : ℕ} (e : edge d) (a : ℕ) (S : subseq):
(e.lub ≤ a) ↔ edge.lub (rel_embedding.trans e S) ≤ S a:=
begin
  simp_rw [edge.lub_le_iff] at *, split, intros h i,  rw rel_embedding.trans_apply _ _, apply lt_of_le_of_ne _ _, 
  apply S.map_rel_iff.2 (le_of_lt (h i)), intro h_f, apply ne_of_lt (h i) (S.inj' h_f), 
  intros h i, apply lt_of_le_of_ne _ _, apply S.map_rel_iff.1 (le_of_lt (h i)), intro h_f,
  have:= h i, rw rel_embedding.trans_apply _ _ at this, rw h_f at this, apply (lt_self_iff_false _).1 this,
end

lemma edge.restrict_distribute {d : ℕ} (e : edge d) (a : ℕ) (h_a: e.lub ≤ a) (S : subseq):
rel_embedding.trans (e.of_lub_le a h_a) S = (edge.of_lub_le (rel_embedding.trans e S) (S a) ((e.lub_map a S).1 h_a)):=
begin
  ext, revert i, refine fin.last_cases _ _, simp, intro i, simp [edge.of_lub_le],
end

lemma edge.monochromatic_restrict {d : ℕ} (e : edge d) (f : colouring (d+1) α) (S : subseq)
:
(((λ e, e.monochromatic f) : colouring (d) Prop) |c S) e → e.monochromatic (f |c S):=
begin
  unfold edge.monochromatic at *, unfold colouring.restrict at *, intros h a b h_a h_b, 
  have:= h (S a) (S b) ((edge.lub_map e a S).1 h_a) ((edge.lub_map e b S).1 h_b), 
  repeat {rw e.restrict_distribute _ _ S}, exact this, /-intros h a b h_a h_b,
  have:= h a b ((e.lub_map a S).2 (le_trans h_a (S.le_self a))) ((e.lub_map b S).2 (le_trans h_b (S.le_self b))),
  repeat {rw e.restrict_distribute _ _ S at this},-/
end

lemma edge.monochromatic_restrict' {d : ℕ} (e : edge d) (f : colouring (d+1) α) (S : subseq)
:
(∀ e_2, ¬ (((λ e_1, e_1.monochromatic f) : colouring (d) Prop) |c S) e_2) → ¬ edge.monochromatic (rel_embedding.trans e S) (f):=
begin
  unfold edge.monochromatic at *, unfold colouring.restrict at *, intros h_1 h_2, apply h_1 e,
  intros a b h_a h_b, apply h_2 a b h_a h_b,
end

lemma edge.polychromatic_stable_apply {d : ℕ} (e : edge d) (f : colouring (d+1) α) (S : subseq)
(h: edge.polychromatic (rel_embedding.trans e S) f): e.polychromatic (f |c S):=
begin
  unfold colouring.restrict, unfold edge.polychromatic at *, intros a b h_a h_b aneb faneb,
  apply aneb, have:= h (S a) (S b) ((edge.lub_map e a S).1 h_a) ((edge.lub_map e b S).1 h_b) _,
  repeat {rw e.restrict_distribute _ _ S at faneb}, exfalso, apply this faneb,
  intro h_f, apply aneb, exact S.inj' h_f,
end

@[reducible] def preserving_pre_piecewise (l : ℕ) (pre : set ℕ) [infinite pre] 
(subtype_prop : ∀ x : ℕ, l ≤ nat.subtype.of_nat pre x)
: subseq:=
{ to_fun := λ x : ℕ, if h: l ≤ x then (nat.order_embedding_of_set pre) x else (@rel_embedding.refl ℕ (≤)) x,
  inj' := begin
    intros a b abeq, cases decidable.em (l ≤ a) with l_le_a l_gt_a, 
    {
      cases decidable.em (l ≤ b) with l_le_b l_gt_b,
      {
        simp only [l_le_a, l_le_b, function.comp_app, dite_eq_ite, if_true] at abeq,
        exact (nat.order_embedding_of_set pre).inj' abeq,  
      },
      {
        simp only [l_le_a, l_gt_b, function.comp_app, dite_eq_ite, if_true, if_false] at abeq,
        simp at abeq, have:= subtype_prop a, rw abeq at this, exact absurd this l_gt_b,
      },
    },
    cases decidable.em (l ≤ b) with l_le_b l_gt_b,
    {
      simp [l_gt_a, l_le_b, function.comp_app, dite_eq_ite, if_true, if_false] at abeq,
      have:= subtype_prop b, rw ← abeq at this, apply absurd this l_gt_a,
    },
    {
      simp only [l_gt_a, l_gt_b, function.comp_app, dite_eq_ite, if_false] at abeq,
      exact abeq,
    },
  end,
  map_rel_iff' := begin
    intros a b, cases decidable.em (l ≤ a) with l_le_a l_gt_a,
    {
      cases decidable.em (l ≤ b) with l_le_b l_gt_b,
      {
        simp only [l_le_a, l_le_b, dite_eq_ite, if_true, function.embedding.coe_fn_mk,
  subtype.coe_le_coe], exact (nat.order_embedding_of_set pre).map_rel_iff',
      },
      {
        simp only [l_le_a, l_gt_b, dite_eq_ite, if_true, nat.coe_order_embedding_of_set, function.comp_app,
  rel_embedding.refl_apply, if_false, function.embedding.coe_fn_mk], 
        have:= subtype_prop a, split,
        intro h_f, exact absurd (le_trans this h_f) l_gt_b, intro h_f, 
        exact absurd (le_trans l_le_a h_f) l_gt_b,
      },
    },
    {
      cases decidable.em (l ≤ b) with l_le_b l_gt_b,
      {
        simp [l_gt_a, l_le_b, function.comp_app, dite_eq_ite, if_true, if_false],
      have:= subtype_prop b, split, intro h, apply le_trans (le_of_not_le l_gt_a) l_le_b,
      intro h, apply le_trans (le_of_not_le l_gt_a) this,
      },
      {
        simp [l_gt_a, l_gt_b, function.comp_app, dite_eq_ite, if_false],
      },
    },
  end }

lemma restrict_assoc {d : ℕ} {f : colouring (d+1) α} {S T : subseq} {e : edge (d+1)}:
(f |c rel_embedding.trans T S) e = (f |c S) (rel_embedding.trans e T):=
begin
  unfold colouring.restrict, congr, 
end

lemma trans_of_lub_preserving {d n x : ℕ} {e : edge d} (h_n : n.succ = e.lub)
{T : subseq} (h_t: n_preserving n T) (h_x : e.lub ≤ x):
rel_embedding.trans (e.of_lub_le x h_x) T = e.of_lub_le (T x) (le_trans h_x (T.le_self x)):=
begin
  ext, revert i, refine fin.last_cases _ _, simp [edge.of_lub_le], simp [edge.of_lub_le],
  intro i, have:= e.lt_lub i, unfold n_preserving at h_t, rw ← h_n at this,
  exact h_t (e i) (nat.le_of_lt_succ this),
end


lemma preserving_pre_not_le {l x : ℕ} {pre : set ℕ} [infinite pre]
{subtype_prop : ∀ x : ℕ, l ≤ nat.subtype.of_nat pre x} (h: ¬ l ≤ x) :
(preserving_pre_piecewise l pre subtype_prop) x = x:=
begin
  unfold preserving_pre_piecewise, simp [h],
end

lemma preserving_pre_piecewise_preserving {l n : ℕ} (h_n : l = n.succ) {pre : set ℕ} [infinite pre]
{subtype_prop : ∀ x : ℕ, l ≤ nat.subtype.of_nat pre x} : n_preserving n (preserving_pre_piecewise l pre subtype_prop):=
begin
  intros x x_le, have l_gt_x: ¬ (l ≤ x), rw h_n, rw not_le, exact nat.lt_succ_iff.2 x_le,
  exact preserving_pre_not_le l_gt_x,
end


lemma seq_mono_poly_preserving {α : Type} {d : ℕ} (n : ℕ) (e : edge d) (h_e : e.lub = n.succ) (f : colouring (d+1) α) (S : subseq):
∃ T : subseq, n_preserving n T ∧ 
(e.monochromatic (f |c rel_embedding.trans T S) ∨ e.polychromatic (f |c rel_embedding.trans T S)):=
begin
  set lub_le:= {x : ℕ // e.lub ≤ x},
  set f_color: lub_le → α:= λ x, (f |c S) (e.of_lub_le x.1 x.2) with f_color_def,
  haveI: infinite lub_le, 
  {
    set nat_to_lub_le: ℕ → lub_le:= λ x : ℕ, ⟨x+e.lub, self_le_add_left _ _⟩,
    apply infinite.of_injective nat_to_lub_le, intros a b abeq, 
    rw subtype.ext_iff_val at abeq, apply (add_left_inj e.lub).1 abeq,
  },
  rcases polychromatic_pigeonhole f_color with ⟨y, h_y⟩, 
  set pre: set ℕ:= set.image (λ x : lub_le, x.1) (f_color ⁻¹' {y}),
  haveI prei: pre.infinite, apply (set.infinite_image_iff _).2 h_y, intros a h_a b h_b abeq, 
  exact subtype.ext_iff_val.2 abeq, haveI: infinite pre, apply set.infinite_coe_iff.2 prei, 
   have pre_mem_lub: ∀ x ∈ pre, e.lub ≤ x,
  intros x h_x, cases (set.mem_image _ _ _).1 h_x with z h_z, rw ← h_z.2, exact z.2,
  have pre_mem_f_color: ∀ (x : ℕ) (h_x : x ∈ pre), f_color ⟨x, pre_mem_lub x h_x⟩ = y, 
  {
    intros x h_x, have mem_pre: (⟨x, pre_mem_lub x h_x⟩: lub_le) ∈ (f_color ⁻¹' {y}),
    apply (function.injective.mem_set_image _).1, 
    exact h_x, intros a b abeq, exact subtype.ext_iff_val.2 abeq, exact set.mem_preimage.1 mem_pre,
  },
  have subtype_prop: ∀ x : ℕ, e.lub ≤ (nat.subtype.of_nat pre x),
  {
    intro x, exact pre_mem_lub (nat.subtype.of_nat pre x) (nat.subtype.of_nat pre x).2,
  },
  set T:=preserving_pre_piecewise e.lub pre subtype_prop,
  use T,
  refine ⟨preserving_pre_piecewise_preserving h_e, _⟩,
  {
    left, intros a b h_a h_b, have e_mono: ∀ (x : ℕ) (h_x: e.lub ≤ x), (f |c rel_embedding.trans T S) (e.of_lub_le x h_x) = y,
    {
      intros x h_x, rw restrict_assoc, rw trans_of_lub_preserving h_e.symm (preserving_pre_piecewise_preserving h_e) h_x,
      simp [h_x], rw f_color_def at pre_mem_f_color, apply pre_mem_f_color (nat.subtype.of_nat pre x) (nat.subtype.of_nat pre x).2,
    },
    rw e_mono a h_a, rw e_mono b h_b,
  },
  have f_range_choose: ∀ n ∈ set.range f_color, ∃ e : lub_le, f_color e = n := λ e ein, set.mem_range.1 ein,
  choose! fn h_fn using f_range_choose, 
  set pre: set ℕ:= set.image (λ x : lub_le, x.1) (set.image fn (set.range f_color)),
  haveI prei: pre.infinite, 
  {
    apply (set.infinite_image_iff _).2, apply (set.infinite_image_iff _).2, 
    apply h, intros a h_a b h_b abeq, have: f_color (fn a) = f_color (fn a):=rfl,
    nth_rewrite 0 abeq at this, rw h_fn a h_a at this, rw h_fn b h_b at this, exact this.symm,
    intros a h_a b h_b abeq, rw subtype.ext_iff_val, apply abeq,
  },
  haveI: infinite pre, apply set.infinite_coe_iff.2 prei,
  have pre_mem_lub: ∀ x ∈ pre, e.lub ≤ x,
  {
    intros x h_x, cases (set.mem_image _ _ _).1 h_x with z h_z, rw ← h_z.2, exact z.2,
  },
  have pre_mem_f_color: ∀ (x y : ℕ) (h_x : x ∈ pre) (h_y : y ∈ pre) (h_xy : x ≠ y), 
  f_color ⟨x, pre_mem_lub x h_x⟩ ≠ f_color ⟨y, pre_mem_lub y h_y⟩, 
  {
    intros x y h_x h_y h_xy, have mem_pre: ∀ x (h_x: x ∈ pre), (⟨x, pre_mem_lub x h_x⟩: lub_le) ∈ (set.image fn (set.range f_color)),
    intros x h_x, apply (function.injective.mem_set_image _).1, exact h_x, 
    intros a b abeq, exact subtype.ext_iff_val.2 abeq, intro h_f, apply h_xy, 
    cases (set.mem_image _ _ _).1 (mem_pre x h_x) with a h_a,
    cases (set.mem_image _ _ _).1 (mem_pre y h_y) with b h_b, 
    rw ←(h_a.2) at h_f, rw ←(h_b.2) at h_f, rw h_fn a h_a.1 at h_f, rw h_fn b h_b.1 at h_f,
    rw h_f at h_a, rw h_b.2 at h_a, rw subtype.ext_iff_val at h_a, exact h_a.2.symm,
  },
  have subtype_prop: ∀ x : ℕ, e.lub ≤ (nat.subtype.of_nat pre x),
  {
    intro x, exact pre_mem_lub (nat.subtype.of_nat pre x) (nat.subtype.of_nat pre x).2,
  },
  set T:=preserving_pre_piecewise e.lub pre subtype_prop,
  use T,
  refine ⟨preserving_pre_piecewise_preserving h_e, _⟩, right,
  intros a b h_a h_b h_ab, repeat {rw restrict_assoc}, 
  rw trans_of_lub_preserving h_e.symm (preserving_pre_piecewise_preserving h_e) h_a,
  rw trans_of_lub_preserving h_e.symm (preserving_pre_piecewise_preserving h_e) h_b,
  simp [h_a, h_b], repeat {rw f_color_def at pre_mem_f_color},
  apply pre_mem_f_color (nat.subtype.of_nat pre a) (nat.subtype.of_nat pre b) (nat.subtype.of_nat pre a).2 (nat.subtype.of_nat pre b).2 _,
  intro h_false, apply h_ab, repeat {rw ← nat.order_embedding_of_set_apply at h_false},
  apply (nat.order_embedding_of_set pre).inj' h_false, 
end


def constraints {d : ℕ} (f : colouring (d+1) α) : ℕ → subseq → Prop:=
λ n, λ S, ∀ e : (edge d), (e.lub = n.succ) → (e.monochromatic (f |c S) ∨ e.polychromatic (f |c S))

lemma edge_stable {d : ℕ} (f : colouring (d+1) α):
∀ n : ℕ, ∀ S T : subseq, ∀ e : (edge d), (e.lub = n.succ) → n_preserving n T → 
(e.monochromatic (f |c S) ∨ e.polychromatic (f |c S)) →
(e.monochromatic (f |c rel_embedding.trans T S) ∨ e.polychromatic (f |c rel_embedding.trans T S)):=
begin
  intros n S T e e_end_g n_pres constr_S, unfold colouring.restrict, 
  have e_le_g:= e.lub_le_iff.1  (nat.le_of_eq e_end_g), simp_rw [nat.lt_succ_iff] at e_le_g,
  have T_id: rel_embedding.trans e (rel_embedding.trans T S)=rel_embedding.trans e S,
    {ext, repeat {rw rel_embedding.trans_apply _ _}, 
    rw n_pres (e x)  (e_le_g x),
    },
  have of_lub_pres: ∀ a : ℕ, ∀ h_a : e.lub ≤ a,
  rel_embedding.trans (e.of_lub_le a h_a) (rel_embedding.trans T S) =
  rel_embedding.trans (e.of_lub_le (T a) (le_trans h_a (T.le_self a))) S,
  {
    intros a h_a, unfold edge.of_lub_le, ext, simp [T_id, fin.cases], cases eq_or_ne x (fin.last d),
    rw h, simp only [fin.last_cases_last], have:= lt_of_le_of_ne (fin.le_last x) h, 
    have xld: (x : ℕ) < d:= this, rw ←fin.cast_succ_cast_lt x xld, simp,
    rw n_pres (e (x.cast_lt xld)) (e_le_g (x.cast_lt xld)),
  }, unfold edge.monochromatic, unfold edge.polychromatic, 
  simp [of_lub_pres], cases constr_S, 
  {
    left, 
    unfold edge.monochromatic at constr_S, intros a b h_a h_b, 
    apply constr_S (T a) (T b) (le_trans h_a (T.le_self a)) (le_trans h_b (T.le_self b)),
  },
  {
    right, 
    unfold edge.polychromatic at constr_S,intros a b h_a h_b aneb, 
    apply constr_S (T a) (T b) (le_trans h_a (T.le_self a)) (le_trans h_b (T.le_self b)), 
    intro taeb, exact aneb (T.inj' taeb),
  },
end

lemma constraints_stable {d : ℕ} (f : colouring (d+1) α):
∀ n : ℕ, ∀ S T : subseq, (constraints f) n S → n_preserving n T → (constraints f) n (rel_embedding.trans T S):=
begin
  intros n S T constr_S n_pres e e_end_g, unfold colouring.restrict, have e_le_g :=e.le_of_lub_eq e_end_g,
  have T_id: rel_embedding.trans e (rel_embedding.trans T S)=rel_embedding.trans e S,
    {ext, repeat {rw rel_embedding.trans_apply _ _}, 
    rw n_pres (e x) (nat.le_of_lt_succ (e_le_g x)),
    },
  unfold edge.monochromatic, unfold edge.polychromatic, dsimp, 
  have of_lub_pres: ∀ a : ℕ, ∀ h_a : e.lub ≤ a,
  rel_embedding.trans (e.of_lub_le a h_a) (rel_embedding.trans T S) =
  rel_embedding.trans (e.of_lub_le (T a) (le_trans h_a (T.le_self a))) S,
  {
    intros a h_a, unfold edge.of_lub_le, ext, simp [T_id, fin.cases], cases eq_or_ne x (fin.last d),
    rw h, simp only [fin.last_cases_last], have:= lt_of_le_of_ne (fin.le_last x) h, 
    have xld: (x : ℕ) < d:= this, rw ←fin.cast_succ_cast_lt x xld, simp,
    rw n_pres (e (x.cast_lt xld)) (nat.le_of_lt_succ (e_le_g (x.cast_lt xld))),
  },
  simp [of_lub_pres], cases constr_S e e_end_g, 
  {
    left, 
    unfold edge.monochromatic at h, unfold colouring.restrict at h,intros a b h_a h_b, 
    apply h (T a) (T b) (le_trans h_a (T.le_self a)) (le_trans h_b (T.le_self b)),
  },
  {
    right, 
    unfold edge.polychromatic at h, unfold colouring.restrict at h,intros a b h_a h_b aneb, 
    apply h (T a) (T b) (le_trans h_a (T.le_self a)) (le_trans h_b (T.le_self b)), 
    intro taeb, exact aneb (T.inj' taeb),
  },
end

def edge_decompose (d : ℕ) (n : ℕ) : 
{e : edge d.succ // e.lub ≤ n} → {e : edge d // e.lub ≤ n} × (fin n):=
λ e, ⟨⟨
    ({to_fun:= λ x, e.1 x,
      inj':= begin
        intros a b, simp [e.val.inj'],
      end,
      map_rel_iff':=begin
      simp [e.val.map_rel_iff'],
      end,
  } : edge d)
  , begin
    rw edge.lub_le_iff _, intro i, dsimp, apply e.1.lub_le_iff.1 e.2 i,
  end⟩, ⟨e.1 (fin.last d), e.1.lub_le_iff.1 e.2 _⟩⟩

lemma erased_or_mem_erase {β : Type} {s : finset β} {e x : β} 
(e_mem : e ∈ s) (x_mem : x ∈ s): x = e ∨ x ∈ s.erase e:=
begin
  by_cases x=e, left, exact h, right, apply finset.mem_erase.2 ⟨h, x_mem⟩,
end

instance edgefin {d : ℕ} {n : ℕ}: finite {e : edge d // e.lub ≤ n}:=
begin
  induction d with d hd,
  {
    by_contradiction, rw not_finite_iff_infinite at h, cases @infinite.exists_subset_card_eq _ h 2 with s h_s, rcases finset.card_eq_two.1 h_s with ⟨a, b, ⟨ab_1, ab_2⟩⟩,
    apply ab_1, ext, apply fin_zero_elim i,
  },
  have decompose_inj: function.injective (edge_decompose d n), intros a b abeq, unfold edge_decompose at abeq,
  rw prod.ext_iff at abeq, dsimp at abeq, cases abeq with e_eq l_eq, rw subtype.ext_iff at e_eq,
  rw rel_embedding.ext_iff at e_eq, ext, rw fin.ext_iff at l_eq, 
  revert i, refine fin.last_cases _ _, apply l_eq, intro i, have:= e_eq i, dsimp at this,
  rw ←fin.coe_eq_cast_succ, exact this, 
  haveI: finite ({e : edge d // e.lub ≤ n} × (fin n)):= @finite.prod.finite _ _ hd _,
  apply finite.of_injective (edge_decompose d n) decompose_inj,
end

instance edgefin2 {d : ℕ} (n : ℕ): finite {e : edge d // e.lub = n}:=
begin
  set f: {e : edge d // e.lub = n} → {e : edge d // e.lub ≤ n}:=λ e, ⟨e.1, le_of_eq e.2⟩ with f_def,
  apply finite.of_injective f _, intros a b abeq, rw f_def at abeq, 
  dsimp at abeq, rw subtype.ext_iff at abeq, rw subtype.ext_iff, apply abeq,
end

instance edgefin3 {d : ℕ} {n : ℕ}: fintype {e : edge d // e.lub = n}:=fintype.of_finite {e : edge d // e.lub = n}

instance edgefin4 {d : ℕ} {n : ℕ}: fintype {e : edge d // e.lub ≤ n}:=fintype.of_finite {e : edge d // e.lub ≤ n}


lemma constraints_reachable {α : Type} {d : ℕ} (f : colouring (d+1) α):
∀ (n : ℕ) (S : subseq), ∃ (T : subseq), 
(n_preserving n T) ∧ (constraints f) n (rel_embedding.trans T S):=
begin
  intros n S, set edges:= {e : edge d // e.lub=n.succ},
  suffices: ∀ (edge_count : ℕ) (edge_set : finset edges),  edge_set.card = edge_count → 
  ∃ (T : subseq), (n_preserving n T) ∧ 
  ∀ (e : edges), e ∈ edge_set →
  e.1.monochromatic (f |c rel_embedding.trans T S) ∨ e.1.polychromatic (f |c rel_embedding.trans T S),
  {
    cases this (fintype.card edges) finset.univ rfl with T h_T,
    use T, refine ⟨h_T.1, _⟩, intros e h_e, exact h_T.2 ⟨e, h_e⟩ (finset.mem_univ _),
  },
  intro edge_count, induction edge_count with edge_count h_edge_count, intros edge_set h_edge_count,
  use (@rel_embedding.refl ℕ (≤)), split, 
  {
    intros i ilen, refl,
  },
  {
    intros e h_e, rw finset.card_eq_zero at h_edge_count, 
    exfalso, rw h_edge_count at h_e, exact finset.not_mem_empty e h_e,
  },
  {
    intros edge_set edge_card, have card_pos: edge_set.card > 0, rw edge_card, 
    exact nat.succ_pos _, cases (finset.card_pos.1 card_pos) with mem h_mem,
    have erase_card: (edge_set.erase mem).card=edge_count, rw ←finset.card_erase_add_one h_mem at edge_card,
    exact nat.succ.inj edge_card, cases h_edge_count (edge_set.erase mem) erase_card with T h_T,
    have reachable: ∃ T_mem : subseq, n_preserving n T_mem ∧ 
    (mem.1.monochromatic (f |c rel_embedding.trans T_mem (rel_embedding.trans T S)) ∨ mem.1.polychromatic (f |c rel_embedding.trans T_mem (rel_embedding.trans T S))),
    {
      cases seq_mono_poly_preserving n mem.1 mem.2 f (rel_embedding.trans T S) with T_mem h_T_mem, use T_mem,
      exact h_T_mem,
    },
    rcases reachable with ⟨T_mem, T_mem_pres, T_mem_constr⟩, set T_fin: subseq:=rel_embedding.trans T_mem T, use T_fin,
    refine ⟨n_preserving_trans h_T.1 T_mem_pres, _⟩, intros e e_mem, cases erased_or_mem_erase h_mem e_mem with m_e_eq e_erase,
    rw m_e_eq, exact T_mem_constr, have mono_poly:=h_T.2 e _, swap, rw finset.mem_erase, 
    rw finset.mem_erase at e_erase, exact e_erase,
    apply edge_stable f n (rel_embedding.trans T S) T_mem e.1 e.2 T_mem_pres mono_poly,
  },
  end

theorem all_heads_mono_poly {α : Type} {d : ℕ} (f : colouring (d+1) α) (S : subseq):
∃ T : subseq, ∀ e : edge d, 
e.monochromatic (f |c rel_embedding.trans T S) ∨ 
e.polychromatic (f |c rel_embedding.trans T S):=
begin
  cases nat.eq_zero_or_pos d, 
  { revert f, rw h, suffices: ∀ (f : colouring 1 α), ∃ (T : subseq), ∀ (e : edge 0), 
    edge.monochromatic e (f |c rel_embedding.trans T S) ∨ edge.polychromatic e (f |c rel_embedding.trans T S),
    intro f, exact this f, intro f, cases seq_mono_poly (f |c S) with T h_t, use T, intro e,
    cases h_t with mono poly, left, intros a b h_a h_b, exact mono (e.of_lub_le a h_a) (e.of_lub_le b h_b),
    right, intros a b h_a h_b aneb, have:= poly (e.of_lub_le a h_a) (e.of_lub_le b h_b) _, exact this,
    intro h_f, apply aneb, rw rel_embedding.ext_iff at h_f, have:= h_f (fin.last 0), 
    repeat {rw edge.of_lub_le_last_eq _ _ _ at this}, exact this,
  },
  cases constraints_apply (constraints f) (constraints_stable f) (constraints_reachable f) S with T ht,
  use T, intro e, cases nat.eq_zero_or_eq_succ_pred e.lub, 
  {
    have:= e.lub_le_iff.1 (le_of_eq h_1) ⟨0, h⟩, apply absurd this (nat.not_lt_zero _),
  },
  exact ht e.lub.pred e h_1, 
end

lemma fintype_canonical_monochromatic {α : Type} [fintype α] {d : ℕ} (f : colouring d α)
(I : index_set d) (S : subseq) (h_c: f |c S ≃c I.canonical):
∃ c : α, ∀ e : edge d, (f |c S) e = c:=
begin
  by_cases I=∅, use (f |c S) default, intro e, unfold colouring.iso at h_c, apply (h_c e default).2, ext, 
  exact is_empty.elim' (set.is_empty_coe_sort.2 h) x, revert d, intro d, cases nat.eq_zero_or_eq_succ_pred d, rw h, 
  intros f I h_c I_none, use (f |c S) default, rw unique.forall_iff, rw unique.eq_default (edge.inhabited.default),
  rw h, intros f I h_c I_none, have: I.nonempty, apply set.nonempty_iff_ne_empty.2, apply I_none, 
  cases set.nonempty_def.1 this with i h_i, exfalso, rw iso_canonical_iff at h_c,
  have: ∀ (y : set.range (f |c S)),  ∃ x : {n : ℕ // (i : ℕ) ≤ n}, ∀ e, (f |c S) e = y.1 → e i = x,
  {
    intro y, cases set.mem_range.1 y.2 with e₀ h_e₀, use (e₀ i), exact edge_le_self, intros e f_e,
    rw ←h_e₀ at f_e, have:= (h_c e e₀).1 f_e, rw set_coe.forall at this, exact this i h_i,
  }, haveI: nonempty {n // (i : ℕ) ≤ n}, refine ⟨⟨(i : ℕ), le_refl _⟩⟩, 
   choose! fn h_fn using this, have fn_surj: fn.surjective,
  {
    intro b, use (f |c S) (edge_force b), exact set.mem_range_self (edge_force b),
    have:= h_fn ⟨(f |c S) (edge_force b), set.mem_range_self (edge_force b)⟩ (edge_force b) rfl, 
    rw edge_force_at at this, symmetry, ext, exact this, 
  },
  haveI: infinite {n // (i : ℕ) ≤ n},
  {
    set add: ℕ → {n // (i : ℕ) ≤ n}:=λ x, ⟨x+i, le_add_self⟩, apply infinite.of_injective add, 
    intros a b, simp, 
  },
  have:=infinite.of_surjective fn fn_surj, apply not_finite_iff_infinite.2 this, rw set.finite_coe_iff,
  apply set.finite.subset _ (set.subset_univ _), refine ⟨set.fintype_univ⟩,
end

lemma mono_colouring_canonical {d : ℕ} {α : Type} {f : colouring (d+1) α} (fn : colouring d α)
(h_fn : ∀ (e : edge d) (a : ℕ) (h_a : e.lub ≤ a), f (e.of_lub_le a h_a) = fn e) (S : subseq)
(I : index_set d) (h_S_I: fn |c S ≃c I.canonical):
f |c S ≃c I.cast.canonical:=
begin
  rw iso_canonical_iff at *, intros e₁ e₂,
  sorry,
end

lemma ramsey {d : ℕ} {α : Type} (f : colouring d α) :
  /- ∃ (S : subseq) (I : index_set d), f |c S ≃c I.canonical -/
  ramsey.statement f :=
begin
  change ∃ (S : subseq) (I : index_set d), f |c S ≃c I.canonical, revert α, 
  induction d with d hd, 
  { --zero case
    intros α f, use subseq.refl, use ∅, intros e₁ e₂, 
    have edge_eq: e₁=e₂, ext, apply fin_zero_elim i, simp [edge_eq],
  },
  intros α f, cases all_heads_mono_poly f subseq.refl with T h_T, rw subseq.trans_refl at h_T, 
  set colour_colouring: colouring d Prop:=λ e, e.monochromatic (f |c T) with c_def,
  rcases hd colour_colouring with ⟨S, I, h_S_I⟩,
  cases fintype_canonical_monochromatic colour_colouring I S h_S_I with colour h_colour,
  have all_mono_or_all_poly: (∀ e : edge d, e.monochromatic ((f |c T) |c S)) ∨ 
  ∀ e : edge d, e.polychromatic ((f |c T) |c S),
  {
    by_cases colour, left, simp [h] at h_colour, rw c_def at h_colour, intro e, 
    exact e.monochromatic_restrict (f |c T) S (h_colour e),
    right, simp [h] at h_colour, rw c_def at h_colour, intro e, 
    have r_poly:= or.resolve_left (h_T (rel_embedding.trans e S)) (e.monochromatic_restrict' (f |c T) S (h_colour)),
    exact e.polychromatic_stable_apply (f |c T) S r_poly,
  },
  cases all_mono_or_all_poly with mono poly,
  {
    simp_rw [edge.monochromatic_equiv] at mono, haveI: nonempty α, 
    {
      refine ⟨f default⟩, 
    },
    choose! fn h_fn using mono, rcases hd fn with ⟨S_1, I_1, h_S_I_1⟩, 
    use ((T |s S) |s S_1), use I_1.cast, 
    rw colouring.restrict_restrict f T S at h_fn, rw ← colouring.restrict_restrict f _ _,
    exact mono_colouring_canonical fn h_fn S_1 I_1 h_S_I_1, 
  },
  {
    sorry,
  },
end


lemma canonical_subseq_iso_self
  {d : ℕ} (I : index_set d) (S : subseq) :
  /- I.canonical |c S ≃c I.canonical -/
  canonical_subseq_iso_self.statement I S :=
begin
  change I.canonical |c S ≃c I.canonical,
  intros e₁ e₂,
  simp_rw [rel_embedding.ext_iff],
  change (∀ (i : I), S (e₁ i) = S (e₂ i)) ↔ (∀ (i : I), e₁ i = e₂ i),
  simp_rw [order_embedding.eq_iff_eq S],
end


lemma canonical_inj
  {d : ℕ} (I J : index_set d) :
  /- I.canonical ≃c J.canonical → I = J -/
  canonical_inj.statement I J :=
begin
  
  set f₁ : fin d → ℕ := λ i, 2 * i with hf₁_def, 
  have hf₁ : strict_mono f₁ := λ x x' h, by {simpa [hf₁_def]},
  set e₁ := order_embedding.of_strict_mono f₁ hf₁ with he₁, 

  set f₂ : fin d → fin d → ℕ := λ x i, if i = x then 2*i + 1 else 2*i with hf₂_def, 
  have hf₂ : ∀ x, strict_mono (f₂ x),
  { rintros ⟨x,hx⟩ ⟨i,hi⟩ ⟨i',hi'⟩ (hii' : i < i'), 
    simp only [hf₂_def], 
    split_ifs with h h' h',
    all_goals {linarith}}, 

  intro h, 
  ext,
  refine ⟨λ hx, by_contra (λ hx', _),λ hx, by_contra (λ hx', _ )⟩, 
  all_goals 
  { set e₂ := order_embedding.of_strict_mono _ (hf₂ x) with he₂, 
    specialize h e₁ e₂, 
    simp only [index_set.canonical, rel_embedding.ext_iff, index_set_apply, 
      order_embedding.coe_of_strict_mono, set_coe.forall, subtype.coe_mk, hf₁_def, hf₂_def] at h, },
  { simpa using h.mpr (λ i hij, by {rw if_neg, rintro rfl, exact hx' hij, }) _ hx},
  simpa using h.mp (λ i hij, by {rw if_neg, rintro rfl, exact hx' hij, }) _ hx,
end



/-!
### Junk
-/

example (d : ℕ) : fin (d+1) := fin.last d
example (d : ℕ) : fin d ↪o fin (d+1) := fin.cast_succ
example (α : Type) : Type :=
quot (λ (f g : ℕ → α), ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → f m = g m)
example (d : ℕ) : d ∈ ({d, 3} : finset ℕ):=
begin
  simp,
end