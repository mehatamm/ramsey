import finramsey


noncomputable theory



instance edges_in_finset_fin (Y : finset ℕ) : fintype {e : edge | ∀ x : fin 2 , e x ∈ Y}:=
begin
  apply fintype.of_equiv (fin 2 ↪o Y), apply order_embedding.iso_restricted.symm, 
end

def edges_in_finset (Y : finset ℕ):=
{e : edge | ∀ x : fin 2 , e x ∈ Y}.to_finset

def homogenous (f : edge → ℕ) (Y : finset ℕ):=
∃ c : ℕ, ∀ e ∈ edges_in_finset Y, f e = c 

def left_monogamous (f : edge → ℕ) (Y: finset ℕ):=
∀ e1 e2 ∈ edges_in_finset Y, f e1 = f e2 ↔ e1 0 = e2 0  

def right_monogamous (f : edge → ℕ) (Y: finset ℕ):=
∀ e1 e2 ∈ edges_in_finset Y, f e1 = f e2 ↔ e1 1 = e2 1 

def rainbow (f : edge → ℕ) (Y : finset ℕ):=
∀ e1 e2 ∈ edges_in_finset Y, f e1 = f e2 ↔ e1 = e2

theorem can_ramsey:
∀ k : ℕ, ∃ n₀ : ℕ, ∀ coll : finset ℕ, n₀ ≤ coll.card → ∃ x ⊆ coll, x.card=k ∧ ∀ f : edge → ℕ, (rainbow f x) ∨ (homogenous f x) ∨ (left_monogamous f x) ∨ (right_monogamous f x):=
begin
  
end