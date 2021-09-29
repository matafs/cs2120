/-
We
-/

def ev (n : ℕ) : Prop := n%2=0

example : exists (n : ℕ), ev n :=
begin
  apply exists.intro _ _,
  exact 6,
  apply eq.refl,
end

example : exists n, ev n := _
def pythagorean_triple (a b c : ℕ ) : Prop := a*a + b*b = c*c
example : ∃ (a b c : ℕ ), pythagorean_triple 3 4 5 := 
begin
  exists.intro 3 _,
  
  unfold pythagorean_triple,
  apply eq.refl,
end


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end