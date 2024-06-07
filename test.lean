
example (a b : Nat) (h1 : a = 1) (h2 : b = 1): (a + b = 2) := by
  rewrite [h1]
  rewrite [h2]
  rfl
-- Eat your heart out Bertrand Russell
def f (x : Nat) :=
  x + 2

#check f


example (a b c : Nat) (h1 : a ≤  b): ((a + c) - c ≤  b) := by
  simp
  exact h1

  def envyfree (a b : Set Nat) :=
    
