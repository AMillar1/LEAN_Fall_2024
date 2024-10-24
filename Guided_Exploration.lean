-- Practice simple logic proofs.

-- Prove modus ponens

example (P Q : Prop) (h1 : P → Q) (h2 : P) : Q :=
by
  apply h1
  exact h2

-- Prove Commutitivity of Conjunction

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
by
  cases h with
  | intro p q =>  -- Break h into P and Q, assigning p : P and q : Q
    exact ⟨q, p⟩ -- Conclude Q ∧ P by constructing the pair ⟨q, p⟩

example (P Q Q : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R :=
by
  cases h with
  | inl p => exact hp p
  | inr q => exact hq q
