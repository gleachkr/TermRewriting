import TermRewriting.WellFoundedInduction_2_2

variable (R : α → α → Prop) 
variable (S : β → β → Prop) 

def monotoneIn (R : α → α → Prop) (S : β → β → Prop) (f : α → β) := ∀{x y}, R x y → S (f x) (f y)

theorem monotoneIn.termination : ∀{f}, monotoneIn R S f → terminating S → terminating R := by
  intro f mono term ⟨chain, desc⟩
  apply term
  exists (f ∘ chain)
  intro n
  apply mono
  apply desc

theorem Nat.lt_terminating : terminating (λ x y => ¬Nat.le x y) := by
  have : ∀n k, k ≤ n → ¬∃c, c 0 = k ∧ isDescendingChain (λ x y => ¬Nat.le x y) c := by
    intro n; induction n
    case zero => intro k le ⟨chain, eq, desc⟩; have := desc 0; simp_all
    case succ n ih => 
      intro k lt ⟨chain, eq, desc⟩
      apply ih (chain 1)
      · have := desc 0; simp_all; omega
      · exists λn ↦ chain (n + 1); constructor
        · rfl
        · simp_all; apply chain_shift (λ x y => y < x) chain desc
  intro ⟨chain, desc⟩
  apply this (chain 0) (chain 0) <;> try simp
  exists chain; simp_all

theorem finitely_branching.terminating_iff_monotoneInN : finitely_branching R →
  (terminating R ↔ ∃f,monotoneIn R (λ x y => ¬Nat.le x y) f) := by
  intro fin_b; constructor
  case mpr => intro ⟨f,mono⟩; apply monotoneIn.termination R (λ x y => ¬Nat.le x y) mono; apply Nat.lt_terminating
  case mp => sorry



