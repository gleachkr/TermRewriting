import TermRewriting.LexicographicOrders_2_4

variable (R S : α → α → Prop) 

def MultisetOver α := α → Nat

def MultisetOver.Finite (m : MultisetOver α) := Set.Finite { x | m x > 0 }

def FinMultisetOver α := { m : MultisetOver α // MultisetOver.Finite m }

def MultisetOver.Mem (x : α) (m : MultisetOver α) := m x > 0
def MultisetOver.Subset (m₁ m₂ : MultisetOver α) := ∀x, m₁ x ≤ m₂ x
def MultisetOver.Union (m₁ m₂ : MultisetOver α) := λx ↦ m₁ x + m₂ x
def MultisetOver.Difference (m₁ m₂ : MultisetOver α) := λx ↦ m₁ x - m₂ x
def MultisetOver.Empty := λ_ : α ↦ 0

def MultisetOver.ordering (m₁ m₂ : MultisetOver α) := 
  ∃X Y : FinMultisetOver α,
    (X.1 ≠ MultisetOver.Empty) ∧
    (MultisetOver.Subset X.1 m₁) ∧
    (m₂ = MultisetOver.Union (MultisetOver.Difference m₁ X.1) Y.1) ∧
    ∀y, MultisetOver.Mem y Y.1 → ∃x, MultisetOver.Mem x X.1 ∧ R x y
