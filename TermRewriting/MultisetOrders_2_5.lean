import TermRewriting.LexicographicOrders_2_4

variable (R S : α → α → Prop) 

def MultisetOver α := α → Nat

def MultisetOver.Mem (x : α) (m : MultisetOver α) := m x > 0

def MultisetOver.Finite (m : MultisetOver α) := Set.Finite { x | Mem x m }

def MultisetOver.Nonempty (m : MultisetOver α) := Set.Nonempty { x | Mem x m }

def FinMultisetOver α := { m : MultisetOver α // MultisetOver.Finite m }

@[simp]
def MultisetOver.Subset (m₁ m₂ : MultisetOver α) := ∀x, m₁ x ≤ m₂ x

@[simp]
def MultisetOver.Union (m₁ m₂ : MultisetOver α) := λx ↦ m₁ x + m₂ x

@[simp]
def MultisetOver.Difference (m₁ m₂ : MultisetOver α) := λx ↦ m₁ x - m₂ x
def MultisetOver.Empty := λ_ : α ↦ 0

def MultisetOver.ordering (m₁ m₂ : MultisetOver α) := 
  ∃X Y : FinMultisetOver α,
    Nonempty X.1 ∧
    MultisetOver.Subset X.1 m₁ ∧
    m₂ = MultisetOver.Union (MultisetOver.Difference m₁ X.1) Y.1 ∧
    ∀y, MultisetOver.Mem y Y.1 → ∃x, MultisetOver.Mem x X.1 ∧ R x y

theorem MultisetOver.ofStrictOrder : isStrictOrder R → isStrictOrder (ordering R) := by
  intro strict; constructor
  case irref =>
    rintro x ⟨X,Y,inhab,sub,eq,cond⟩
    have : X = Y := by
      apply Subtype.eq
      funext el
      have : x el + X.val el = X.val el + (x el - X.val el) +  Y.val el  := by
        conv => lhs; rw [eq]
        simp_arith
      rw [Nat.add_sub_cancel' (sub el)] at this 
      simp_arith at this
      assumption
    rw [this] at cond
    rw [this] at inhab
    have : ∀x : { z | Mem z Y.val }, ∃y : { z | Mem z Y.val}, R y x := by 
      intro x; have ⟨y, yprop⟩ := cond x.val x.prop; exists ⟨y, yprop.1⟩; simp; exact yprop.2
    unfold Nonempty at inhab; unfold Set.Nonempty at inhab
    have ⟨a,prop⟩ := inhab
    have ⟨chain,cprop⟩ := descending.fromAE (λ x y : { z | Mem z Y.val} ↦ R y x) ⟨a,prop⟩ this
    have strict_conv := (StrictOrder.of_converse R).mpr strict
    sorry
  all_goals sorry



    --apply Set.Finite.not_infinite X.prop



