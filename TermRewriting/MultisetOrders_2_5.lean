import TermRewriting.LexicographicOrders_2_4

variable (R S : α → α → Prop) 

def MultisetOver α := α → Nat

@[simp]
def MultisetOver.Mem (x : α) (m : MultisetOver α) := m x > 0

@[simp]
def MultisetOver.Finite (m : MultisetOver α) := Set.Finite { x | Mem x m }

@[simp]
def MultisetOver.Nonempty (m : MultisetOver α) := Set.Nonempty { x | Mem x m }

def FinMultisetOver α := { m : MultisetOver α // MultisetOver.Finite m }

@[simp]
def MultisetOver.Subset (m₁ m₂ : MultisetOver α) := ∀x, m₁ x ≤ m₂ x

@[simp]
def MultisetOver.Union (m₁ m₂ : MultisetOver α) := λx ↦ m₁ x + m₂ x

theorem MultisetOver.Union_mem : {x | Mem x (Union m₁ m₂)} = { x | Mem x m₁ } ∪ { x | Mem x m₂ } := by
  apply Set.ext; intro x; constructor
  case mp => 
    intro hyp
    have := Nat.not_le_of_gt hyp
    apply Classical.byContradiction
    intro hyp₂
    apply this
    simp_all
  case mpr => 
    rintro (hyp | hyp)
    case inl hyp => apply Nat.add_pos_left; assumption
    case inr hyp => apply Nat.add_pos_right; assumption

@[simp]
def FinMultisetOver.Union (m₁ m₂ : FinMultisetOver α) : FinMultisetOver α := by
  constructor
  case val => exact MultisetOver.Union m₁.val m₂.val
  case property => 
    simp
    apply Set.finite_union.mpr
    exact ⟨m₁.property, m₂.property⟩

@[simp]
def MultisetOver.Difference (m₁ m₂ : MultisetOver α) := λx ↦ m₁ x - m₂ x

theorem MultisetOver.Difference_mem (m₁ m₂ : MultisetOver α) : 
    {x | Mem x (Difference m₁ m₂)} ⊆ {x | Mem x m₁}:= 
  by rintro x hyp; simp_all; omega

@[simp]
def FinMultisetOver.Difference (m₁ m₂ : FinMultisetOver α) : FinMultisetOver α := by
  constructor
  case val => exact MultisetOver.Difference m₁.val m₂.val
  case property =>
    apply Set.Finite.subset _ (MultisetOver.Difference_mem m₁.val m₂.val)
    exact m₁.property

def MultisetOver.Empty := λ_ : α ↦ 0

def MultisetOver.ordering (m₁ m₂ : MultisetOver α) := 
  ∃X Y : FinMultisetOver α,
    Nonempty X.1 ∧
    MultisetOver.Subset X.1 m₁ ∧
    m₂ = MultisetOver.Union (MultisetOver.Difference m₁ X.1) Y.1 ∧
    ∀y, MultisetOver.Mem y Y.1 → ∃x, MultisetOver.Mem x X.1 ∧ R x y

/- Lemma 2.5.4 -/
theorem MultisetOver.ofStrictOrder : isStrictOrder R → isStrictOrder (ordering R) := by
  intro strict; apply StrictOrder.of_minimal_conditions'
  case irref =>
    rintro x ⟨X,Y,inhab,sub,eq,cond⟩
    have : X = Y := by
      apply Subtype.eq
      funext el
      have : x el + X.val el = X.val el + (x el - X.val el) + Y.val el := by
        conv => lhs; rw [eq]
        simp_arith
      rw [Nat.add_sub_cancel' (sub el)] at this 
      simp_arith at this
      assumption
    rw [this] at cond
    rw [this] at inhab
    have : ∀x : { z | Mem z Y.val }, ∃y : { z | Mem z Y.val}, R y x := by 
      intro x; have ⟨y, yprop⟩ := cond x.val x.prop; exists ⟨y, yprop.1⟩; simp; exact yprop.2
    have ⟨a,prop⟩ := inhab
    let restrictedOrder := λ x y : { z | Mem z Y.val } ↦ R y x
    have ⟨chain,cprop⟩ := descending.fromAE restrictedOrder ⟨a,prop⟩ this
    have rs_acyc : acyclic restrictedOrder := by 
      apply acyclic.of_strictOrder
      apply StrictOrder.preimage (λx y => R y x) Subtype.val
      exact (StrictOrder.of_converse R).mpr strict
    apply not_infinite_iff_finite.mpr Y.prop
    exact acyclic.codomain_infinite restrictedOrder rs_acyc cprop
  case trans =>
    rintro x y z ⟨X,Y,inhab₁,sub₁,eq₁,cond₁⟩ ⟨Z,W,inhab₂,sub₂,eq₂,cond₂⟩
    exists FinMultisetOver.Union X (FinMultisetOver.Difference Z Y)
    exists FinMultisetOver.Union W (FinMultisetOver.Difference Y Z)
    constructor
    · simp; have ⟨i₁, prop⟩ := inhab₁; exact ⟨i₁,Or.inl prop⟩
    · constructor
      simp_all
      have                                                                                                  
        h : MultisetOver.Subset (MultisetOver.Difference Z.val Y.val) (MultisetOver.Difference x X.val) :=
      by intro elt; simp; exact (sub₂ elt)
      · intro elt; apply Nat.add_le_of_le_sub'
        · exact sub₁ elt
        · simp at h; simp; exact h elt
      constructor
      · rw [eq₂, eq₁]; funext; simp; omega
      · intro k hyp; simp at hyp; cases hyp
        case inr hyp => 
          have : Mem k Y.val := by simp; omega
          have ⟨witness,⟨prop₁,prop₂⟩⟩ := cond₁ k this
          exists witness
          refine ⟨?_, prop₂⟩
          simp
          exact Or.inl prop₁
        case inl hyp =>
          have ⟨witness,⟨prop₁,prop₂⟩⟩ := cond₂ k hyp
          cases Classical.em (Mem witness Y.val)
          case inl hyp₂ => 
            have ⟨witness₂,⟨prop₃,prop₄⟩⟩ := cond₁ witness hyp₂
            exists witness₂
            constructor
            · simp; apply Or.inl; exact prop₃
            · exact strict.trans prop₄ prop₂
          case inr hyp₂ => 
            exists witness
            refine ⟨?_, prop₂⟩
            simp; apply Or.inr
            simp at hyp₂
            rw [hyp₂]
            exact prop₁
