import TermRewriting.ProvingTermination_2_3

variable (R : α → α → Prop) 
variable (S : β → β → Prop) 

def LexProduct (x y : α × β) := R x.1 y.1 ∨ x.1 = y.1 ∧ S x.2 y.2

theorem LexProduct.ofIrreflexive : isIrreflexive R → isIrreflexive S → 
    isIrreflexive (LexProduct R S) := by
      intro irrefR irrefS x h; cases h
      · apply irrefR ; assumption
      · apply irrefS; aesop

theorem LexProduct.ofAsymmetric : isAsymmetric R → isAsymmetric S → 
    isAsymmetric (LexProduct R S) := by
    intro asymmR asymmS x y h contr; cases h <;> cases contr
    · apply asymmR <;> assumption
    · apply isAsymmetric.isIrreflexive R asymmR <;> aesop
    · apply isAsymmetric.isIrreflexive R asymmR <;> aesop
    · apply asymmS <;> aesop

theorem LexProduct.ofTransitive : isTransitive R → isTransitive S → 
    isTransitive (LexProduct R S) := by
    intro transR transS x y z step₁ step₂; cases step₁ <;> cases step₂
    · apply Or.inl; apply transR <;> aesop
    · apply Or.inl; aesop
    · apply Or.inl; aesop
    · apply Or.inr; constructor
      · aesop
      · apply transS (y:= y.2) <;> aesop

/-- Lemma 2.4.1 -/
theorem LexProduct.ofStrictOrder : isStrictOrder R → isStrictOrder S → 
    isStrictOrder (LexProduct R S) := by
  intro strictR strictS; constructor
  · exact LexProduct.ofIrreflexive R S strictR.irref strictS.irref
  · exact LexProduct.ofAsymmetric R S strictR.asymm strictS.asymm
  · exact LexProduct.ofTransitive R S strictR.trans strictS.trans

theorem LexProduct.ofConnected : isConnected R → isConnected S → 
    isConnected (LexProduct R S) := by
  intro cnctdR cnctdS x y neq
  cases Classical.em (x.1 = y.1)
  case inl lor =>
    have : x.2 ≠ y.2 := by
      intro hyp; apply neq; aesop
    cases cnctdS x.2 y.2 this
    case inl => apply Or.inl ∘ Or.inr; aesop
    case inr => apply Or.inr ∘ Or.inr; aesop
  case inr ror =>
    cases cnctdR x.1 y.1 ror
    case inl => apply Or.inl ∘ Or.inl; assumption
    case inr => apply Or.inr ∘ Or.inl; assumption

/-- Exercise 2.13 -/
theorem LexProduct.ofStrictLinearOrder : isStrictLinearOrder R → isStrictLinearOrder S →
    isStrictLinearOrder (LexProduct R S) := by
  intro strictLinR strictLinS
  constructor
  · exact LexProduct.ofIrreflexive R S strictLinR.irref strictLinS.irref
  · exact LexProduct.ofAsymmetric R S strictLinR.asymm strictLinS.asymm
  · exact LexProduct.ofTransitive R S strictLinR.trans strictLinS.trans
  · exact LexProduct.ofConnected R S strictLinR.cnctd strictLinS.cnctd

section open Classical

theorem Nat.minimize : ∀P: Nat → Prop, (∃n, P n) → (∃n, P n ∧ ∀m < n, ¬P m) := by
  intro P hyp
  apply byContradiction
  intro contra
  have : ∀n, ∀m ≤ n, ¬ P m := by
    intro n; induction n
    case zero => 
      intro n _ _; apply contra; exists 0; simp_all
    case succ n ih => 
      intro succ le contra₂
      apply contra
      exists succ
      simp_all
      intro m lt
      apply ih
      omega
  have ⟨n,not⟩ := hyp
  apply this n n <;> aesop

/-- Theorem 2.4.2 -/
theorem LexProduct.ofTerminating : terminating R → terminating S →
    terminating (LexProduct R S) := by
  intro strictR strictS ⟨chain, desc⟩
  let chainL n := (chain n).1

  -- It suffices to show that there's a point where the first part of the tuple
  -- stabilizes, since then the second part must for a descending chain
  suffices ∃k, ∀i ≥ k, chainL i = chainL (i + 1) by
    have ⟨i,iprop⟩ := this
    apply strictS
    exists (λn ↦ (chain (n + i)).2)
    intro n; cases desc (n + i)
    case inl orl =>
      exfalso
      have : (chain (n + i)).1 = (chain (n + i + 1)).1 := iprop (n + i) (by omega)
      rw [this] at orl
      apply terminating.irreflexive R strictR <;> assumption
    case inr orr => 
      simp
      rw [(by simp_arith : n + 1 + i = n + i + 1)]
      exact orr.right

  have chainLProp : ∀i, chainL i ≠ chainL (i + 1) → R (chainL i) (chainL (i + 1)) := by
    intro i; cases desc i <;> intro hyp
    case inl orl => assumption
    case inr orr => have := orr.left; contradiction

  apply byContradiction
  intro nonExist
  have next₁ : ∀ n, ∃ i ≥ n, chainL i ≠ chainL (i + 1) := by aesop
  have next₂ : ∀ n, ∃ i > n, R (chainL n) (chainL i) := by
    intro n
    let minProp := λx ↦ x ≥ n ∧ chainL x ≠ chainL (x + 1)
    have ⟨i,min⟩ := Nat.minimize minProp (next₁ n)
    exists i + 1; constructor
    case left => omega
    case right =>
      have : ∀m ≤ i, m ≥ n → chainL n = chainL m := by
        intro m; induction m
        case zero => 
          cases min.left.left <;> intro _ _ <;> rw [(by aesop : n = 0)]
        case succ m ih => 
          intro le₁ le₂
          cases le₁ <;> cases le₂ <;> try rfl
          case refl.step le =>
            rw [ih (by omega) le]
            have := not_and.mp (min.right m (by omega)) le
            aesop
          case step.step k le₁ le₂ => 
            simp at le₁
            rw [ih (by omega) le₂]
            have := not_and.mp (min.right m (by omega)) le₂
            aesop
      rw [this i (by omega) (min.left.left)]
      apply chainLProp i (min.left.right)
  apply strictR
  exact descending.fromAE R chainL next₂

theorem LexProduct.ofwWFI : wWFI R → wWFI S → wWFI (LexProduct R S) := by
  intro wfiR wfiS P hereditary
  let saturated x := ∀y, P (x,y)
  suffices ∀x, saturated x by 
    intro x; apply this x.1
  apply wfiR; intro x predsSat
  apply wfiS; intro z preds
  apply hereditary; intro y step
  cases step
  case a.a.a.inl orl =>
    have := predsSat y.1 orl
    apply this y.2
  case a.a.a.inr orr => 
    have := preds y.2 orr.right
    have : (y.1, y.2) = (x,y.2) := by rw [←orr.left]
    simp at this
    rw [this]
    assumption

/-- Theorem 2.4.2, alternative proof (Exercise 2.10) -/
theorem LexProduct.ofTerminating_alt : terminating R → terminating S →
    terminating (LexProduct R S) := by
    intro termS termR
    apply WFI.terminating
    apply wWFI.WFI
    apply LexProduct.ofwWFI <;> apply terminating.wWFI <;> assumption

def nTuples (α : Type u) (n : Nat) : Type u :=
  match n with
  | 0 => PUnit
  | .succ n => α × (nTuples α n)

@[simp]
def List.toNTuple : List α → Σn, nTuples α n
  | [] => ⟨0, PUnit.unit⟩
  | h :: t => let ⟨n,tup⟩ := List.toNTuple t; ⟨n + 1, (h,tup)⟩

theorem List.toNTuple_length : ∀l : List α, (List.toNTuple l).1 = l.length := by
  intro l; induction l <;> aesop

def nOrder (n : Nat) := @nTuples α n → @nTuples α n → Prop

def LexPower (n : Nat) : @nOrder α n :=
  match n with
  | 0 => λ_ _ ↦ False
  | .succ n => LexProduct R (LexPower n)

theorem LexPower.ofTerminating : terminating R → ∀n, terminating (LexPower R n) := by
  intro term n; induction n
  case zero => intro ⟨_,desc⟩; apply desc 0
  case succ n ih => exact LexProduct.ofTerminating R (LexPower R n) term ih

inductive LexSum (T : β → Type u) (R : Πi: β, T i → T i → Prop) : (Σ i, T i) → (Σ i, T i) → Prop
  | step (i : β) (x y : T i) : R i x y → LexSum T R ⟨i,x⟩ ⟨i,y⟩

theorem LexSum.homogenousChains_aux2 
    {R : Πi: β, T i → T i → Prop} : LexSum T R x y → x.1 = y.1 := by
  intro step; cases step; simp
  
theorem LexSum.homogenousChains 
    {R : Πi: β, T i → T i → Prop} 
    (eq₁ : z = x.1) 
    (eq₂ : z = y.1) : 
    LexSum T R x y → R z (eq₁ ▸ x.2) (eq₂ ▸ y.2) := by
  intro step; cases step; aesop

theorem LexSum.ofTerminating (T : β → Type u) (R : Πi: β, T i → T i → Prop) : 
    (∀i, terminating (R i)) → terminating (LexSum T R) := by
  intro term ⟨chain,desc⟩
  suffices eq : ∀n, (chain 0).1 = (chain n).1  by
    apply term (chain 0).1
    exists λn ↦ eq n ▸ (chain n).2
    intro n
    exact LexSum.homogenousChains (eq n) (eq (n + 1)) (desc n)
  intro n; induction n
  case zero => rfl
  case succ n ih => rw [ih]; exact LexSum.homogenousChains_aux2 (desc n)

def TupleOrdering : (Σn, nTuples α n) → (Σn, nTuples α n) → Prop :=
  LexSum (nTuples α) (λn ↦ LexPower R n)

def List.lexOrdering (l₁ : List α) (l₂ : List α) := 
  l₁.length > l₂.length ∨ 
  (l₁.length = l₂.length ∧ TupleOrdering R l₁.toNTuple l₂.toNTuple)
