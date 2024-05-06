import Aesop

variable (R S : α → α → Prop) 

def contains := ∀ {x y}, R x y → S x y

infix:60 " ⊆ " => contains

abbrev monotone (F : (α → α → Prop) → (α → α → Prop)) : Prop := R ⊆ S → F R ⊆ F S

abbrev increasing (F : (α → α → Prop) → (α → α → Prop)) : Prop := R ⊆ F R

@[aesop unsafe [constructors, cases]]
inductive TransClosure (R : α → α → Prop) : α → α → Prop
| base : ∀ a b, R a b → TransClosure R a b
| step : ∀ a b c, R a b → TransClosure R b c → TransClosure R a c

def isTransitive : Prop := ∀{x y z}, R x y → R y z → R x z

theorem TransClosure.isTransitive : isTransitive (TransClosure R) := 
  by intros x y z step₁ step₂; induction step₁ <;> aesop

theorem TransClosure.monotone : monotone R S TransClosure := 
  by intro h₁ x y h₂; induction h₂ <;> aesop

theorem TransClosure.push : TransClosure R x y → R y z → TransClosure R x z :=
  by intro tcstep step; induction tcstep <;> aesop

theorem TransClosure.pop : TransClosure R x y → R x y ∨ ∃ z, TransClosure R x z ∧ R z y  :=
  by intro tcstep
     induction tcstep
     case base => aesop
     case step x y z step tcstep ih => 
      cases ih
      case inl => aesop
      case inr ih =>
        apply Or.inr; 
        have ⟨w,ih₁⟩ := ih
        exists w
        aesop

instance : Coe (R x y : Prop) (TransClosure R x y) where coe h := TransClosure.base x y h

@[aesop unsafe [constructors, cases]]
inductive ReflClosure (R  : α → α → Prop) : α → α → Prop where
| refl : ∀ a, ReflClosure R a a
| base : ∀ a b, R a b → ReflClosure R a b

def isReflexive : Prop := ∀x, R x x

theorem ReflClosure.isReflexive : isReflexive (ReflClosure R) :=
  by intros x; exact refl x

theorem ReflClosure.monotone : monotone R S ReflClosure := 
  by intro h₁ x y h₂; induction h₂ <;> aesop

@[aesop unsafe [constructors, cases]]
inductive SymClosure (R  : α → α → Prop) : α → α → Prop
| base : ∀ a b, R a b → SymClosure R a b
| inv : ∀ a b, R b a → SymClosure R a b

def isSymmetric : Prop := ∀{x y}, R x y → R y x

theorem SymClosure.isSymmetric : isSymmetric (SymClosure R) :=
  by intros x y step; induction step <;> aesop

theorem SymClosure.monotone : monotone R S SymClosure := 
  by intro step x y step₂; aesop

instance : Coe (R x y : Prop) (SymClosure R x y) where coe h := SymClosure.base x y h

@[simp]
abbrev ReflTransClosure := ReflClosure (TransClosure R)

theorem ReflTransClosure.base : increasing R ReflTransClosure := 
  by intro x y h; aesop

instance : Coe (R x y : Prop) (ReflTransClosure R x y) where coe h := ReflTransClosure.base R h

theorem ReflTransClosure.isTransitive : isTransitive (ReflTransClosure R) :=
  by intro x y z step₁ step₂; cases step₂ 
     case refl => aesop
     case base step₂ => 
       cases step₁ <;> apply ReflClosure.base
       case refl => aesop
       case base step₁ => apply TransClosure.isTransitive <;> assumption

theorem ReflTransClosure.step : ∀x y z, R x y → ReflTransClosure R y z → ReflTransClosure R x z :=
  by intro x y z step; apply ReflTransClosure.isTransitive R step

theorem ReflTransClosure.monotone : monotone R S ReflTransClosure := 
  by intro step; apply ReflClosure.monotone; apply TransClosure.monotone; assumption

theorem ReflTransClosure.fromReflClosure : ReflClosure R ⊆ ReflTransClosure R :=
  by apply ReflClosure.monotone; apply TransClosure.base

theorem ReflTransClosure.toTransRefl : ReflTransClosure R ⊆ TransClosure (ReflClosure R) := 
  by intro x y step
     induction step
     case refl => aesop
     case base z h => 
        apply TransClosure.monotone
        . apply ReflClosure.base
        . assumption

theorem ReflTransClosure.push : ∀x y z, ReflTransClosure R x y → R y z → ReflTransClosure R x z :=
  by intro x y z step₁ step₂; apply ReflTransClosure.isTransitive R step₁ step₂

theorem ReflTransClosure.fromTransRefl : TransClosure (ReflClosure R) ⊆ ReflTransClosure R :=
  by intro x y step
     induction step
     case base z w h => 
        apply ReflTransClosure.fromReflClosure; assumption
     case step z w k step₁ step₂ ih =>
        cases step₁
        case refl => aesop
        case base step₁ => apply ReflTransClosure.step <;> assumption

@[simp]
abbrev ReflTransSymClosure := ReflTransClosure (SymClosure R)

theorem ReflTransSymClosure.isSymmetric : isSymmetric (ReflTransSymClosure R) := 
  by intro x y step; cases step;
     case refl => aesop
     case base step => 
        induction step
        case base z w step => apply ReflTransClosure.base; aesop
        case step z w u step₁ step₂ step₃ => 
          cases step₃
          case refl => apply ReflTransClosure.base; apply SymClosure.isSymmetric; assumption
          case base step₃ => 
            apply ReflClosure.base
            apply TransClosure.isTransitive (SymClosure R) step₃
            apply TransClosure.base
            apply SymClosure.isSymmetric
            assumption

theorem ReflTransSymClosure.monotone : monotone R S ReflTransSymClosure :=
  by intro step; apply ReflTransClosure.monotone; apply SymClosure.monotone; assumption

theorem ReflTransSymClosure.base: increasing R ReflTransSymClosure :=
  by intro x y h; aesop

instance : Coe (R x y : Prop) (ReflTransSymClosure R x y) where coe h := ReflTransSymClosure.base R h

theorem ReflTransSymClosure.step : ∀x y z, R x y → ReflTransSymClosure R y z → ReflTransSymClosure R x z :=
  by intro x y z step; apply ReflTransClosure.isTransitive (SymClosure R) step

theorem ReflTransSymClosure.fromReflTrans : ReflTransClosure R ⊆ ReflTransSymClosure R :=
  by apply ReflTransClosure.monotone; apply SymClosure.base

instance : Coe (ReflTransClosure R x y : Prop) (ReflTransSymClosure R x y) where coe h := ReflTransSymClosure.fromReflTrans R h

def EquivalenceRel := isSymmetric R ∧ isTransitive R ∧ isReflexive R

theorem ReflTransSymClosure.minimal : EquivalenceRel S → R ⊆ S → ReflTransSymClosure R ⊆ S :=
  by intros equiv sub x y step
     have ⟨sym,trans,refl⟩ := equiv
     clear equiv
     cases step
     case refl => aesop
     case base step =>
        induction step
        case base step => cases step <;> aesop
        case step u v w step₁ _ _ => cases step₁ <;> aesop

def isIrreflexive := ∀x, ¬R x x
def isAsymmetric := ∀x y, R x y → ¬R y x
def isConnected := ∀x y, x ≠ y → R x y ∨ R y x

theorem isAsymmetric.isIrreflexive : isAsymmetric R → isIrreflexive R := by
  intro asymR x; intro loop; apply asymR <;> assumption

structure isStrictOrder (R : α → α → Prop) : Prop where
  irref : isIrreflexive R
  asymm : isAsymmetric R
  trans : isTransitive R

structure isStrictLinearOrder (R : α → α → Prop) : Prop where
  irref : isIrreflexive R
  asymm : isAsymmetric R
  trans : isTransitive R
  cnctd : isConnected R

theorem Nat.isStrictLinearOrder : isStrictLinearOrder (λ x y => Nat.lt y x) := by
  constructor
  · exact Nat.lt_irrefl
  · intro x y edge₁ edge₂; apply Nat.lt_asymm edge₁ <;> assumption
  · intro x y z edge₁ edge₂; apply Nat.lt_trans <;> assumption
  · intro x y neq; apply Nat.lt_or_gt.mp <;> aesop

instance : Coe (isStrictLinearOrder R) (isStrictOrder R) where
  coe s := ⟨s.irref, s.asymm, s.trans⟩
