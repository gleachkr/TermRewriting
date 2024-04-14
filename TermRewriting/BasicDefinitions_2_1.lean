import Aesop
import TermRewriting.Relations

variable (R S : α → α → Prop) 

def reducible (x : α) : Prop := ∃y, R x y
def inNormalForm (x : α) : Prop := ¬reducible R x
def normalFormOf (x y : α) : Prop:= ReflTransClosure R x y ∧ inNormalForm R y
def joinable (x y : α) : Prop := ∃z, ReflTransClosure R x z ∧ ReflTransClosure R y z
def churchRosser : Prop := ∀ {x y}, ReflTransSymClosure R x y → joinable R x y
def confluent : Prop := ∀ {x y z}, ReflTransClosure R x y → ReflTransClosure R x z → joinable R y z
def semiconfluent : Prop := ∀ {x y z}, R x y → ReflTransClosure R x z → joinable R y z
def normalizing : Prop := ∀ x, ∃ y, normalFormOf R x y
def isDescendingChain (c : Nat → α) : Prop := ∀n, R (c n) (c $ n + 1)
def terminating  : Prop := ¬∃c, isDescendingChain R c
def convergent : Prop := confluent R ∧ terminating R

theorem joinable.isSymmetric : isSymmetric (joinable R) := 
  by intro x y ⟨j,h₁,h₂⟩; exact ⟨j,h₂,h₁⟩

theorem joinable.isReflexive : isReflexive (joinable R) := 
  by intro x; exact ⟨x, ReflClosure.refl x, ReflClosure.refl x⟩

/-- 
a direct proof that joinability is transitive if R is semiconfluent. You
can also deduce this from semiconfluent implies church-rosser fairly directly
-/
theorem joinable.isTransitive (h : semiconfluent R) : isTransitive (joinable R) := 
  by intro x y z ⟨j₁,step₁,step₂⟩ ⟨j₂,step₃,step₄⟩
     cases step₂
     case refl => 
        exists j₂; constructor
        . apply ReflTransClosure.isTransitive <;> assumption
        . assumption
     case base step₂ =>
        revert x z j₂ 
        induction step₂
        case base v w step =>
          intros x z step₃ j₂ step₄ step₅
          have ⟨j₃, step₆, step₇⟩ := h step step₄
          exists j₃; constructor
          . apply ReflTransClosure.isTransitive <;> assumption
          . apply ReflTransClosure.isTransitive <;> assumption
        case step u v w step _ ih =>
          intros r s step₃ j₃ step₄ step₅
          have ⟨j₄, step₆, step₇⟩ := h step step₄
          apply ih <;> try assumption
          . apply ReflTransClosure.isTransitive <;> assumption

theorem joinable.increasing : increasing R joinable := 
  by intro x y h; exists y; aesop

theorem joinable.fromSymClosure : SymClosure R ⊆ joinable R := 
  by  intro x y step
      cases step
      . apply joinable.increasing; assumption
      . apply joinable.isSymmetric; apply joinable.increasing; assumption

/-- Theorem 2.1.5 a -/
theorem churchRosser_confluent : ∀{R : α → α → Prop}, churchRosser R → confluent R := 
  by  intro R h w y z step₁ step₂; apply h;
      apply ReflTransClosure.isTransitive (y:=w)
      . apply ReflTransSymClosure.isSymmetric; exact ↑step₁
      . exact ↑step₂

/-- Theorem 2.1.5 b -/
theorem confluent_semiconfluent : ∀{R : α → α → Prop}, confluent R → semiconfluent R := 
  by  intro R h x y z step rtcstep; aesop

/-- Theorem 2.1.5 c -/
theorem semiconfluent_rosser : ∀{R: α → α → Prop}, semiconfluent R → churchRosser R := 
  by intro R h₁ x y h₂
     cases h₂
     case refl h => apply joinable.isReflexive
     case base h =>
      induction h
      case base h => apply joinable.fromSymClosure; assumption
      case step z w v symstep _ ih =>
        have ⟨j₁,rtcstep₁,rtcstep₂⟩ := ih
        cases symstep
        case base step =>
          exists j₁; constructor
          · apply ReflTransClosure.step R <;> assumption
          · assumption
        case inv step =>
          have ⟨j₂,rtcstep₃,rtcstep₄⟩ := h₁ step rtcstep₁ 
          exists j₂; constructor
          · assumption
          · apply ReflTransClosure.isTransitive R <;> assumption

/-- Theorem 2.1.5 c, alternative proof -/
theorem semiconfluent_rosser_alt : ∀{R: α → α → Prop}, semiconfluent R → churchRosser R :=
  by intros R h
     apply ReflTransSymClosure.minimal
     . exact ⟨joinable.isSymmetric R, joinable.isTransitive R h, joinable.isReflexive R⟩
     . exact joinable.increasing R

/-- Corrolary 2.1.6 a -/
theorem confluent_nf_flow : ∀{R: α → α → Prop}, confluent R →
  ∀{x y}, ReflTransSymClosure R x y 
    → inNormalForm R y → ReflTransClosure R x y := 
    by intro R h₁ x y h₂ h₃
       have ⟨j,h₄,h₅⟩ := (semiconfluent_rosser $ confluent_semiconfluent h₁) h₂
       cases h₅
       case refl h₅ => aesop
       case base h₅ => 
         apply False.elim ∘ h₃
         cases h₅
         case base => exists j
         case step z step rtcstep => exists z

/-- Corrolary 2.1.6 a -/
theorem confluent_nf_eq : ∀{R: α → α → Prop}, confluent R →
  ∀{x y}, ReflTransSymClosure R x y 
    → inNormalForm R y → inNormalForm R x → x = y := by
    intro R h₁ x y h₂ h₃ h₄
    cases confluent_nf_flow h₁ h₂ h₃
    case refl => aesop
    case base h => 
      cases h <;> apply False.elim <;> apply h₄
      case base step => exact ⟨y, step⟩
      case step z step _ => exact ⟨z, step⟩

/-- Fact 2.1.8 --/
theorem confluent_normalForm : ∀{R: α → α → Prop}, confluent R → 
  ∀{x y z}, normalFormOf R x y → normalFormOf R x z → y = z := by
  intro R h₁ x y z ⟨path₁,h₂⟩ ⟨path₂,h₃⟩
  apply confluent_nf_eq h₁ _ h₃ h₂ 
  apply ReflTransClosure.isTransitive (SymClosure R)
  case a => 
    apply ReflTransSymClosure.isSymmetric R
    revert path₁
    apply ReflTransClosure.monotone
    apply SymClosure.base
  case a =>
    revert path₂
    apply ReflTransClosure.monotone
    apply SymClosure.base

section open Classical

@[simp]
noncomputable def theNormalFormOf {R: α → α → Prop} (h:normalizing R) x :=
  choose (h x)

/-- Theorem 2.1.9 -/
theorem normalFormTheorem : ∀{R: α → α → Prop}, confluent R → 
  ∀(h: normalizing R) {x y}, ReflTransSymClosure R x y 
    → theNormalFormOf h x = theNormalFormOf h y :=
    by intro R h₁ h₂ x y h₃; simp
       have ⟨path₁,n₁⟩ := choose_spec (h₂ x)
       have ⟨path₂,n₂⟩ := choose_spec (h₂ y)
       apply confluent_nf_eq h₁ <;> try assumption
       apply ReflTransClosure.isTransitive (SymClosure R) (y:=x)
       exact ReflTransSymClosure.isSymmetric R path₁
       exact ReflTransClosure.isTransitive (SymClosure R) h₃ path₂
end
