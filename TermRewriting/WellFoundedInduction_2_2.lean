import TermRewriting.BasicDefinitions_2_1
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fintype.Card

variable (R S : α → α → Prop) 

@[simp]
def WFI := ∀P: α → Prop, (∀x, (∀y, TransClosure R x y → P y) → P x) → ∀x, P x

@[simp]
def wWFI := ∀P: α → Prop, (∀x, (∀y, R x y → P y) → P x) → ∀x, P x

section open Classical

def iter_chain (f : α → α) (x : α) : Nat → α
  | 0 => x
  | Nat.succ n => f (iter_chain f x n)

theorem iter_chain_rel : ∀f,(∀x, R x (f x)) → ∀x n, R (iter_chain f x n) (iter_chain f x (Nat.succ n)) := 
  by intro f h x n
     conv => rhs; unfold iter_chain
     apply h

theorem terminating_wWFI : terminating R → wWFI R := 
  by apply byContradiction
     simp; intro rterminates P ind y; apply byContradiction; intro start
     have successor : ∀z: {z : α // ¬P z}, ∃w : {z : α // ¬P z}, R z w := 
      by intro ⟨z,zprop⟩
         have ⟨w',wprop'⟩ := not_forall.mp $ zprop ∘ ind z
         simp at wprop'
         let w : {z : α // ¬P z} := ⟨w',wprop'.2⟩
         exists w
         simp
         exact wprop'.1
     have ⟨next,cprop⟩ := skolem.mp successor
     have root : {z : α // ¬ P z} := ⟨y,start⟩
     have iter_chain_prop := iter_chain_rel (λ x y => R x.val y.val) next cprop root
     have trans_dc : isDescendingChain R (λn ↦ (iter_chain next root n).val) := by
        intro n; simp; apply iter_chain_prop
     apply rterminates
     aesop

theorem tcTerminating_WFI : terminating (TransClosure R) → WFI R := 
  by intro h; exact terminating_wWFI (TransClosure R) h

-- Proof idea. Given the knowledge that if all transitive desendents of
-- a node have x have P, then x does too, use one-step induction to show
-- that everything is such that all its transitive descendents have P.
-- Conclude that everything has P.
theorem wWFI_WFI : wWFI R → WFI R := 
  by simp; intro ind P closure
     let closureProp (x : α) := ∀y, TransClosure R x y → P y
     have key : ∀x, closureProp x := by
        apply ind
        intro x ih z tcstep
        cases tcstep
        case a.base step =>
          apply closure
          apply ih
          assumption
        case a.step w step tcstep =>
          apply (ih w step)
          assumption
     intro x
     apply closure
     intro y
     apply key

/-- Theorem 2.2.1 -/
theorem terminating_WFI : terminating R → WFI R := by
  intro h; apply wWFI_WFI; apply terminating_wWFI; assumption

theorem chain_shift : ∀c, isDescendingChain R c → isDescendingChain R (λ n ↦ c (n + 1)) := by
  intro c chain n; apply chain

theorem chain_lift : ∀c, isDescendingChain R c → isDescendingChain (TransClosure R) c := by
  intro c chain n; apply TransClosure.base; apply chain

theorem chain_tc_rel : ∀{c}, isDescendingChain R c → ∀{m n}, m < n → TransClosure R (c m) (c n) := by
  intro c h m n; revert m; induction n <;> intro m lt
  case zero => contradiction
  case succ n ih => 
    cases lt
    case refl => apply TransClosure.base; apply h
    case step le =>
      apply TransClosure.push (y := c n)
      · apply ih; apply le
      · apply h

theorem WFI.tc_terminating : WFI R → terminating (TransClosure R) :=
  by intro wfi; unfold terminating
     have key : ∀x, ¬∃c, isDescendingChain (TransClosure R) c ∧ c 0 = x := by
        apply wfi; intro x ih ⟨chain, chainProp, chainEq⟩
        apply ih (chain 1)
        · rw [←chainEq]; apply chainProp
        · exists (λ n ↦ chain (n + 1)); simp; apply chain_shift; assumption
     intro ⟨chain,absurd⟩
     apply key; exists chain

/-- Exercise 2.4 -/
theorem terminating.trans_closure : terminating (TransClosure R) ↔ terminating R := by
  constructor
  case mp => intro term ⟨chain, absurd⟩; apply term; exists chain; apply chain_lift; assumption
  case mpr => intro term; apply WFI.tc_terminating; apply terminating_WFI; assumption

/-- Theorem 2.2.2 -/
theorem WFI.terminating : WFI R → terminating R := by
  intro wfi; apply (terminating.trans_closure R).mp; exact WFI.tc_terminating R wfi

@[simp]
def finitely_branching := ∀x, Set.Finite { z | R x z }
@[simp]
def globally_finite := finitely_branching (TransClosure R)
@[simp]
def acyclic := ∀x, ¬TransClosure R x x

/-- Lemma 2.2.4 -/
theorem terminating.finite_local_global : terminating R → finitely_branching R → globally_finite R := by
  intro term fini; simp
  apply (terminating_WFI R)
  · assumption
  · intro x ih
    simp_all
    let f : {y // R x y } → Set α := λy ↦ { z | TransClosure R y.val z }
    have f_fin : ∀y, Set.Finite (f y) := by
      intro y; apply ih y; exact TransClosure.base x y.val y.prop
    let f_union := ⋃ (i : {y // R x y}), f i
    have : Set.Finite f_union := @Set.finite_iUnion _ _ (fini x) _ f_fin 
    apply Set.Finite.subset (s := {y | R x y} ∪ f_union)
    · apply Set.Finite.union <;> aesop
    · intro z h; cases h
      case a.ht.base step => exact Or.inl step
      case a.ht.step w step tcstep =>
        apply Or.inr; exists (f ⟨w, step⟩); constructor
        · simp
        · exact tcstep

theorem terminating.acyclic : terminating R → acyclic R := by
  intro term x cyc
  apply (terminating.trans_closure R).mpr  term
  exists λ_ ↦ x
  intro _
  simp_all

theorem acyclic.chain_injection : acyclic R → ∀c, isDescendingChain R c → 
    Function.Injective c := 
  by intro acyc chain desc x y eq
     apply byContradiction; intro neq
     cases Nat.lt_or_gt.mp neq <;> apply acyc (chain x)
     case h.inl lt => 
      conv => rhs; rw [eq]
      apply chain_tc_rel <;> aesop
     case h.inr lt =>
      conv => lhs; rw [eq]
      apply chain_tc_rel <;> aesop

theorem acyclic.tc_infinite : acyclic R → ∀{c}, isDescendingChain R c → 
    Infinite { z // TransClosure R (c 0) z } :=
  by intro acyc chain desc
     let f : Nat → { z // TransClosure R (chain 0) z } := 
        λn ↦ ⟨chain (n + 1), chain_tc_rel R desc (Nat.zero_lt_succ n)⟩
     apply Infinite.of_injective f
     intro x y eq
     have eq_c : (f x).val = (f y).val := by rw [eq]
     have := acyclic.chain_injection R acyc chain desc eq_c
     simp_all

theorem acyclic.tc_subset : acyclic R → ∀x y, R x y → 
    {z | TransClosure R y z} ⊂ { z | TransClosure R x z} := 
  by intro acyc x y step; constructor
     case left => 
       intro z hyp
       induction hyp
       case base v w step₂ => 
          apply TransClosure.step
          · assumption
          · apply TransClosure.base; assumption
       case step t u v step₂ tcstep _ => 
          apply TransClosure.step
          · assumption
          · apply TransClosure.step <;> assumption
     case right => 
        intro absurd
        apply acyc
        apply absurd
        apply TransClosure.base
        assumption

theorem acyclic.fintype_tc_reducing : 
  acyclic R → ∀x y, R x y → 
    [Fintype {z | TransClosure R y z}] → [Fintype {z | TransClosure R x z}] →
    Fintype.card {z | TransClosure R y z} < Fintype.card { z | TransClosure R x z} :=
  by intro acyc x y step inst₁ inst₂
     apply Set.card_lt_card
     apply acyclic.tc_subset <;> assumption

theorem globally_finite_fintype : globally_finite R → ∀x, Fintype {z | TransClosure R x z} := 
  by intro fini x; simp; apply Set.Finite.fintype; apply fini

noncomputable def globally_finite.card (h: globally_finite R) (x : α) : Nat :=
  @Fintype.card { z | TransClosure R x z} (globally_finite_fintype R h x)

theorem acyclic.finite_tc_reducing :
  acyclic R → ∀x y, R x y → (h : globally_finite R) →
    globally_finite.card R h y < globally_finite.card R h x :=
  by intro acyc x y step fini; unfold globally_finite.card
     apply @Set.card_lt_card α { z | TransClosure R y z} { z | TransClosure R x z} (globally_finite_fintype R fini y) (globally_finite_fintype R fini x)
     apply acyclic.tc_subset <;> assumption

/-- Lemma 2.2.5 -/
theorem acyclic.globally_finite_terminates : 
  acyclic R → globally_finite R → terminating R := by
  intro acyc fini ⟨chain,desc⟩
  have infini : Infinite { z // TransClosure R (chain 0) z } := acyclic.tc_infinite R acyc desc
  apply infini.not_finite
  apply fini
