import TermRewriting.BasicDefinitions_2_1

variable (R S : α → α → Prop) 

def WFI R := ∀P: α → Prop, (∀x, (∀y, TransClosure R x y → P y) → P x) → ∀x, P x

/-- Theorem 2.2.1 -/
theorem terminating_WFI : terminating R → WFI R := by sorry
