import Mathlib.Order.Disjoint
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import «IntroToCp».Name

variable {α : Type} [DecidableEq α] [fin : Fintype α]

-- # Simple Choreographies

-- ## Syntax

inductive SimpleChor (α : Type) where
  | done : SimpleChor α
  | comm (p : α) (q : α) (C : SimpleChor α) (hneq : p ≠ q := by simp [*]) : SimpleChor α
deriving DecidableEq

-- terminated choreography
def SimpleChor.𝕆 : SimpleChor α := SimpleChor.done

notation:10 p " ~> " q " ; " C => SimpleChor.comm p q C

-- Example 2.2
#check Name.buyer ~> Name.seller ; Name.seller ~> Name.buyer ; SimpleChor.done

-- Exercise 2.1
def ringProtocol := Name.alice ~> Name.bob ; Name.bob ~> Name.charlie ; Name.charlie ~> Name.alice ; SimpleChor.done

-- Exercise 2.2
def scatterProtocol := Name.alice ~> Name.bob ; Name.alice ~> Name.charlie ; SimpleChor.done

-- Semantics


def Transition (S : Type) (L : Type) : Type := S → L → S → Prop
inductive Transition.Multi {S : Type} {L : Type} (t : Transition S L) : S → List L → S → Prop where
  | rfl : ∀ (s₀: S), Multi t s₀ [] s₀
  | step : ∀ (s: S) (μ : L) (s' : S) (μ' : List L) (s'' : S),
      t s μ s' → Multi t s' μ' s'' → Multi t s (μ :: μ') s''

def pn (s : α × α) : Finset α := {s.fst, s.snd}

inductive SimpleChor.Step : Transition (SimpleChor α) (α × α) where
  | comm : ∀ (p q : α) (C : SimpleChor α), (hneq : p ≠ q )→ Step (SimpleChor.comm p q C) (p, q) C
  | delay : ∀ C μ C' (p q : α), (hneq : p ≠ q) → Step C μ C' → Disjoint {p, q} (pn μ) → Step (p ~> q ; C) μ (p ~> q ; C')

-- Example 2.3
example : SimpleChor.Step
  (Name.buyer ~> Name.seller ; Name.seller ~> Name.buyer ; SimpleChor.done)
  (Name.buyer, Name.seller)
  (Name.seller ~> Name.buyer ; SimpleChor.done) := by apply SimpleChor.Step.comm ; simp

def SimpleChor.MultiStep {α : Type} [DecidableEq α] := Transition.Multi (S := SimpleChor α) (SimpleChor.Step)

example : SimpleChor.MultiStep
  (Name.p₁ ~> Name.q₁ ; Name.p₂ ~> Name.q₂ ; Name.p₃ ~> Name.q₃ ; SimpleChor.𝕆)
  [(Name.p₁, Name.q₁), (Name.p₂, Name.q₂), (Name.p₃, Name.q₃)]
  SimpleChor.𝕆
:= by
  apply Transition.Multi.step _ _ (Name.p₂ ~> Name.q₂ ; Name.p₃ ~> Name.q₃ ; SimpleChor.𝕆) _ _
  apply SimpleChor.Step.comm
  simp
  apply Transition.Multi.step _ _ (Name.p₃ ~> Name.q₃ ; SimpleChor.𝕆) _ _
  apply SimpleChor.Step.comm
  simp
  apply Transition.Multi.step _ _ (SimpleChor.𝕆) _ _
  apply SimpleChor.Step.comm
  simp
  apply Transition.Multi.rfl
