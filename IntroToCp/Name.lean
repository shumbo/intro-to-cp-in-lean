import Mathlib.Data.Fintype.Basic

inductive Name where
| alice : Name
| bob : Name
| charlie : Name
| buyer : Name
| seller : Name
| p₁ : Name
| q₁ : Name
| p₂ : Name
| q₂ : Name
| p₃ : Name
| q₃ : Name

deriving Repr, DecidableEq

instance : Fintype Name where
  elems := {Name.alice, Name.bob, Name.charlie, Name.buyer, Name.seller, Name.p₁, Name.q₁, Name.p₂, Name.q₂, Name.p₃, Name.q₃}
  complete := by
    intro n
    simp
    cases n <;> simp
