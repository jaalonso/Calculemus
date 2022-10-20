-- Propiedad_distributiva_1.lean
-- Si R es un retículo tal que (∀ x y z ∈ R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))),
--   entonces (∀ a b c ∈ R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c))
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-octubre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si R es un retículo tal que
--    ∀ x y z : R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
-- entonces
--    ∀ a b c : R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
-- ----------------------------------------------------------------------

import order.lattice
variables {R : Type*} [lattice R]

example
  (h : ∀ x y z : R, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
  : ∀ a b c : R, (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
begin
  intros a b c,
  calc (a ⊔ b) ⊓ c
       = c ⊓ (a ⊔ b)       : by rw inf_comm
   ... = (c ⊓ a) ⊔ (c ⊓ b) : by rw h
   ... = (a ⊓ c) ⊔ (c ⊓ b) : by rw [@inf_comm _ _ c a]
   ... = (a ⊓ c) ⊔ (b ⊓ c) : by rw [@inf_comm _ _ c b]
end
