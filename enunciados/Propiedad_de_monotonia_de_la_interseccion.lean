-- Demostrar que si
--    s ⊆ t
-- entonces
--    s ∩ u ⊆ t ∩ u

import data.set.basic
open set

variable {α : Type}
variables s t u : set α

example
  (h : s ⊆ t)
  : s ∩ u ⊆ t ∩ u :=
sorry
