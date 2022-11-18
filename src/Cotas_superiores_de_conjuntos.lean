-- Cotas_superiores_de_conjuntos.lean
-- Si a es una cota superior de s y a ≤ b, entonces b es una cota
--   superior de s.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-noviembre-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si a es una cota superior de s y a ≤ b, entonces b es
-- una cota superior de s.
-- ----------------------------------------------------------------------

import tactic

variables {α : Type*} [partial_order α]
variables s : set α
variables a b : α

-- (cota_superior s a) expresa que a es una cota superior de s.
def cota_superior (s : set α) (a : α) := ∀ {x}, x ∈ s → x ≤ a

-- 1ª demostración
-- ===============

example
  (h1 : cota_superior s a)
  (h2 : a ≤ b)
  : cota_superior s b :=
begin
  intro x,
  assume xs : x ∈ s,
  have h3 : x ≤ a := h1 xs,
  show x ≤ b,
    by exact le_trans h3 h2,
end

-- 2ª demostración
-- ===============

example
  (h1 : cota_superior s a)
  (h2 : a ≤ b)
  : cota_superior s b :=
begin
  intros x xs,
  calc x ≤ a : h1 xs
     ... ≤ b : h2
end
