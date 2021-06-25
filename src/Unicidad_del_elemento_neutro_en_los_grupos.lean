-- Unicidad_del_elemento_neutro_en_los_grupos.lean
-- Unicidad del elemento neutro en los grupos
-- José A. Alonso Jiménez
-- Sevilla, 4 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que un grupo sólo posee un elemento neutro.
-- ---------------------------------------------------------------------

import algebra.group.basic

universe  u
variables {G : Type u} [group G]

-- 1ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
calc e = 1 * e : (one_mul e).symm
   ... = 1     : h 1

-- 2ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
self_eq_mul_left.mp (congr_arg _ (congr_arg _ (eq.symm (h e))))

-- 3ª demostración
-- ===============

example
  (e : G)
  (h : ∀ x, x * e = x)
  : e = 1 :=
by finish

-- Referencia
-- ==========

-- Propiedad 3.17 del libro "Abstract algebra: Theory and applications"
-- de Thomas W. Judson.
-- http://abstract.ups.edu/download/aata-20200730.pdf#page=49
