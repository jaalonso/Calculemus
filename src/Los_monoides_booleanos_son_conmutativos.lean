-- Los_monoides_booleanos_son_conmutativos.lean
-- Los monoides booleanos son conmutativos
-- José A. Alonso Jiménez
-- Sevilla, 10 de julio de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Un monoide es un conjunto junto con una operación binaria que es
-- asociativa y tiene elemento neutro.
--
-- Un monoide M es booleano si
--    ∀ x ∈ M, x * x = 1
-- y es conmutativo si
--    ∀ x y ∈ M, x * y = y * x
--
-- En Lean, está definida la clase de los monoides (como `monoid`) y sus
-- propiedades características son
--    mul_assoc : (a * b) * c = a * (b * c)
--    one_mul :   1 * a = a
--    mul_one :   a * 1 = a
--
-- Demostrar que los monoides booleanos son conmutativos.
-- ---------------------------------------------------------------------

import algebra.group.basic

example
  {M : Type} [monoid M]
  (h : ∀ x : M, x * x = 1)
  : ∀ x y : M, x * y = y * x :=
begin
  intros a b,
  calc a * b
       = (a * b) * 1
         : (mul_one (a * b)).symm
   ... = (a * b) * (a * a)
         : congr_arg ((*) (a*b)) (h a).symm
   ... = ((a * b) * a) * a
         : (mul_assoc (a*b) a a).symm
   ... = (a * (b * a)) * a
         : congr_arg (* a) (mul_assoc a b a)
   ... = (1 * (a * (b * a))) * a
         : congr_arg (* a) (one_mul (a*(b*a))).symm
   ... = ((b * b) * (a * (b * a))) * a
         : congr_arg (* a) (congr_arg (* (a*(b*a))) (h b).symm)
   ... = (b * (b * (a * (b * a)))) * a
         : congr_arg (* a) (mul_assoc b b (a*(b*a)))
   ... = (b * ((b * a) * (b * a))) * a
         : congr_arg (* a) (congr_arg ((*) b) (mul_assoc b a (b*a)).symm)
   ... = (b * 1) * a
         : congr_arg (* a) (congr_arg ((*) b) (h (b*a)))
   ... = b * a
         : congr_arg (* a) (mul_one b),
end
