-- Pruebas_de_que_la_funcion_espejo_de_los_arboles_binarios_es_involutiva.lean
-- Pruebas de que la función espejo de los árboles binarios es involutiva
-- José A. Alonso Jiménez
-- Sevilla, 12 de septiembre de 2021
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- El árbol correspondiente a
--        3
--       / \
--      2   4
--     / \
--    1   5
-- se puede representar por el término
--    nodo 3 (nodo 2 (hoja 1) (hoja 5)) (hoja 4)
-- usado el tipo de dato arbol definido por
--    inductive arbol (α : Type) : Type
--    | hoja : α → arbol
--    | nodo : α → arbol → arbol → arbol
--
-- La imagen especular del árbol anterior es
--      3
--     / \
--    4   2
--       / \
--      5   1
-- cuyo término es
--    nodo 3 (hoja 4) (nodo 2 (hoja 5) (hoja 1))
--
-- La definición de la función que calcula la imagen especular es
--    def espejo : arbol α → arbol α
--    | (hoja x)     := hoja x
--    | (nodo x i d) := nodo x (espejo d) (espejo i)
--
-- Demostrar que la función espejo es involutiva; es decir,
--    espejo (espejo a) = a
-- ---------------------------------------------------------------------

import tactic

variable  {α : Type}

inductive arbol (α : Type) : Type
| hoja : α → arbol
| nodo : α → arbol → arbol → arbol

namespace arbol

variables (a i d : arbol α)
variable  (x : α)

def espejo : arbol α → arbol α
| (hoja x)     := hoja x
| (nodo x i d) := nodo x (espejo d) (espejo i)

@[simp]
lemma espejo_1 :
  espejo (hoja x) = hoja x :=
espejo.equations._eqn_1 x

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) :=
espejo.equations._eqn_2 x i d

-- 1ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { rw espejo_1,
    rw espejo_1, },
  { rw espejo_2,
    rw espejo_2,
    rw Hi,
    rw Hd, },
end

-- 2ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : congr_arg espejo (espejo_1 x)
     ... = hoja x
             : espejo_1 x, },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : espejo_2 (espejo d) (espejo i) x
     ... = nodo x i (espejo (espejo d))
             : congr_arg2 (nodo x) Hi rfl
     ... = nodo x i d
             : congr_arg2 (nodo x) rfl Hd, },
end

-- 3ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : congr_arg espejo (espejo_1 x)
     ... = hoja x
             : by rw espejo_1, },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : by rw espejo_2
     ... = nodo x i (espejo (espejo d))
             : by rw Hi
     ... = nodo x i d
             : by rw Hd, },
end

-- 4ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with x x i d Hi Hd,
  { calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : by simp
     ... = hoja x
             : by simp },
  { calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : by simp
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : by simp
     ... = nodo x i (espejo (espejo d))
             : by simp [Hi]
     ... = nodo x i d
             : by simp [Hd], },
end

-- 5ª demostración
example :
  espejo (espejo a) = a :=
begin
  induction a with _ x i d Hi Hd,
  { simp, },
  { simp [Hi, Hd], },
end

-- 6ª demostración
example :
  espejo (espejo a) = a :=
by induction a ; simp [*]

-- 7ª demostración
example :
  espejo (espejo a) = a :=
arbol.rec_on a
  ( assume x,
    calc espejo (espejo (hoja x))
         = espejo (hoja x)
             : congr_arg espejo (espejo_1 x)
     ... = hoja x
             : espejo_1 x)
  ( assume x i d,
    assume Hi : espejo (espejo i) = i,
    assume Hd : espejo (espejo d) = d,
    calc espejo (espejo (nodo x i d))
         = espejo (nodo x (espejo d) (espejo i))
             : congr_arg espejo (espejo_2 i d x)
     ... = nodo x (espejo (espejo i)) (espejo (espejo d))
             : by rw espejo_2
     ... = nodo x i (espejo (espejo d))
             : by rw Hi
     ... = nodo x i d
             : by rw Hd )

-- 8ª demostración
example :
  espejo (espejo a) = a :=
arbol.rec_on a
  (λ x, by simp )
  (λ x i d Hi Hd, by simp [Hi,Hd])

-- 9ª demostración
lemma espejo_espejo :
  ∀ a : arbol α, espejo (espejo a) = a
| (hoja x)     := by simp
| (nodo x i d) := by simp [espejo_espejo i, espejo_espejo d]

end arbol
