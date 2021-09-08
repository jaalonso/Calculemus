-- Razonamiento_sobre_arboles_binarios_Aplanamiento_e_imagen_especular.lean
-- Razonamiento sobre árboles binarios: Aplanamiento e imagen especular
-- José A. Alonso Jiménez
-- Sevilla, 13 de septiembre de 2021
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
-- usando el tipo de dato arbol definido por
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
-- y la lista obtenida aplanándolo (recorriéndolo en orden infijo) es
--    [4, 3, 5, 2, 1]
--
-- La definición de la función que calcula la imagen especular es
--    def espejo : arbol α → arbol α
--    | (hoja x)     := hoja x
--    | (nodo x i d) := nodo x (espejo d) (espejo i)
-- y la que aplana el árbol es
--    def aplana : arbol α → list α
--    | (hoja x)     := [x]
--    | (nodo x i d) := (aplana i) ++ [x] ++ (aplana d)
--
-- Demostrar que
--    aplana (espejo a) = rev (aplana a)
-- ---------------------------------------------------------------------

import tactic
open list

variable {α : Type}

-- Para que no use la notación con puntos
set_option pp.structure_projections false

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
rfl

@[simp]
lemma espejo_2 :
  espejo (nodo x i d) = nodo x (espejo d) (espejo i) :=
rfl

def aplana : arbol α → list α
| (hoja x)     := [x]
| (nodo x i d) := (aplana i) ++ [x] ++ (aplana d)

@[simp]
lemma aplana_1 :
  aplana (hoja x) = [x] :=
rfl

@[simp]
lemma aplana_2 :
  aplana (nodo x i d) = (aplana i) ++ [x] ++ (aplana d) :=
rfl

-- 1ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { rw espejo_1,
    rw aplana_1,
    rw reverse_singleton, },
  { rw espejo_2,
    rw aplana_2,
    rw [Hi, Hd],
    rw aplana_2,
    rw reverse_append,
    rw reverse_append,
    rw reverse_singleton,
    rw append_assoc, },
end

-- 2ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)
             : congr_arg aplana (espejo_1 x)
     ... = [x]
             : aplana_1 x
     ... = reverse [x]
             : reverse_singleton x
     ... = reverse (aplana (hoja x))
             : congr_arg reverse (aplana_1 x).symm, },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : congr_arg aplana (espejo_2 i d x)
     ... = (aplana (espejo d) ++ [x]) ++ aplana (espejo i)
             : aplana_2 (espejo d) (espejo i) x
     ... = (reverse (aplana d) ++ [x]) ++ aplana (espejo i)
             : congr_arg2 (++) (congr_arg2 (++) Hd rfl) rfl
     ... = (reverse (aplana d) ++ [x]) ++ reverse (aplana i)
             : congr_arg2 (++) rfl Hi
     ... = (reverse (aplana d) ++ reverse [x]) ++ reverse (aplana i)
             : congr_arg2 (++) (congr_arg2 (++) rfl (reverse_singleton x).symm) rfl
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : congr_arg2 (++) (reverse_append [x] (aplana d)).symm rfl
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : (reverse_append (aplana i) ([x] ++ aplana d)).symm
     ... = reverse ((aplana i ++ [x]) ++ aplana d)
             : congr_arg reverse (append_assoc (aplana i) [x] (aplana d)).symm
     ... = reverse (aplana (nodo x i d))
             : congr_arg reverse (aplana_2 i d x), },
end

-- 3ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)
             : by simp only [espejo_1]
     ... = [x]
             : by rw aplana_1
     ... = reverse [x]
             : by rw reverse_singleton
     ... = reverse (aplana (hoja x))
             : by simp only [aplana_1], },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : by simp only [espejo_2]
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             : by rw aplana_2
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by rw [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             : by simp only [reverse_singleton]
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ [x] ++ aplana d)
             : by simp only [append_assoc]
     ... = reverse (aplana (nodo x i d))
             : by simp only [aplana_2], },
end

-- 3ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { calc aplana (espejo (hoja x))
         = aplana (hoja x)           : by simp
     ... = [x]                       : by simp
     ... = reverse [x]               : by simp
     ... = reverse (aplana (hoja x)) : by simp, },
  { calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : by simp
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             : by simp
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by simp [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             : by simp
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : by simp
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : by simp
     ... = reverse (aplana i ++ [x] ++ aplana d)
             : by simp
     ... = reverse (aplana (nodo x i d))
             : by simp },
end

-- 5ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { simp, },
  { calc aplana (espejo (nodo x i d))
         = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by simp [Hi, Hd]
     ... = reverse (aplana (nodo x i d))
             : by simp },
end

-- 6ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
begin
  induction a with x x i d Hi Hd,
  { simp, },
  { simp [Hi, Hd], },
end

-- 7ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
by induction a ; simp [*]

-- 8ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
arbol.rec_on a
  ( assume x,
    calc aplana (espejo (hoja x))
         = aplana (hoja x)
             : by simp only [espejo_1]
     ... = [x]
             : by rw aplana_1
     ... = reverse [x]
             : by rw reverse_singleton
     ... = reverse (aplana (hoja x))
             : by simp only [aplana_1])
  ( assume x i d,
    assume Hi : aplana (espejo i) = reverse (aplana i),
    assume Hd : aplana (espejo d) = reverse (aplana d),
    calc aplana (espejo (nodo x i d))
         = aplana (nodo x (espejo d) (espejo i))
             : by simp only [espejo_2]
     ... = aplana (espejo d) ++ [x] ++ aplana (espejo i)
             : by rw aplana_2
     ... = reverse (aplana d) ++ [x] ++ reverse (aplana i)
             : by rw [Hi, Hd]
     ... = reverse (aplana d) ++ reverse [x] ++ reverse (aplana i)
             : by simp only [reverse_singleton]
     ... = reverse ([x] ++ aplana d) ++ reverse (aplana i)
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ ([x] ++ aplana d))
             : by simp only [reverse_append]
     ... = reverse (aplana i ++ [x] ++ aplana d)
             : by simp only [append_assoc]
     ... = reverse (aplana (nodo x i d))
             : by simp only [aplana_2])

-- 9ª demostración
example :
  aplana (espejo a) = reverse (aplana a) :=
arbol.rec_on a
  (λ x, by simp)
  (λ x i d Hi Hd, by simp [Hi, Hd])

-- 10ª demostración
lemma aplana_espejo :
  ∀ a : arbol α, aplana (espejo a) = reverse (aplana a)
| (hoja x)     := by simp
| (nodo x i d) := by simp [aplana_espejo i,
                           aplana_espejo d]

end arbol
