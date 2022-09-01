---
Título: Si G es un grupo y a, b ∈ G entonces (a * b)⁻¹ = b⁻¹ * a⁻¹
Autor:  José A. Alonso
---

Demostrar que si G es un grupo y a, b ∈ G, entonces
<pre lang="text">
(a * b)⁻¹ = b⁻¹ * a⁻¹
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables a b : G

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
sorry
</pre>
<!--more-->

<b>Soluciones con Lean</b>

<pre lang="lean">
import algebra.group
variables {G : Type*} [group G]
variables a b : G

-- 1ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_eq_one_iff_inv_eq.mp,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : (mul_assoc _ _ _).symm
   ... = (a * (b * b⁻¹)) * a⁻¹ : congr_arg (* a⁻¹) (mul_assoc a _ _)
   ... = (a * 1) * a⁻¹         : congr_arg2 _ (congr_arg _ (mul_inv_self b)) rfl
   ... = a * a⁻¹               : congr_arg (* a⁻¹) (mul_one a)
   ... = 1                     : mul_inv_self a
end

-- 2ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_eq_one_iff_inv_eq.mp,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : by simp only [mul_assoc]
   ... = (a * (b * b⁻¹)) * a⁻¹ : by simp only [mul_assoc]
   ... = (a * 1) * a⁻¹         : by simp only [mul_inv_self]
   ... = a * a⁻¹               : by simp only [mul_one]
   ... = 1                     : by simp only [mul_inv_self]
end

-- 3ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_eq_one_iff_inv_eq.mp,
  calc a * b * (b⁻¹ * a⁻¹)
       = ((a * b) * b⁻¹) * a⁻¹ : by simp [mul_assoc]
   ... = (a * (b * b⁻¹)) * a⁻¹ : by simp
   ... = (a * 1) * a⁻¹         : by simp
   ... = a * a⁻¹               : by simp
   ... = 1                     : by simp,
end

-- 4ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
-- by library_search
mul_inv_rev a b

-- 5ª demostración
-- ===============

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
by simp
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Inverso_del_producto.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.
