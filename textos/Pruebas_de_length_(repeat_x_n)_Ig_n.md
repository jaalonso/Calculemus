---
Título: Pruebas de length (repeat x n) = n
Autor:  José A. Alonso
---

En Lean están definidas las funciones length y repeat tales que

+ (length xs) es la longitud de la lista xs. Por ejemplo,
<pre lang="text">
     length [1,2,5,2] = 4
</pre>
+ (repeat x n) es la lista que tiene el elemento x n veces. Por
  ejemplo,
<pre lang="text">
     repeat 7 3 = [7, 7, 7]
</pre>

Demostrar que
<pre lang="text">
   length (repeat x n) = n
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.list.basic
open nat
open list

variable {α : Type}
variable (x : α)
variable (n : ℕ)

example :
  length (repeat x n) = n :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.list.basic
open nat
open list

set_option pp.structure_projections false

variable {α : Type}
variable (x : α)
variable (n : ℕ)

example :
  length (repeat x n) = n :=
begin
  induction n with n HI,
  { calc length (repeat x 0)
          = length []                : rfl
      ... = 0                        : rfl },
  { calc length (repeat x (succ n))
         = length (x :: repeat x n)  : rfl
     ... = length (repeat x n) + 1   : rfl
     ... = n + 1                     : by rw HI
     ... = succ n                    : rfl, },
end

-- 2ª demostración
example : length (repeat x n) = n :=
begin
  induction n with n HI,
  { refl, },
  { dsimp,
    rw HI, },
end

-- 3ª demostración
example : length (repeat x n) = n :=
begin
  induction n with n HI,
  { simp, },
  { simp [HI], },
end

-- 4ª demostración
example : length (repeat x n) = n :=
by induction n ; simp [*]

-- 5ª demostración
example : length (repeat x n) = n :=
nat.rec_on n
  ( show length (repeat x 0) = 0, from
      calc length (repeat x 0)
           = length []                : rfl
       ... = 0                        : rfl )
  ( assume n,
    assume HI : length (repeat x n) = n,
    show length (repeat x (succ n)) = succ n, from
      calc length (repeat x (succ n))
           = length (x :: repeat x n) : rfl
       ... = length (repeat x n) + 1  : rfl
       ... = n + 1                    : by rw HI
       ... = succ n                   : rfl )

-- 6ª demostración
example : length (repeat x n) = n :=
nat.rec_on n
  ( by simp )
  ( λ n HI, by simp [HI])

-- 7ª demostración
example : length (repeat x n) = n :=
length_repeat x n

-- 8ª demostración
example : length (repeat x n) = n :=
by simp

-- 9ª demostración
lemma length_repeat_1 :
  ∀ n, length (repeat x n) = n
| 0 := by calc length (repeat x 0)
               = length ([] : list α)         : rfl
           ... = 0                            : rfl
| (n+1) := by calc length (repeat x (n + 1))
                   = length (x :: repeat x n) : rfl
               ... = length (repeat x n) + 1  : rfl
               ... = n + 1                    : by rw length_repeat_1

-- 10ª demostración
lemma length_repeat_2 :
  ∀ n, length (repeat x n) = n
| 0     := by simp
| (n+1) := by simp [*]
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pruebas_de_length_(repeat_x_n)_Ig_n.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "Pruebas_de_length_(repeat_x_n)_Ig_n"
imports Main
begin

(* 1ª demostración⁾*)
lemma "length (replicate n x) = n"
proof (induct n)
  have "length (replicate 0 x) = length ([] :: 'a list)"
    by (simp only: replicate.simps(1))
  also have "… = 0"
    by (rule list.size(3))
  finally show "length (replicate 0 x) = 0"
    by this
next
  fix n
  assume HI : "length (replicate n x) = n"
  have "length (replicate (Suc n) x) =
        length (x # replicate n x)"
    by (simp only: replicate.simps(2))
  also have "… = length (replicate n x) + 1"
    by (simp only: list.size(4))
  also have "… = Suc n"
    by (simp only: HI)
  finally show "length (replicate (Suc n) x) = Suc n"
    by this
qed

(* 2ª demostración⁾*)
lemma "length (replicate n x) = n"
proof (induct n)
  show "length (replicate 0 x) = 0"
    by simp
next
  fix n
  assume "length (replicate n x) = n"
  then show "length (replicate (Suc n) x) = Suc n"
    by simp
qed

(* 3ª demostración⁾*)
lemma "length (replicate n x) = n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

(* 4ª demostración⁾*)
lemma "length (replicate n x) = n"
  by (rule length_replicate)

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
