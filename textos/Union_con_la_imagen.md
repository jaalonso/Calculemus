---
Título: Unión con la imagen
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[s ∪ f⁻¹[v]] ⊆ f[s] ∪ v
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
import tactic

open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α
variable  v : set β

-- 1ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  intros y hy,
  cases hy with x hx,
  cases hx with hx1 fxy,
  cases hx1 with xs xv,
  { left,
    use x,
    split,
    { exact xs, },
    { exact fxy, }},
  { right,
    rw ← fxy,
    exact xv, },
end

-- 2ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  rintros y ⟨x, xs | xv, fxy⟩,
  { left,
    use [x, xs, fxy], },
  { right,
    rw ← fxy,
    exact xv, },
end

-- 3ª demostración
-- ===============

example : f '' (s ∪ f ⁻¹' v) ⊆ f '' s ∪ v :=
begin
  rintros y ⟨x, xs | xv, fxy⟩;
  finish,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Union_con_la_imagen.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Union_con_la_imagen
imports Main
begin

(* 1ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof (rule subsetI)
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v"
    proof (rule UnE)
      assume "x ∈ s"
      then have "f x ∈ f ` s"
        by (rule imageI)
      with ‹y = f x› have "y ∈ f ` s"
        by (rule ssubst)
      then show "y ∈ f ` s ∪ v"
        by (rule UnI1)
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v"
        by (rule vimageD)
      with ‹y = f x› have "y ∈ v"
        by (rule ssubst)
      then show "y ∈ f ` s ∪ v"
        by (rule UnI2)
    qed
  qed
qed

(* 2ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v"
    proof
      assume "x ∈ s"
      then have "f x ∈ f ` s" by simp
      with ‹y = f x› have "y ∈ f ` s" by simp
      then show "y ∈ f ` s ∪ v" by simp
    next
      assume "x ∈ f -` v"
      then have "f x ∈ v" by simp
      with ‹y = f x› have "y ∈ v" by simp
      then show "y ∈ f ` s ∪ v" by simp
    qed
  qed
qed

(* 3ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v"
    proof
      assume "x ∈ s"
      then show "y ∈ f ` s ∪ v" by (simp add: ‹y = f x›)
    next
      assume "x ∈ f -` v"
      then show "y ∈ f ` s ∪ v" by (simp add: ‹y = f x›)
    qed
  qed
qed

(* 4ª demostración *)

lemma "f ` (s ∪ f -` v) ⊆ f ` s ∪ v"
proof
  fix y
  assume "y ∈ f ` (s ∪ f -` v)"
  then show "y ∈ f ` s ∪ v"
  proof
    fix x
    assume "y = f x"
    assume "x ∈ s ∪ f -` v"
    then show "y ∈ f ` s ∪ v" using ‹y = f x› by blast
  qed
qed

(* 5ª demostración *)

lemma "f ` (s ∪ f -` u) ⊆ f ` s ∪ u"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
