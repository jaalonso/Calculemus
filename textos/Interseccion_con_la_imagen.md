---
Título: Intersección con la imagen
Autor:  José A. Alonso
---

Demostrar que
<pre lang="text">
   f[s] ∩ v = f[s ∩ f⁻¹[v]]
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

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
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

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { intro hy,
    cases hy with hyfs yv,
    cases hyfs with x hx,
    cases hx with xs fxy,
    use x,
    split,
    { split,
      { exact xs, },
      { rw mem_preimage,
        rw fxy,
        exact yv, }},
    { exact fxy, }},
  { intro hy,
    cases hy with x hx,
    split,
    { use x,
      split,
      { exact hx.1.1, },
      { exact hx.2, }},
    { cases hx with hx1 fxy,
      rw ← fxy,
      rw ← mem_preimage,
      exact hx1.2, }},
end

-- 2ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { rintros ⟨⟨x, xs, fxy⟩, yv⟩,
    use x,
    split,
    { split,
      { exact xs, },
      { rw mem_preimage,
        rw fxy,
        exact yv, }},
    { exact fxy, }},
  { rintros ⟨x, ⟨xs, xv⟩, fxy⟩,
    split,
    { use [x, xs, fxy], },
    { rw ← fxy,
      rw ← mem_preimage,
      exact xv, }},
end

-- 3ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y,
  split,
  { rintros ⟨⟨x, xs, fxy⟩, yv⟩,
    finish, },
  { rintros ⟨x, ⟨xs, xv⟩, fxy⟩,
    finish, },
end

-- 4ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by ext ; split ; finish

-- 5ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
by finish [ext_iff, iff_def]

-- 6ª demostración
-- ===============

example : (f '' s) ∩ v = f '' (s ∩ f ⁻¹' v) :=
(image_inter_preimage f s v).symm
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Interseccion_con_la_imagen.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Interseccion_con_la_imagen
imports Main
begin

(* 1ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
proof (rule equalityI)
  show "(f ` s) ∩ v ⊆ f ` (s ∩ f -` v)"
  proof (rule subsetI)
    fix y
    assume "y ∈ (f ` s) ∩ v"
    then show "y ∈ f ` (s ∩ f -` v)"
    proof (rule IntE)
      assume "y ∈ v"
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∩ f -` v)"
      proof (rule imageE)
        fix x
        assume "x ∈ s"
        assume "y = f x"
        then have "f x ∈ v"
          using ‹y ∈ v› by (rule subst)
        then have "x ∈ f -` v"
          by (rule vimageI2)
        with ‹x ∈ s› have "x ∈ s ∩ f -` v"
          by (rule IntI)
        then have "f x ∈ f ` (s ∩ f -` v)"
          by (rule imageI)
        with ‹y = f x› show "y ∈ f ` (s ∩ f -` v)"
          by (rule ssubst)
      qed
    qed
  qed
next
  show "f ` (s ∩ f -` v) ⊆ (f ` s) ∩ v"
  proof (rule subsetI)
    fix y
    assume "y ∈ f ` (s ∩ f -` v)"
    then show "y ∈ (f ` s) ∩ v"
    proof (rule imageE)
      fix x
      assume "y = f x"
      assume hx : "x ∈ s ∩ f -` v"
      have "y ∈ f ` s"
      proof -
        have "x ∈ s"
          using hx by (rule IntD1)
        then have "f x ∈ f ` s"
          by (rule imageI)
        with ‹y = f x› show "y ∈ f ` s"
          by (rule ssubst)
      qed
      moreover
      have "y ∈ v"
      proof -
        have "x ∈ f -` v"
          using hx by (rule IntD2)
        then have "f x ∈ v"
          by (rule vimageD)
        with ‹y = f x› show "y ∈ v"
          by (rule ssubst)
      qed
      ultimately show "y ∈ (f ` s) ∩ v"
        by (rule IntI)
    qed
  qed
qed

(* 2ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
proof
  show "(f ` s) ∩ v ⊆ f ` (s ∩ f -` v)"
  proof
    fix y
    assume "y ∈ (f ` s) ∩ v"
    then show "y ∈ f ` (s ∩ f -` v)"
    proof
      assume "y ∈ v"
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∩ f -` v)"
      proof
        fix x
        assume "x ∈ s"
        assume "y = f x"
        then have "f x ∈ v" using ‹y ∈ v› by simp
        then have "x ∈ f -` v" by simp
        with ‹x ∈ s› have "x ∈ s ∩ f -` v" by simp
        then have "f x ∈ f ` (s ∩ f -` v)" by simp
        with ‹y = f x› show "y ∈ f ` (s ∩ f -` v)" by simp
      qed
    qed
  qed
next
  show "f ` (s ∩ f -` v) ⊆ (f ` s) ∩ v"
  proof
    fix y
    assume "y ∈ f ` (s ∩ f -` v)"
    then show "y ∈ (f ` s) ∩ v"
    proof
      fix x
      assume "y = f x"
      assume hx : "x ∈ s ∩ f -` v"
      have "y ∈ f ` s"
      proof -
        have "x ∈ s" using hx by simp
        then have "f x ∈ f ` s" by simp
        with ‹y = f x› show "y ∈ f ` s" by simp
      qed
      moreover
      have "y ∈ v"
      proof -
        have "x ∈ f -` v" using hx by simp
        then have "f x ∈ v" by simp
        with ‹y = f x› show "y ∈ v" by simp
      qed
      ultimately show "y ∈ (f ` s) ∩ v" by simp
    qed
  qed
qed

(* 2ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
proof
  show "(f ` s) ∩ v ⊆ f ` (s ∩ f -` v)"
  proof
    fix y
    assume "y ∈ (f ` s) ∩ v"
    then show "y ∈ f ` (s ∩ f -` v)"
    proof
      assume "y ∈ v"
      assume "y ∈ f ` s"
      then show "y ∈ f ` (s ∩ f -` v)"
      proof
        fix x
        assume "x ∈ s"
        assume "y = f x"
        then show "y ∈ f ` (s ∩ f -` v)"
          using ‹x ∈ s› ‹y ∈ v› by simp
      qed
    qed
  qed
next
  show "f ` (s ∩ f -` v) ⊆ (f ` s) ∩ v"
  proof
    fix y
    assume "y ∈ f ` (s ∩ f -` v)"
    then show "y ∈ (f ` s) ∩ v"
    proof
      fix x
      assume "y = f x"
      assume hx : "x ∈ s ∩ f -` v"
      then have "y ∈ f ` s" using ‹y = f x› by simp
      moreover
      have "y ∈ v" using hx ‹y = f x› by simp
      ultimately show "y ∈ (f ` s) ∩ v" by simp
    qed
  qed
qed

(* 4ª demostración *)

lemma "(f ` s) ∩ v = f ` (s ∩ f -` v)"
  by auto

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
