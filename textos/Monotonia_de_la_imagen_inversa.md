---
Título: Monotonía de la imagen inversa
Autor:  José A. Alonso
---

Demostrar que si u ⊆ v, entonces
<pre lang="text">
    f⁻¹[u] ⊆ f⁻¹[v]
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic
open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic
open set

variables {α : Type*} {β : Type*}
variable  f : α → β
variables u v : set β

-- 1ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  apply mem_preimage.mpr,
  apply h,
  apply mem_preimage.mp,
  exact hx,
end

-- 2ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  apply h,
  exact hx,
end

-- 3ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  exact h hx,
end

-- 4ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
λ x hx, h hx

-- 5ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

-- 6ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
preimage_mono h

-- 7ª demostración
-- ===============

example
  (h : u ⊆ v)
  : f ⁻¹' u ⊆ f ⁻¹' v :=
by tauto
</pre>

Se puede interactuar con la prueba anterior en <a href="https://bit.ly/34YYshL" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Monotonia_de_la_imagen_inversa
imports Main
begin

section ‹1ª demostración›

lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
proof (rule subsetI)
  fix x
  assume "x ∈ f -` u"
  then have "f x ∈ u"
    by (rule vimageD)
  then have "f x ∈ v"
    using ‹u ⊆ v› by (rule set_rev_mp)
  then show "x ∈ f -` v"
    by (simp only: vimage_eq)
qed

section ‹2ª demostración›

lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
proof
  fix x
  assume "x ∈ f -` u"
  then have "f x ∈ u"
    by simp
  then have "f x ∈ v"
    using ‹u ⊆ v› by (rule set_rev_mp)
  then show "x ∈ f -` v"
    by simp
qed

section ‹3ª demostración›

lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
  using assms
  by (simp only: vimage_mono)

section ‹4ª demostración›

lemma
  assumes "u ⊆ v"
  shows "f -` u ⊆ f -` v"
  using assms
  by blast

end
</pre>
[/expand]

[expand title="Nuevas soluciones"]
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;lean&quot;&#62; (o &#60;pre lang=&quot;isar&quot;&#62;) y otra con &#60;/pre&#62;
</ul>
[/expand]
