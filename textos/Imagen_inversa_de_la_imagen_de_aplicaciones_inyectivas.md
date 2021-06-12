---
Título: Imagen inversa de la imagen de aplicaciones inyectivas
Autor:  José A. Alonso
---

Demostrar que si f es inyectiva, entonces
<pre lang="text">
    f⁻¹[f[s]] ⊆ s
</pre>

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.set.basic

open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.set.basic

open set function

variables {α : Type*} {β : Type*}
variable  f : α → β
variable  s : set α

-- 1ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rw mem_preimage at hx,
  rw mem_image_eq at hx,
  cases hx with y hy,
  cases hy with ys fyx,
  unfold injective at h,
  have h1 : y = x := h fyx,
  rw ← h1,
  exact ys,
end

-- 2ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rw mem_preimage at hx,
  rcases hx with ⟨y, ys, fyx⟩,
  rw ← h fyx,
  exact ys,
end

-- 3ª demostración
-- ===============

example
  (h : injective f)
  : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, hy⟩,
  rw ← h hy,
  exact ys,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://bit.ly/3ptTl2C" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>,
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory Imagen_inversa_de_la_imagen_de_aplicaciones_inyectivas
imports Main
begin

section ‹?ª demostración›

lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
proof (rule subsetI)
  fix x
  assume "x ∈ f -` (f ` s)"
  then have "f x ∈ f ` s"
    by (rule vimageD)
  then show "x ∈ s"
  proof (rule imageE)
    fix y
    assume "f x = f y"
    assume "y ∈ s"
    have "x = y"
      using ‹inj f› ‹f x = f y› by (rule injD)
    then show "x ∈ s"
      using ‹y ∈ s›  by (rule ssubst)
  qed
qed

section ‹2ª demostración›

lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
proof
  fix x
  assume "x ∈ f -` (f ` s)"
  then have "f x ∈ f ` s"
    by simp
  then show "x ∈ s"
  proof
    fix y
    assume "f x = f y"
    assume "y ∈ s"
    have "x = y"
      using ‹inj f› ‹f x = f y› by (rule injD)
    then show "x ∈ s"
      using ‹y ∈ s›  by simp
  qed
qed

section ‹3ª demostración›

lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
  using assms
  unfolding inj_def
  by auto

section ‹4ª demostración›

lemma
  assumes "inj f"
  shows "f -` (f ` s) ⊆ s"
  using assms
  by (simp only: inj_vimage_image_eq)

end
</pre>
[/expand]

[expand title="Nuevas soluciones"]
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
[/expand]
