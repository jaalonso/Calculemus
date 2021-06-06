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

<h4>Soluciones</h4>
<!--more-->

**Soluciones con Lean**

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

Se puede interactuar con la prueba anterior en [esta sesión con Lean](???).

**Soluciones con Isabelle/HOL**

<pre lang="isar">
???
</pre>

**Nuevas soluciones**
<ul>
<li>En los comentarios se pueden escribir nuevas soluciones.
<li>El código se debe escribir entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
</ul>
