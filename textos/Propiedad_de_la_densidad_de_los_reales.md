---
Título: Propiedad de la densidad de los reales
Autor:  José A. Alonso
---

Sean x, y números reales tales que
<pre lang="text">
   ∀ z, y < z → x ≤ z
</pre>
Demostrar que x ≤ y.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variables {x y : ℝ}

example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variables {x y : ℝ}

-- 1ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  apply (lt_irrefl a),
  calc a
       < x : ha.2
   ... ≤ a : h a ha.1,
end

-- 2ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  apply (lt_irrefl a),
  exact lt_of_lt_of_le ha.2 (h a ha.1),
end

-- 3ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  cases (exists_between hxy) with a ha,
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1)),
end

-- 3ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  rcases (exists_between hxy) with ⟨a, ha⟩,
  exact (lt_irrefl a) (lt_of_lt_of_le ha.2 (h a ha.1)),
end

-- 4ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
begin
  apply le_of_not_gt,
  intro hxy,
  rcases (exists_between hxy) with ⟨a, hya, hax⟩,
  exact (lt_irrefl a) (lt_of_lt_of_le hax (h a hya)),
end

-- 5ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_not_gt (λ hxy,
  let ⟨a, hya, hax⟩ := exists_between hxy in
  lt_irrefl a (lt_of_lt_of_le hax (h a hya)))

-- 6ª demostración
example
  (h : ∀ z, y < z → x ≤ z) :
  x ≤ y :=
le_of_forall_le_of_dense h
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Propiedad_de_la_densidad_de_los_reales.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
???
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
