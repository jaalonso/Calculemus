---
Título: Pruebas de "Si f es continua en a y el límite de u es a, entonces el límite de (f ∘ u) es f(a)"
Autor:  José A. Alonso
---

En Lean, se puede definir que a es el límite de la sucesión u por
<pre lang="text">
   def limite (u : ℕ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| < ε
</pre>
y que f es continua en a por
<pre lang="text">
   def continua_en_punto (f : ℝ → ℝ) (a : ℝ) :=
     ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε
</pre>

Demostrar que si f es continua en a y el límite de u es a, entonces el límite de (f ∘ u) es f(a).

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continua_en_punto (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variable {f : ℝ → ℝ}
variable {a : ℝ}
variable {u : ℕ → ℝ}

notation `|`x`|` := abs x

def limite (u : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ k, ∀ n ≥ k, |u n - a| ≤ ε

def continua_en_punto (f : ℝ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| ≤ δ → |f x - f a| ≤ ε

-- ?ª demostración
example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
begin
  intros ε hε,
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩,
  cases hu δ hδ1 with k hk,
  use k,
  intros n hn,
  apply hδ2,
  exact hk n hn,
end

-- ?ª demostración
example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
begin
  intros ε hε,
  rcases hf ε hε with ⟨δ, hδ1, hδ2⟩,
  cases hu δ hδ1 with k hk,
  exact ⟨k, λ n hn, hδ2 (u n) (hk n hn)⟩,
end

-- ?ª demostración
example
  (hf : continua_en_punto f a)
  (hu : limite u a)
  : limite (f ∘ u) (f a) :=
begin
  intros ε hε,
  obtain ⟨δ, hδ1, hδ2⟩ := hf ε hε,
  obtain ⟨k, hk⟩ := hu δ hδ1,
  exact ⟨k, λ n hn, hδ2 (u n) (hk n hn)⟩,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Pruebas_de_"Si_f_es_continua_en_a_y_el_limite_de_u_es_a_entonces_el_límite_de_(f_._u)_es_f(a)".lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
