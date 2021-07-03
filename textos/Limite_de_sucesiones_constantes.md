---
Título: Límite de sucesiones constantes
Autor:  José A. Alonso
---

En Lean, una sucesión u₀, u₁, u₂, ... se puede representar mediante una función (u : ℕ → ℝ) de forma que u(n) es uₙ.

Se define que a es el límite de la sucesión u, por
<pre lang="text">
   def limite : (ℕ → ℝ) → ℝ → Prop :=
   λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε
</pre>
donde se usa la notación |x| para el valor absoluto de x
<pre lang="text">
   notation `|`x`|` := abs x
</pre>

Demostrar que el límite de la sucesión constante c es c.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic

variable (u : ℕ → ℝ)
variable (c : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε

example :
  limite (λ n, c) c :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic

variable (u : ℕ → ℝ)
variable (c : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u a, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - a| < ε

-- 1ª demostración
-- ===============

example :
  limite (λ n, c) c :=
begin
  unfold limite,
  intros ε hε,
  use 0,
  intros n hn,
  dsimp,
  simp,
  exact hε,
end

-- 2ª demostración
-- ===============

example :
  limite (λ n, c) c :=
begin
  intros ε hε,
  use 0,
  rintro n -,
  norm_num,
  assumption,
end

-- 3ª demostración
-- ===============

example :
  limite (λ n, c) c :=
begin
  intros ε hε,
  use 0,
  intros n hn,
  calc |(λ n, c) n - c|
       = |c - c|  : rfl
   ... = 0        : by simp
   ... < ε        : hε
end

-- 4ª demostración
-- ===============

example :
  limite (λ n, c) c :=
begin
  intros ε hε,
  by finish,
end

-- 5ª demostración
-- ===============

example :
  limite (λ n, c) c :=
λ ε hε, by finish

-- 6ª demostración
-- ===============

example :
  limite (λ n, c) c :=
assume ε,
assume hε : ε > 0,
exists.intro 0
  ( assume n,
    assume hn : n ≥ 0,
    show |(λ n, c) n - c| < ε, from
      calc |(λ n, c) n - c|
           = |c - c|  : rfl
       ... = 0        : by simp
       ... < ε        : hε)
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/Limite_de_sucesiones_constantes.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
