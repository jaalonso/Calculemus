---
Título: Si f es continua en a y el límite de u(n) es a, entonces el límite de f(u(n)) es f(a)
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

Demostrar que si f es continua en a y el límite de uₙ es a, entonces el límite de f(uₙ) es f(a).

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

-- 1ª demostración
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

-- 2ª demostración
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

-- 3ª demostración
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

Se puede interactuar con la prueba anterior en <a href="https://leanprover-community.github.io/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/CS_de_continuidad.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory CS_de_continuidad
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool" where
  "limite u c ⟷ (∀ε>0. ∃k. ∀n≥k. ¦u n - c¦ ≤ ε)"

definition continua_en_punto :: "(real ⇒ real) ⇒ real ⇒ bool" where
  "continua_en_punto f a ⟷
   (∀ε>0. ∃δ>0. ∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"

(* 1ª demostración *)
lemma
  assumes "continua_en_punto f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_punto_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def hδ1 by auto
  have "∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
  proof (intro allI impI)
    fix n
    assume "n ≥ k"
    then have "¦u n - a¦ ≤ δ"
      using hk by auto
    then show "¦(f ∘ u) n - f a¦ ≤ ε"
      using hδ2 by simp
  qed
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    by auto
qed

(* 2ª demostración *)
lemma
  assumes "continua_en_punto f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_punto_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def hδ1 by auto
  have "∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hk hδ2 by simp
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    by auto
qed

(* 3ª demostración *)
lemma
  assumes "continua_en_punto f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where hδ1 : "δ > 0" and
                      hδ2 :" (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_punto_def by auto
  obtain k where hk : "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def hδ1 by auto
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hk hδ2 by auto
qed

(* 4ª demostración *)
lemma
  assumes "continua_en_punto f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
proof (unfold limite_def; intro allI impI)
  fix ε :: real
  assume "0 < ε"
  then obtain δ where
              hδ : "δ > 0 ∧ (∀x. ¦x - a¦ ≤ δ ⟶ ¦f x - f a¦ ≤ ε)"
    using assms(1) continua_en_punto_def by auto
  then obtain k where "∀n≥k. ¦u n - a¦ ≤ δ"
    using assms(2) limite_def by auto
  then show "∃k. ∀n≥k. ¦(f ∘ u) n - f a¦ ≤ ε"
    using hδ by auto
qed

(* 5ª demostración *)
lemma
  assumes "continua_en_punto f a"
          "limite u a"
  shows "limite (f ∘ u) (f a)"
  using assms continua_en_punto_def limite_def
  by force

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
