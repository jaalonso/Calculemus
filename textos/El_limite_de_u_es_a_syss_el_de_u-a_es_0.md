---
Título: El límite de u(n) es a syss el de u(n)-a es 0
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

Demostrar que que el límite de u(n) es a si y solo si el de u(n)-a es 0.

Para ello, completar la siguiente teoría de Lean:

<pre lang="lean">
import data.real.basic
import tactic

variable  {u : ℕ → ℝ}
variables {a c x : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

example
  : limite u a ↔ limite (λ i, u i - a) 0 :=
sorry
</pre>

[expand title="Soluciones con Lean"]

<pre lang="lean">
import data.real.basic
import tactic

variable  {u : ℕ → ℝ}
variables {a c x : ℝ}

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| < ε

-- 1ª demostración
-- ===============

example
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  split,
  { intros h ε hε,
    convert h ε hε,
    norm_num, },
  { intros h ε hε,
    convert h ε hε,
    norm_num, },
end

-- 2ª demostración
-- ===============

example
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  split;
  { intros h ε hε,
    convert h ε hε,
    norm_num, },
end

-- 3ª demostración
-- ===============

lemma limite_con_suma
  (c : ℝ)
  (h : limite u a)
  : limite (λ i, u i + c) (a + c) :=
λ ε hε, (by convert h ε hε; norm_num)

lemma CNS_limite_con_suma
  (c : ℝ)
  : limite u a ↔ limite (λ i, u i + c) (a + c) :=
begin
  split,
  { apply limite_con_suma },
  { intro h,
    convert limite_con_suma (-c) h; simp, },
end

example
  (u : ℕ → ℝ)
  (a : ℝ)
  : limite u a ↔ limite (λ i, u i - a) 0 :=
begin
  convert CNS_limite_con_suma (-a),
  simp,
end
</pre>

Se puede interactuar con la prueba anterior en <a href="https://www.cs.us.es/~jalonso/lean-web-editor/#url=https://raw.githubusercontent.com/jaalonso/Calculemus/main/src/El_limite_de_u_es_a_syss_el_de_u-a_es_0.lean" rel="noopener noreferrer" target="_blank">esta sesión con Lean</a>.

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;lean&quot;&#62; y otra con &#60;/pre&#62;
[/expand]

[expand title="Soluciones con Isabelle/HOL"]

<pre lang="isar">
theory "El_limite_de_u_es_a_syss_el_de_u-a_es_0"
imports Main HOL.Real
begin

definition limite :: "(nat ⇒ real) ⇒ real ⇒ bool"
  where "limite u c ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - c¦ < ε)"

(* 1ª demostración *)

lemma
  "limite u a ⟷ limite (λ i. u i - a) 0"
proof -
  have "limite u a ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - a¦ < ε)"
    by (rule limite_def)
  also have "… ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦(u n - a) - 0¦ < ε)"
    by simp
  also have "… ⟷ limite (λ i. u i - a) 0"
    by (rule limite_def[symmetric])
  finally show "limite u a ⟷ limite (λ i. u i - a) 0"
    by this
qed

(* 2ª demostración *)

lemma
  "limite u a ⟷ limite (λ i. u i - a) 0"
proof -
  have "limite u a ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦u n - a¦ < ε)"
    by (simp only: limite_def)
  also have "… ⟷ (∀ε>0. ∃k::nat. ∀n≥k. ¦(u n - a) - 0¦ < ε)"
    by simp
  also have "… ⟷ limite (λ i. u i - a) 0"
    by (simp only: limite_def)
  finally show "limite u a ⟷ limite (λ i. u i - a) 0"
    by this
qed

(* 3ª demostración *)

lemma
  "limite u a ⟷ limite (λ i. u i - a) 0"
  using limite_def
  by simp

end
</pre>

En los comentarios se pueden escribir otras soluciones, escribiendo el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;
[/expand]
