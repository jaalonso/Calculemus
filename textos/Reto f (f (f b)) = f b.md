% Reto f (f (f b)) = f b 

El problema de hoy está basado en el reto [Daily Challenge #168](https://dev.to/thepracticaldev/daily-challenge-168-code-golf-f-f-f-b-f-b-1nd9) que se planteó ayer. El reto consiste en demostrar que si `f` es una función de los booleanos en los booleanos, entonces para todo `b` se verifica que `f (f (f b)) = f b`.

Concretamente, el reto consiste en completar la siguiente demostración 

<pre lang="isar">
lemma 
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  sorry
</pre>

<h4>Soluciones</h4>

Puedes escribir tus soluciones en los comentarios (con el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;) o ver las soluciones propuestas pulsando [expand title="aquí"]

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory reto

imports Main
begin

(* 1ª solución *)

lemma "∀(f :: bool ⇒ bool). f (f (f b)) = f b"
  by smt

(* 2ª solución *)

lemma 
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  by smt

(* 3ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  by (cases b; cases "f True"; cases "f False"; simp)

(* 4ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
proof (cases "f True"; cases "f False"; cases b)
  assume "f True" "f False" "b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹f True› by simp 
next
  assume "f True" "f False" "¬ b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹f True› ‹f False› ‹¬ b› by simp 
next
  assume "f True" "¬ f False" "b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹f True› ‹¬ f False› ‹b› by simp 
next
  assume "f True" "¬ f False" "¬ b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹f True› ‹¬ f False› ‹¬ b› by simp 
next 
  assume "¬ f True" "f False" "b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹f False› ‹b› by simp 
next
  assume "¬ f True" "f False" "¬ b"
  then have "f b = True" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹f False› ‹¬ b› by simp 
next
  assume "¬ f True" "¬ f False" "b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹¬ f False› ‹b› by simp 
next
  assume "¬ f True" "¬ f False" "¬ b"
  then have "f b = False" by simp
  then show "f (f (f b)) = f b" using ‹¬ f True› ‹¬ f False› ‹¬b› by simp 
qed

(* 5ª solución *)

lemma
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
proof (cases "f True"; cases "f False"; cases b)
  assume "f True" "f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f True)" using ‹f True› by simp
  also have "… = f True" using ‹f True› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "f True" "f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f True)" using ‹f False› by simp
  also have "… = f True" using ‹f True› by simp
  also have "… = f False" using ‹f True› ‹f False› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "f True" "¬ f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f True)" using ‹f True› by simp
  also have "… = f True" using ‹f True› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "f True" "¬ f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f False)" using ‹¬ f False› by simp
  also have "… = f False" using ‹¬ f False› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this 
next 
  assume "¬ f True" "f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f False)" using ‹¬ f True› by simp
  also have "… = f True" using ‹f False› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "¬ f True" "f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f True)" using ‹f False› by simp
  also have "… = f False" using ‹¬ f True› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "¬ f True" "¬ f False" "b"
  have "f (f (f b)) = f (f (f True))" using ‹b› by simp
  also have "… = f (f False)" using ‹¬ f True› by simp
  also have "… = f False" using ‹¬ f False› by simp
  also have "… = False" using ‹¬ f False› by simp
  also have "… = f True" using ‹¬ f True› by simp
  also have "… = f b" using ‹b› by simp
  finally show "f (f (f b)) = f b" by this 
next
  assume "¬ f True" "¬ f False" "¬ b"
  have "f (f (f b)) = f (f (f False))" using ‹¬b› by simp
  also have "… = f (f False)" using ‹¬ f False› by simp
  also have "… = f False" using ‹¬ f False› by simp
  also have "… = f b" using ‹¬ b› by simp
  finally show "f (f (f b)) = f b" by this 
qed

(* 6ª solución *)

theorem
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b" 
proof (cases b)
  assume b: b
  show ?thesis
  proof (cases "f True")
    assume ft: "f True"
    show ?thesis
      using b ft by auto
  next
    assume ft: "¬ f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "¬ f False"
      show ?thesis
        using b ft ff by auto
    qed
  qed
next
  assume b: "¬ b"
  show ?thesis
  proof (cases "f True")
    assume ft: "f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "¬ f False"
      show ?thesis
        using b ft ff by auto
    qed
  next
    assume ft: "¬ f True"
    show ?thesis
    proof (cases "f False")
      assume ff: "f False"
      show ?thesis
        using b ft ff by auto
    next
      assume ff: "¬ f False"
      show ?thesis
        using b ft ff by auto
    qed
  qed
qed

(* 7ª solución *)

theorem
  fixes f :: "bool ⇒ bool"
  shows "f (f (f b)) = f b"
  by (cases b "f True" "f False"
      rule: bool.exhaust [ case_product bool.exhaust
                         , case_product bool.exhaust])
    auto

end
</pre>
[/expand]




