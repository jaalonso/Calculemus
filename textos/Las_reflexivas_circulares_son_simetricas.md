# Las reflexivas circulares son simétricas

Se dice que la relación binaria R es

* reflexiva si ∀x. R(x, x)
* circular si ∀x y z. R(x, y) ∧ R(y, z) ⟶ R(z, x)
* simétrica si ∀x y. R(x, y) ⟶ R(y, x)

Demostrar que las relaciones reflexivas y circulares son simétricas. Para ello, completar la siguiente teoría de Isabelle/HOL:

<pre lang="isar">
theory Las_reflexivas_circulares_son_simetricas
imports Main
begin

lemma 
  assumes "∀x. R(x, x)"
          "∀x y z. R(x, y) ∧ R(y, z) ⟶ R(z, x)" 
  shows   "∀x y. R(x, y) ⟶ R(y, x)"
  oops
  
end
</pre>

<h4>Soluciones</h4>

Puedes escribir tus soluciones en los comentarios (con el código entre una línea con &#60;pre lang=&quot;isar&quot;&#62; y otra con &#60;/pre&#62;) o ver las soluciones propuestas pulsando [expand title="aquí"]

<h4>Soluciones con Isabelle/HOL</h4>

<pre lang="isar">
theory Las_reflexivas_circulares_son_simetricas
imports Main
begin

(* 1ª demostración: automática *)
lemma 
  assumes "∀x. R(x, x)"
          "∀x y z. R(x, y) ∧ R(y, z) ⟶ R(z, x)" 
  shows   "∀x y. R(x, y) ⟶ R(y, x)"
  using assms
  by blast

(* 2ª demostración: estructurada *)
lemma
  assumes "∀x. R(x, x)"
          "∀x y z. R(x, y) ∧ R(y, z) ⟶ R(z, x)" 
  shows   "∀x y. R(x, y) ⟶ R(y, x)"
proof (rule allI)+
  fix a b
  show "R (a, b) ⟶ R (b, a)"
  proof (rule impI)
    assume "R(a, b)"
    have "R(b, b)" 
      using assms(1) by (rule allE)
    with `R(a, b)` have "R(a, b) ∧ R(b, b)" 
      by (rule conjI)
    have  "∀y z. R(a, y) ∧ R(y, z) ⟶ R(z, a)" 
      using assms(2) by (rule allE)
    then have "∀z. R(a, b) ∧ R(b, z) ⟶R(z, a)" 
      by (rule allE)
    then have "R(a, b) ∧ R(b, b) ⟶R(b, a)" 
      by (rule allE)
    then show "R(b, a)" using `R(a, b) ∧ R(b, b)` 
      by (rule mp)
  qed
qed

(* 3º demostración: detallada *)
lemma
  assumes "∀x. R(x, x)"
          "∀x y z. R(x, y) ∧ R(y, z) ⟶ R(z, x)" 
  shows   "∀x y. R(x, y) ⟶ R(y, x)"
proof (rule allI)+
  fix a b
  show "R (a, b) ⟶ R (b, a)"
  proof (rule impI)
    assume "R(a , b)"
    have "R(b, b)" using assms(1) ..
    with `R(a, b)` have "R(a, b) ∧ R(b, b)" ..
    have  "∀y z. R(a, y) ∧ R(y, z) ⟶ R(z, a)" using assms(2) ..
    then have "∀z. R(a, b) ∧ R(b, z) ⟶R(z, a)" ..
    then have "R(a, b) ∧ R(b, b) ⟶R(b, a)" ..
    then show "R(b, a)" using `R(a, b) ∧ R(b, b)` ..
  qed
qed

end
</pre>
[/expand]
