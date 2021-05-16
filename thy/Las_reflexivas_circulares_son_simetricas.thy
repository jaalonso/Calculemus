theory Las_reflexivas_circulares_son_simetricas
imports Main
begin

text \<open>------------------------------------------------------------------ 
  Ejercicio 5: Demostrar que si R es una relación reflexiva y circular, 
  entonces R es una relacin de equivalencia. 
  { \<forall>x.R(x, x), \<forall>x. \<forall>y. \<forall>z.(R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)) } \<turnstile> 
  (\<forall>x. \<forall>y. (R(x, y) \<longrightarrow> R(y, x))) \<and>(\<forall>x. \<forall>y. \<forall>z.(R(x, y) \<and> R(y, z) \<longrightarrow> R(x, z)))
  --------------------------------------------------------------------\<close>

(* 1\<ordfeminine> demostración: automática *)
lemma 
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)" 
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
  using assms
  by blast

(* 2\<ordfeminine> demostración: estructurada *)
lemma
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)" 
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)+
  fix a b
  show "R (a, b) \<longrightarrow> R (b, a)"
  proof (rule impI)
    assume "R(a, b)"
    have "R(b, b)" 
      using assms(1) by (rule allE)
    with `R(a, b)` have "R(a, b) \<and> R(b, b)" 
      by (rule conjI)
    have  "\<forall>y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)" 
      using assms(2) by (rule allE)
    then have "\<forall>z. R(a, b) \<and> R(b, z) \<longrightarrow>R(z, a)" 
      by (rule allE)
    then have "R(a, b) \<and> R(b, b) \<longrightarrow>R(b, a)" 
      by (rule allE)
    then show "R(b, a)" using `R(a, b) \<and> R(b, b)` 
      by (rule mp)
  qed
qed

(* 3\<ordmasculine> demostración: detallada *)
lemma
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)" 
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)+
  fix a b
  show "R (a, b) \<longrightarrow> R (b, a)"
  proof (rule impI)
    assume "R(a , b)"
    have "R(b, b)" using assms(1) ..
    with `R(a, b)` have "R(a, b) \<and> R(b, b)" ..
    have  "\<forall>y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)" using assms(2) ..
    then have "\<forall>z. R(a, b) \<and> R(b, z) \<longrightarrow>R(z, a)" ..
    then have "R(a, b) \<and> R(b, b) \<longrightarrow>R(b, a)" ..
    then show "R(b, a)" using `R(a, b) \<and> R(b, b)` ..
  qed
qed

section \<open>Soluciones de alumnos\<close>

subsection \<open>inmrodmon\<close>

lemma 
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)" 
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)
  fix a 
  have 1: "R(a, a)" 
    using assms(1) by (rule allE)
  show "\<forall>y. R (a, y) \<longrightarrow> R (y, a)"
  proof (rule allI) 
    fix b 
    have "\<forall> y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)" 
      using assms(2) by (rule allE)
    then have "\<forall> z. R(a, a) \<and> R(a, z) \<longrightarrow> R(z, a)" 
      by (rule allE) 
    then have 3: "R(a, a) \<and> R(a, b) \<longrightarrow> R(b, a)" 
      by (rule allE) 
    show " R (a, b) \<longrightarrow> R (b, a)"
    proof (rule impI) 
      assume 2: "R(a, b)" 
      have "R(a, a) \<and> R(a, b)" 
        using 1 2 by (rule conjI) 
      with 3 show "R(b, a)" 
        by (rule mp) 
    qed
  qed
qed 

subsection \<open>inehenluq\<close>

lemma 
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)" 
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)
  fix a
  show "\<forall>y. R(a,y)\<longrightarrow>R(y,a)"
  proof (rule allI)
    fix b
    show "R(a, b) \<longrightarrow> R(b, a)"
    proof (rule impI)
      assume 1: "R(a, b)"
      have "R(a, a)" 
        using assms(1) by (rule allE)
      then have 2: "R(a,a) \<and> R(a,b)" 
        using 1 by (rule conjI)
      have "\<forall>y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)" 
        using assms(2) by (rule allE)
      then have "\<forall>z. R(a, a) \<and> R(a, z) \<longrightarrow> R(z, a)" 
        by (rule allE)
      then have "R(a, a) \<and> R(a, b)\<longrightarrow> R(b, a)" 
        by (rule allE)
      then show "R(b, a)" 
        using 2 by (rule mp)
    qed
  qed
qed

subsection \<open>enrniecar\<close>

lemma 
  assumes "\<forall>x. R(x, x)"
          "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)" 
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (rule allI)
  fix a
  show "\<forall>y. R(a, y) \<longrightarrow> R(y, a)"
  proof (rule allI)
    fix b
    show "R(a, b) \<longrightarrow> R(b, a)"
    proof (rule impI)
      assume "R(a, b)"
      have "\<forall>y z. R(a, y) \<and> R(y, z) \<longrightarrow> R(z, a)" 
        using assms(2) by (rule allE)
      then have "\<forall>z. R(a, b) \<and> R(b, z) \<longrightarrow> R(z, a)" 
        by (rule allE)
      then have "R(a, b) \<and> R(b, b) \<longrightarrow> R(b, a)" 
        by (rule allE)
      have "R(b,b)" 
        using assms(1) by (rule allE)
      with \<open>R(a,b)\<close> have "R(a, b) \<and> R(b, b)" 
        by (rule conjI)
      with \<open>R(a, b) \<and> R(b, b) \<longrightarrow> R(b, a)\<close> show "R(b,a)" 
        by (rule mp)
    qed
  qed
qed

lemma
  "\<lbrakk>\<forall>x. R(x, x);\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)\<rbrakk>\<Longrightarrow>\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
  apply (rule allI)+
  apply (erule allE)+
  apply (rule impI)
  apply (erule mp)
  apply (erule conjI)
  apply assumption
  done

subsection \<open>carruirui3\<close>

lemma
  assumes reflexiva: "\<forall>x. R(x, x)" and
          circular:  "\<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x)"
  shows   "\<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
proof (intro allI)
  fix a b
  show "R(a, b) \<longrightarrow> R(b, a)"
  proof (rule impI)
    assume "R(a, b)"
    have "R(b, b)" 
      using reflexiva by (rule allE)
    with `R(a,b)` have "R(a,b) \<and> R(b,b)" 
      by (rule conjI)
    from circular have "R(a, b) \<and> R(b, b) \<longrightarrow> R(b, a)" 
      by (erule_tac x="a" in allE,
          erule_tac x="b" in allE,
          erule_tac x="b" in allE) 
    then show "R(b,a)" 
      using `R(a,b) \<and> R(b,b)` by (rule mp)
  qed
qed

subsection \<open>antrivmar\<close>

lemma 
  "\<forall>x. R(x, x)
   \<Longrightarrow> \<forall>x y z. R(x, y) \<and> R(y, z) \<longrightarrow> R(z, x) 
   \<Longrightarrow> \<forall>x y. R(x, y) \<longrightarrow> R(y, x)"
  apply(rule allI)+
  apply(erule allE)+
  apply (rule impI)
  apply(erule mp)
  apply(rule conjI)
   apply assumption+
  done

end
