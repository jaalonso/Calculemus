theory El_problema_del_barbero
imports Main
begin

text \<open>--------------------------------------------------------------- 
  Ejercicio 20. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Carlos afeita a todos los habitantes de Las Chinas que no se
     afeitan a sí mismo y sólo a ellos. Carlos es un habitante de las
     Chinas. Por consiguiente, Carlos no afeita a nadie.
  Usar A(x,y) para x afeita a y
       C(x)   para x es un habitante de Las Chinas
       c      para Carlos
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
  using assms
  by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
proof -
  have 1: "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" using assms(1) ..
  have "A(c,c)"
  proof (rule ccontr)
    assume "\<not>A(c,c)"
    with assms(2) have "C(c) \<and> \<not>A(c,c)" ..
    with 1 have "A(c,c)" .. 
    with \<open>\<not>A(c,c)\<close> show False ..
  qed
  have "\<not>A(c,c)"
  proof -
    have "C(c) \<and> \<not>A(c,c)" using 1 \<open>A(c,c)\<close> ..
    then show "\<not>A(c,c)" ..
  qed
  then show "\<not>(\<exists>x. A(c,x))" using \<open>A(c,c)\<close> ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma 
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
proof -
  have 1: "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" using assms(1) by (rule allE)
  have "A(c,c)"
  proof (rule ccontr)
    assume "\<not>A(c,c)"
    with assms(2) have "C(c) \<and> \<not>A(c,c)" by (rule conjI)
    with 1 have "A(c,c)" by (rule iffD2)
    with \<open>\<not>A(c,c)\<close> show False by (rule notE)
  qed
  have "\<not>A(c,c)"
  proof -
    have "C(c) \<and> \<not>A(c,c)" using 1 \<open>A(c,c)\<close> by (rule iffD1)
    then show "\<not>A(c,c)" by (rule conjunct2)
  qed
  then show "\<not>(\<exists>x. A(c,x))" using \<open>A(c,c)\<close> by (rule notE)
qed

section \<open>Soluciones de alumnos\<close>

subsection \<open>inmrodmon\<close>

lemma 
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> (C(x) \<and> \<not>A(x,x))"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
  using assms by auto 

subsection \<open>enrniecar\<close>

lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
proof - 
  have "\<not>A(c,c) \<or> A(c,c)" by (rule excluded_middle)
  then show "\<not>(\<exists>x. A(c,x))"
  proof (rule disjE)
    assume "\<not>A(c,c)"
    have "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" using assms(1) by (rule allE)
    have "C(c) \<and> \<not>A(c,c)" using assms(2) \<open>\<not>A(c,c)\<close> by (rule conjI)
    with \<open>A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)\<close> have "A(c,c)" by (rule iffD2)
    with \<open>\<not>A(c,c)\<close> have False by (rule notE)
    then show "\<not>(\<exists>x. A(c,x))" by (rule FalseE)
  next 
    assume "A(c,c)"
    have "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" using assms(1) by (rule allE)
    then have "C(c) \<and> \<not>A(c,c)" using \<open>A(c,c)\<close> by (rule iffD1)
    then have "\<not>A(c,c)" by (rule conjunct2)
    then have False using \<open>A(c,c)\<close> by (rule notE)
    then show "\<not>(\<exists>x. A(c,x))" by (rule FalseE)
  qed
qed

subsection \<open>inehenluq\<close>

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
  by auto

lemma aux:
  assumes "p"
  shows "\<not>(q \<and> \<not>p)"
proof (rule notI)
  assume "q\<and> \<not>p"
  then have "\<not>p" 
    by (rule conjunct2)
  then show False 
    using assms by (rule notE)
qed

lemma
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
proof (rule notI)
  assume  "\<exists>x. A(c,x)"
  have "\<not>A(c,c) \<or> A(c,c)" 
    by (rule excluded_middle)
  then show False
  proof (rule disjE)
    assume 1: "\<not>A(c,c)"
    with assms(2) have 2: "C(c) \<and> \<not>A(c,c)" 
      by (rule conjI)
    have "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" 
      using assms(1) by (rule allE)
    then have " C(c) \<and> \<not>A(c,c)\<longrightarrow>A(c,c)" 
      by (rule iffE)
    then have "A(c,c)" 
      using 2 by (rule mp)
    with 1 show False 
      by (rule notE)
  next
    assume 3:"A(c,c)"
    then have 4: "\<not>(C(c) \<and> \<not>A(c,c))" 
      by (rule aux)
    have "A(c,c) \<longleftrightarrow> C(c) \<and> \<not>A(c,c)" 
      using assms(1) by (rule allE)
    then have "A(c,c) \<longrightarrow> C(c) \<and> \<not>A(c,c)"  
      by (rule iffE)
    then have "\<not> A(c,c)" 
      using 4 by (rule mt)
    then show False 
      using 3 by (rule notE)
  qed
qed


end
