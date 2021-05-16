theory Persona_rica_con_abuelo_rico
imports Main
begin

text \<open>--------------------------------------------------------------- 
  Ejercicio 12. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Toda persona pobre tiene un padre rico. Por tanto, existe una
     persona rica que tiene un abuelo rico.
  Usar R(x) para x es rico
       p(x) para el padre de x
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_12a:
  assumes "\<forall>x. \<not>R(x) \<longrightarrow> R(p(x))"
  shows   "\<exists>x. R(x) \<and> R(p(p(x)))"
  using assms
  by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_12b:
  assumes "\<forall>x. \<not>R(x) \<longrightarrow> R(p(x))"
  shows   "\<exists>x. R(x) \<and> R(p(p(x)))"
proof -
  have "\<exists>x. R(x)"
  proof (rule ccontr)
    assume "\<not>(\<exists>x. R(x))"
    then have "\<forall>x. \<not>R(x)" by (rule Meson.not_exD)
    then have "\<not>R(a)" ..
    have "\<not>R(a) \<longrightarrow> R(p(a))" using assms ..
    then have "R(p(a))" using \<open>\<not>R(a)\<close> ..
    then have "\<exists>x. R(x)" ..
    with \<open>\<not>(\<exists>x. R(x))\<close> show False ..
  qed
  then obtain a where "R(a)" ..
  have "\<not>R(p(p(a))) \<or> R(p(p(a)))" by (rule excluded_middle)
  then show "\<exists>x. R(x) \<and> R(p(p(x)))"
  proof
    assume "\<not>R(p(p(a)))"
    have "R(p(a)) \<and> R(p(p(p(a))))"
    proof
      show "R(p(a))"
      proof (rule ccontr)
        assume "\<not>R(p(a))"
        have "\<not>R(p(a)) \<longrightarrow> R(p(p(a)))" using assms ..
        then have "R(p(p(a)))" using \<open>\<not>R(p(a))\<close> ..
        with \<open>\<not>R(p(p(a)))\<close> show False ..
      qed
    next
      show "R(p(p(p(a))))"
      proof -
        have "\<not>R(p(p(a))) \<longrightarrow> R(p(p(p(a))))" using assms ..
        then show "R(p(p(p(a))))" using \<open>\<not>R(p(p(a)))\<close> .. 
      qed
    qed
    then show "\<exists>x. R(x) \<and> R(p(p(x)))" ..
  next
    assume "R(p(p(a)))"
    with \<open>R(a)\<close> have "R(a) \<and> R(p(p(a)))" ..
    then show "\<exists>x. R(x) \<and> R(p(p(x)))" ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_12c:
  assumes "\<forall>x. \<not>R(x) \<longrightarrow> R(p(x))"
  shows   "\<exists>x. R(x) \<and> R(p(p(x)))"
proof -
  have "\<exists>x. R(x)"
  proof (rule ccontr)
    assume "\<not>(\<exists>x. R(x))"
    then have "\<forall>x. \<not>R(x)" by (rule no_ex)
    then have "\<not>R(a)" by (rule allE)
    have "\<not>R(a) \<longrightarrow> R(p(a))" using assms by (rule allE)
    then have "R(p(a))" using \<open>\<not>R(a)\<close> by (rule mp)
    then have "\<exists>x. R(x)" by (rule exI)
    with \<open>\<not>(\<exists>x. R(x))\<close> show False by (rule notE)
  qed
  then obtain a where "R(a)" by (rule exE)
  have "\<not>R(p(p(a))) \<or> R(p(p(a)))" by (rule excluded_middle)
  then show "\<exists>x. R(x) \<and> R(p(p(x)))"
  proof (rule disjE)
    assume "\<not>R(p(p(a)))"
    have "R(p(a)) \<and> R(p(p(p(a))))"
    proof (rule conjI)
      show "R(p(a))"
      proof (rule ccontr)
        assume "\<not>R(p(a))"
        have "\<not>R(p(a)) \<longrightarrow> R(p(p(a)))" using assms by (rule allE)
        then have "R(p(p(a)))" using \<open>\<not>R(p(a))\<close> by (rule mp)
        with \<open>\<not>R(p(p(a)))\<close> show False by (rule notE)
      qed
    next
      show "R(p(p(p(a))))"
      proof -
        have "\<not>R(p(p(a))) \<longrightarrow> R(p(p(p(a))))" using assms by (rule allE)
        then show "R(p(p(p(a))))" using \<open>\<not>R(p(p(a)))\<close> by (rule mp)
      qed
    qed
    then show "\<exists>x. R(x) \<and> R(p(p(x)))" by (rule exI)
  next
    assume "R(p(p(a)))"
    with \<open>R(a)\<close> have "R(a) \<and> R(p(p(a)))" by (rule conjI)
    then show "\<exists>x. R(x) \<and> R(p(p(x)))" by (rule exI)
  qed
qed

end
