section \<open>T4R3: Argumentación en lógica de primer orden con igualdad\<close>

theory T4R3
imports Main 
begin

text \<open>
  --------------------------------------------------------------------- 
  El objetivo de esta relación es formalizar y decidir la corrección
  de los argumentos. En el caso de que sea correcto, demostrarlo usando
  sólo las reglas básicas de deducción natural de la lógica de primer
  orden (sin usar el método auto). En el caso de que sea incorrecto,
  calcular un contraejemplo con QuickCheck. 

  Las reglas básicas de la deducción natural son las siguientes:
  · conjI:      \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> P \<and> Q
  · conjunct1:  P \<and> Q \<Longrightarrow> P
  · conjunct2:  P \<and> Q \<Longrightarrow> Q  
  · notnotD:    \<not>\<not> P \<Longrightarrow> P
  · notnotI:    P \<Longrightarrow> \<not>\<not> P
  · mp:         \<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q 
  · mt:         \<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F 
  · impI:       (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q
  · disjI1:     P \<Longrightarrow> P \<or> Q
  · disjI2:     Q \<Longrightarrow> P \<or> Q
  · disjE:      \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R 
  · FalseE:     False \<Longrightarrow> P
  · notE:       \<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> R
  · notI:       (P \<Longrightarrow> False) \<Longrightarrow> \<not>P
  · iffI:       \<lbrakk>P \<Longrightarrow> Q; Q \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P = Q
  · iffD1:      \<lbrakk>Q = P; Q\<rbrakk> \<Longrightarrow> P 
  · iffD2:      \<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P
  · ccontr:     (\<not>P \<Longrightarrow> False) \<Longrightarrow> P
  · excluded_middle: \<not>P \<or> P

  · allI:       \<lbrakk>\<forall>x. P x; P x \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R
  · allE:       (\<And>x. P x) \<Longrightarrow> \<forall>x. P x
  · exI:        P x \<Longrightarrow> \<exists>x. P x
  · exE:        \<lbrakk>\<exists>x. P x; \<And>x. P x \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q

  · refl:       t = t
  · subst:      \<lbrakk>s = t; P s\<rbrakk> \<Longrightarrow> P t

  · trans:      \<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t
  · sym:        s = t \<Longrightarrow> t = s
  · not_sym:    t \<noteq> s \<Longrightarrow> s \<noteq> t
  · ssubst:     \<lbrakk>t = s; P s\<rbrakk> \<Longrightarrow> P t
  · box_equals: \<lbrakk>a = b; a = c; b = d\<rbrakk> \<Longrightarrow> a: = d
  · arg_cong:   x = y \<Longrightarrow> f x = f y
  · fun_cong:   f = g \<Longrightarrow> f x = g x
  · cong:       \<lbrakk>f = g; x = y\<rbrakk> \<Longrightarrow> f x = g y
  --------------------------------------------------------------------- 
\<close>

text \<open>
  Se usarán, además, siquientes reglas que demostramos a continuación.
\<close>

text \<open>--------------------------------------------------------------- 
  Ejercicio 1. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Rosa ama a Curro. Paco no simpatiza con Ana. Quien no simpatiza con
     Ana ama a Rosa. Si una persona ama a otra, la segunda ama a la
     primera. Hay como máximo una persona que ama a Rosa. Por tanto,
     Paco es Curro. 
  Usar A(x,y) para x ama a y 
       S(x,y) para x simpatiza con y 
       a      para Ana
       c      para Curro
       p      para Paco 
       r      para Rosa
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_1a:
  assumes "A(r,c)" 
          "\<not>S(p,a)"
          "\<forall>x. \<not>S(x,a) \<longrightarrow> A(x,r)"
          "\<forall>x y. A(x,y) \<longrightarrow> A(y,x)"
          "\<forall>x y. A(x,r) \<and> A(y,r) \<longrightarrow> x=y"
  shows   "p = c"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_1b:
  assumes 1: "A(r,c)" and 
          2: "\<not>S(p,a)" and
          3: "\<forall>x. \<not>S(x,a) \<longrightarrow> A(x,r)" and
          4: "\<forall>x y. A(x,y) \<longrightarrow> A(y,x)" and
          5: "\<forall>x y. A(x,r) \<and> A(y,r) \<longrightarrow> x=y"
  shows   "p = c"
proof -
  have "\<forall> y. A(p,r) \<and> A(y,r) \<longrightarrow> p=y" using 5 ..
  then have "A(p,r) \<and> A(c,r) \<longrightarrow> p=c" ..
  moreover
  have "A(p,r) \<and> A(c,r)"
  proof
    have "\<not>S(p,a) \<longrightarrow> A(p,r)" using 3 ..
    then show "A(p,r)" using 2 ..
  next
    have "\<forall>y. A(r,y) \<longrightarrow> A(y,r)" using 4 ..
    then have "A(r,c) \<longrightarrow> A(c,r)" ..
    then show "A(c,r)" using 1 ..
  qed
  ultimately show "p=c" ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_1c:
  assumes 1: "A(r,c)" and 
          2: "\<not>S(p,a)" and
          3: "\<forall>x. \<not>S(x,a) \<longrightarrow> A(x,r)" and
          4: "\<forall>x y. A(x,y) \<longrightarrow> A(y,x)" and
          5: "\<forall>x y. A(x,r) \<and> A(y,r) \<longrightarrow> x=y"
  shows   "p = c"
proof -
  have "\<forall> y. A(p,r) \<and> A(y,r) \<longrightarrow> p=y" using 5 by (rule allE)
  then have "A(p,r) \<and> A(c,r) \<longrightarrow> p=c" by (rule allE)
  moreover
  have "A(p,r) \<and> A(c,r)"
  proof (rule conjI)
    have "\<not>S(p,a) \<longrightarrow> A(p,r)" using 3 by (rule allE)
    then show "A(p,r)" using 2 by (rule mp)
  next
    have "\<forall>y. A(r,y) \<longrightarrow> A(y,r)" using 4 by (rule allE)
    then have "A(r,c) \<longrightarrow> A(c,r)" by (rule allE)
    then show "A(c,r)" using 1 by (rule mp)
  qed
  ultimately show "p=c" by (rule mp)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 2. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Sólo hay un sofista que enseña gratuitamente, y éste es
     Sócrates. Sócrates argumenta mejor que ningún otro sofista. Platón
     argumenta mejor que algún sofista que enseña gratuitamente. Si una
     persona argumenta mejor que otra segunda, entonces la segunda no
     argumenta mejor que la primera. Por consiguiente, Platón no es un
     sofista. 
  Usar G(x)   para x enseña gratuitamente
       M(x,y) para x argumenta mejor que y
       S(x)   para x es un sofista
       p      para Platón
       s      para Sócrates
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_2a:
  assumes 1: "\<exists>y. (\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x=y) \<and> y=s" and
          2: "\<forall>x. S(x) \<and> x \<noteq> s \<longrightarrow> M(s,x)" and
          3: "\<exists>x. S(x) \<and> G(x) \<and> M(p,x)"  and
          4: "\<forall>x y. M(x,y) \<longrightarrow> \<not>M(y,x)"
  shows "\<not>S(p)"
using assms
by metis

\<comment> \<open>La demostración semiautomática es\<close>
lemma ejercicio_2b:
  assumes 1: "\<exists>y. (\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = y) \<and> y = s" and
          2: "\<forall>x. S(x) \<and> x \<noteq> s \<longrightarrow> M(s,x)" and
          3: "\<exists>x. S(x) \<and> G(x) \<and> M(p,x)"  and
          4: "\<forall>x y. M(x,y) \<longrightarrow> \<not>M(y,x)"
  shows "\<not>S(p)"
proof
  assume "S(p)"
  obtain a where a: "(\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = a) \<and> a = s" using 1 ..
  then have s: "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = s" by metis 
  obtain b where b: "S(b) \<and> G(b) \<and> M(p,b)" using 3 ..
  then have "b = s" using s by metis
  then have "M(p,s)" using b by metis
  then have "\<not>M(s,p)" using 4 by metis
  then have "p = s" using 2 \<open>S(p)\<close> by metis
  then have "M(s,s)" using \<open>M(p,s)\<close> by auto
  have "\<not>M(s,s)" using \<open>p = s\<close> \<open>\<not>M(s,p)\<close> by auto
  then show False using \<open>M(s,s)\<close> by auto
qed

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_2c:
  assumes 1: "\<exists>y. (\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = y) \<and> y = s" and
          2: "\<forall>x. S(x) \<and> x \<noteq> s \<longrightarrow> M(s,x)" and
          3: "\<exists>x. S(x) \<and> G(x) \<and> M(p,x)"  and
          4: "\<forall>x y. M(x,y) \<longrightarrow> \<not>M(y,x)"
  shows "\<not>S(p)"
proof
  assume "S(p)"
  obtain a where a: "(\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = a) \<and> a = s" using 1 ..
  then have s: "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = s" 
  proof
    have "a = s" using a ..
    have "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = a" using a ..
    with \<open>a = s\<close> show "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = s"  by (rule subst)
  qed
  obtain b where b: "S(b) \<and> G(b) \<and> M(p,b)" using 3 ..
  then have "b = s"
  proof
    have "S(b) \<and> G(b)"
    proof
      show "S(b)" using b ..
    next
      have "G(b) \<and> M(p,b)" using b ..
      then show "G(b)" ..
    qed
    have "S(b) \<and> G(b) \<longleftrightarrow> b = s" using s ..
    then show "b = s" using \<open>S(b) \<and> G(b)\<close> ..
  qed
  have "M(p,s)"
  proof -
    have "G(b) \<and> M(p,b)" using b ..
    then have "M(p,b)" ..
    with \<open>b = s\<close> show "M(p,s)" by (rule subst) 
  qed
  have "\<not>M(s,p)"
  proof -
    have "\<forall>y. M(p,y) \<longrightarrow> \<not>M(y,p)" using 4 ..
    then have "M(p,s) \<longrightarrow> \<not>M(s,p)" ..
    then show "\<not>M(s,p)" using \<open>M(p,s)\<close> ..
  qed
  have "p = s"
  proof (rule ccontr)
    assume "p \<noteq> s"
    with \<open>S(p)\<close> have "S(p) \<and> p \<noteq> s" ..
    have "S(p) \<and> p \<noteq> s \<longrightarrow> M(s,p)" using 2 ..
    then have "M(s,p)" using \<open>S(p) \<and> p \<noteq> s\<close> ..
    with \<open>\<not>M(s,p)\<close> show False ..
  qed
  then have "M(s,s)" using \<open>M(p,s)\<close> by (rule subst)
  have "\<not>M(s,s)" using \<open>p = s\<close> \<open>\<not>M(s,p)\<close> by (rule subst)
  then show False using \<open>M(s,s)\<close> ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_2d:
  assumes 1: "\<exists>y. (\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = y) \<and> y = s" and
          2: "\<forall>x. S(x) \<and> x \<noteq> s \<longrightarrow> M(s,x)" and
          3: "\<exists>x. S(x) \<and> G(x) \<and> M(p,x)"  and
          4: "\<forall>x y. M(x,y) \<longrightarrow> \<not>M(y,x)"
  shows "\<not>S(p)"
proof
  assume "S(p)"
  obtain a where a: "(\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = a) \<and> a = s" using 1 by (rule exE)
  have s: "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = s" 
  proof -
    have "a = s" using a ..
    have "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = a" using a ..
    with \<open>a = s\<close> show "\<forall>x. S(x) \<and> G(x) \<longleftrightarrow> x = s"  by (rule subst)
  qed
  obtain b where b: "S(b) \<and> G(b) \<and> M(p,b)" using 3 ..
  have "b = s"
  proof -
    have "S(b) \<and> G(b)"
    proof (rule conjI)
      show "S(b)" using b by (rule conjunct1)
    next
      have "G(b) \<and> M(p,b)" using b by (rule conjunct2)
      then show "G(b)" by (rule conjunct1)
    qed
    have "S(b) \<and> G(b) \<longleftrightarrow> b = s" using s by (rule allE)
    then show "b = s" using \<open>S(b) \<and> G(b)\<close> by (rule iffD1)
  qed
  have "M(p,s)"
  proof -
    have "G(b) \<and> M(p,b)" using b ..
    then have "M(p,b)" ..
    with \<open>b = s\<close> show "M(p,s)" by (rule subst) 
  qed
  have "\<not>M(s,p)"
  proof -
    have "\<forall>y. M(p,y) \<longrightarrow> \<not>M(y,p)" using 4 ..
    then have "M(p,s) \<longrightarrow> \<not>M(s,p)" ..
    then show "\<not>M(s,p)" using \<open>M(p,s)\<close> ..
  qed
  have "p = s"
  proof (rule ccontr)
    assume "p \<noteq> s"
    with \<open>S(p)\<close> have "S(p) \<and> p \<noteq> s" ..
    have "S(p) \<and> p \<noteq> s \<longrightarrow> M(s,p)" using 2 ..
    then have "M(s,p)" using \<open>S(p) \<and> p \<noteq> s\<close> ..
    with \<open>\<not>M(s,p)\<close> show False ..
  qed
  then have "M(s,s)" using \<open>M(p,s)\<close> by (rule subst)
  have "\<not>M(s,s)" using \<open>p = s\<close> \<open>\<not>M(s,p)\<close> by (rule subst)
  then show False using \<open>M(s,s)\<close> by (rule notE)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 3. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todos los filósofos se han preguntado qué es la filosofía. Los que
     se preguntan qué es la filosofía se vuelven locos. Nietzsche es
     filósofo. El maestro de Nietzsche no acabó loco. Por tanto,
     Nietzsche y su maestro son diferentes personas. 
  Usar F(x) para x es filósofo
       L(x) para x se vuelve loco
       P(x) para x se ha preguntado qué es la filosofía.
       m    para el maestro de Nietzsche
       n    para Nietzsche
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_3a:
  assumes "\<forall>x. F(x) \<longrightarrow> P(x)"
          "\<forall>x. P(x) \<longrightarrow> L(x)"
          "F(n)"
          "\<not>L(m)"
  shows   "n \<noteq> m"
using assms
by auto

\<comment> \<open>En las siguientes demostraciones se usará este lema\<close>
lemma para_todo_implica:
  assumes "\<forall>x. P(x) \<longrightarrow> Q(x)"
          "P(a)"
  shows   "Q(a)"
proof -
  have "P(a) \<longrightarrow> Q(a)" using assms(1) ..
  then show "Q(a)" using assms(2) ..
qed

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_3b:
  assumes "\<forall>x. F(x) \<longrightarrow> P(x)"
          "\<forall>x. P(x) \<longrightarrow> L(x)"
          "F(n)"
          "\<not>L(m)"
  shows   "n \<noteq> m"
proof
  assume "n = m"
  then have "F(m)" using assms(3) by (rule subst)
  with assms(1) have "P(m)" by (rule para_todo_implica)
  with assms(2) have "L(m)" by (rule para_todo_implica)
  with assms(4) show False ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_3c:
  assumes "\<forall>x. F(x) \<longrightarrow> P(x)"
          "\<forall>x. P(x) \<longrightarrow> L(x)"
          "F(n)"
          "\<not>L(m)"
  shows   "n \<noteq> m"
proof (rule notI)
  assume "n = m"
  then have "F(m)" using assms(3) by (rule subst)
  with assms(1) have "P(m)" by (rule para_todo_implica)
  with assms(2) have "L(m)" by (rule para_todo_implica)
  with assms(4) show False by (rule notE)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 4. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Los padres son mayores que los hijos. Juan es el padre de Luis. Por
     tanto, Juan es mayor que Luis.
  Usar M(x,y) para x es mayor que y
       p(x)   para el padre de x
       j      para Juan
       l      para Luis
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_4a:
  assumes "\<forall>x. M(p(x),x)"
          "j = p(l)"
shows     "M(j,l)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_4b:
  assumes "\<forall>x. M(p(x),x)"
          "j = p(l)"
shows     "M(j,l)"
proof -
  have "M(p(l),l)" using assms(1) ..
  with assms(2) show "M(j,l)" by (rule ssubst)
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_4c:
  assumes "\<forall>x. M(p(x),x)"
          "j = p(l)"
shows     "M(j,l)"
proof -
  have "M(p(l),l)" using assms(1) by (rule allE)
  with assms(2) show "M(j,l)" by (rule ssubst)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 5. Formalizar, y decidir la corrección, del siguiente
  argumento 
     El esposo de la hermana de Toni es Roberto. La hermana de Toni es
     María. Por tanto, el esposo de María es Roberto. 
  Usar e(x) para el esposo de x
       h    para la hermana de Toni
       m    para María
       r    para Roberto
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_5a:
  assumes "e(h) = r"
          "h = m"
  shows   "e(m) = r"
using assms
by auto

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_5b:
  assumes "e(h) = r"
          "h = m"
  shows   "e(m) = r"
using assms(2,1) 
by (rule subst)

text \<open>--------------------------------------------------------------- 
  Ejercicio 6. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Luis y Jaime tienen el mismo padre. La madre de Rosa es
     Eva. Eva ama a Carlos. Carlos es el padre de Jaime. Por tanto,
     la madre de Rosa ama al padre de Luis.
  Usar A(x,y) para x ama a y
       m(x)   para la madre de x
       p(x)   para el padre de x
       c      para Carlos
       e      para Eva
       j      para Jaime
       l      para Luis
       r      para Rosa
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_6a:
  assumes "p(l) = p(j)"
          "m(r) = e"
          "A(e,c)"
          "c = p(j)"
  shows   "A(m(r),p(l))"
using assms
by auto

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_6b:
  assumes "p(l) = p(j)"
          "m(r) = e"
          "A(e,c)"
          "c = p(j)"
  shows   "A(m(r),p(l))"
proof -
  have "A(m(r),c)" using assms(2,3) by (rule ssubst)
  with assms(4) have "A(m(r),p(j))" by (rule subst)
  with assms(1) show "A(m(r),p(l))" by (rule ssubst)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 7. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Si dos personas son hermanos, entonces tienen la misma madre y el
     mismo padre. Juan es hermano de Luis. Por tanto, la madre del padre
     de Juan es la madre del padre de Luis.
  Usar H(x,y) para x es hermano de y
       m(x)   para la madre de x
       p(x)   para el padre de x
       j      para Juan
       l      para Luis
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_7a:
  assumes "\<forall>x y. H(x,y) \<longrightarrow> m(x) = m(y) \<and> p(x) = p(y)"
          "H(j,l)"
  shows   "m(p(j)) = m(p(l))"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_7b:
  assumes "\<forall>x y. H(x,y) \<longrightarrow> m(x) = m(y) \<and> p(x) = p(y)"
          "H(j,l)"
  shows   "m(p(j)) = m(p(l))"
proof -
  have "\<forall>y. H(j,y) \<longrightarrow> m(j) = m(y) \<and> p(j) = p(y)" using assms(1) ..
  then have "H(j,l) \<longrightarrow> m(j) = m(l) \<and> p(j) = p(l)" ..
  then have "m(j) = m(l) \<and> p(j) = p(l)" using assms(2) ..
  then have "p(j) = p(l)" ..
  have "m(p(j)) = m(p(j))" by (rule refl)
  with \<open>p(j) = p(l)\<close> show "m(p(j)) = m(p(l))" by (rule subst)
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_7c:
  assumes "\<forall>x y. H(x,y) \<longrightarrow> m(x) = m(y) \<and> p(x) = p(y)"
          "H(j,l)"
  shows   "m(p(j)) = m(p(l))"
proof -
  have "\<forall>y. H(j,y) \<longrightarrow> m(j) = m(y) \<and> p(j) = p(y)" 
    using assms(1)  by (rule allE)
  then have "H(j,l) \<longrightarrow> m(j) = m(l) \<and> p(j) = p(l)" by (rule allE)
  then have "m(j) = m(l) \<and> p(j) = p(l)" using assms(2) by (rule mp)
  then have "p(j) = p(l)" by (rule conjunct2)
  have "m(p(j)) = m(p(j))" by (rule refl)
  with \<open>p(j) = p(l)\<close> show "m(p(j)) = m(p(l))" by (rule subst)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 8. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todos los miembros del claustro son asturianos. El secretario forma
     parte del claustro. El señor Martínez es el secretario. Por tanto,
     el señor Martínez es asturiano.
  Usar C(x) para x es miembro del claustro
       A(x) para x es asturiano
       s    para el secretario
       m    para el señor Martínez
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_8a:
  assumes "\<forall>x. C(x) \<longrightarrow> A(x)"
          "C(s)"
          "m = s"
  shows   "A(m)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_8b:
  assumes "\<forall>x. C(x) \<longrightarrow> A(x)"
          "C(s)"
          "m = s"
  shows   "A(m)"
proof -
  have "C(s) \<longrightarrow> A(s)" using assms(1) ..
  then have "A(s)" using assms(2) ..
  with assms(3) show "A(m)" by (rule ssubst)
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_8c:
  assumes "\<forall>x. C(x) \<longrightarrow> A(x)"
          "C(s)"
          "m = s"
  shows   "A(m)"
proof -
  have "C(s) \<longrightarrow> A(s)" using assms(1) by (rule allE)
  then have "A(s)" using assms(2) by (rule mp)
  with assms(3) show "A(m)" by (rule ssubst)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 10. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Eduardo pudo haber visto al asesino. Antonio fue el primer testigo
     de la defensa. O Eduardo estaba en clase o Antonio dio falso
     testimonio. Nadie en clase pudo haber visto al asesino. Luego, el
     primer testigo de la defensa dio falso testimonio. 
  Usar C(x) para x estaba en clase
       F(x) para x dio falso testimonio
       V(x) para x pudo haber visto al asesino
       a    para Antonio
       e    para Eduardo
       p    para el primer testigo de la defensa
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_10a:
  assumes "V(e)"
          "a = p"
          "C(e) \<or> F(a)"
          "\<forall>x. C(x) \<longrightarrow> \<not>V(x)"
   shows  "F(p)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_10b:
  assumes "V(e)"
          "a = p"
          "C(e) \<or> F(a)" 
          "\<forall>x. C(x) \<longrightarrow> \<not>V(x)"
   shows  "F(p)"
proof -
  have "C(e) \<or> F(a)" using assms(3) .
  then have "F(a)"
  proof 
    assume "C(e)"
    have "C(e) \<longrightarrow> \<not>V(e)" using assms(4) ..
    then have "\<not>V(e)" using \<open>C(e)\<close> ..
    then show "F(a)" using assms(1) ..
  next
    assume "F(a)"
    then show "F(a)" .
  qed
  with assms(2) show "F(p)" by (rule subst)
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_10c:
  assumes "V(e)"
          "a = p"
          "C(e) \<or> F(a)" 
          "\<forall>x. C(x) \<longrightarrow> \<not>V(x)"
   shows  "F(p)"
proof -
  have "C(e) \<or> F(a)" using assms(3) by this
  then have "F(a)"
  proof (rule disjE)
    assume "C(e)"
    have "C(e) \<longrightarrow> \<not>V(e)" using assms(4) by (rule allE)
    then have "\<not>V(e)" using \<open>C(e)\<close> by (rule mp)
    then show "F(a)" using assms(1) by (rule notE)
  next
    assume "F(a)"
    then show "F(a)" by this
  qed
  with assms(2) show "F(p)" by (rule subst)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 11. Formalizar, y decidir la corrección, del siguiente
  argumento 
     La luna hoy es redonda. La luna de hace dos semanas tenía forma de
     cuarto creciente. Luna no hay más que una, es decir, siempre es la
     misma. Luego existe algo que es a la vez redondo y con forma de
     cuarto creciente. 
  Usar L(x) para la luna del momento x
       R(x) para x es redonda
       C(x) para x tiene forma de cuarto creciente
       h    para hoy
       d    para hace dos semanas
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_11a:
  assumes "R(l(h))"
          "C(l(d))"
          "\<forall>x y. l(x) = l(y)"
  shows   "\<exists>x. R(x) \<and> C(x)"
using assms
by metis

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_11b:
  assumes "R(l(h))"
          "C(l(d))"
          "\<forall>x y. l(x) = l(y)"
  shows   "\<exists>x. R(x) \<and> C(x)"
proof -
  have "R(l(h)) \<and> C(l(d))" using assms(1,2) ..
  have "\<forall>y. l(d) = l(y)" using assms(3) ..
  then have "l(d) = l(h)" ..
  then have "R(l(h)) \<and> C(l(h))" using \<open>R(l(h)) \<and> C(l(d))\<close> by (rule subst)
  then show "\<exists>x. R(x) \<and> C(x)" ..
qed 

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_11c:
  assumes "R(l(h))"
          "C(l(d))"
          "\<forall>x y. l(x) = l(y)"
  shows   "\<exists>x. R(x) \<and> C(x)"
proof -
  have "R(l(h)) \<and> C(l(d))" using assms(1,2) by (rule conjI)
  have "\<forall>y. l(d) = l(y)" using assms(3) by (rule allE)
  then have "l(d) = l(h)" by (rule allE)
  then have "R(l(h)) \<and> C(l(h))" using \<open>R(l(h)) \<and> C(l(d))\<close> by (rule subst)
  then show "\<exists>x. R(x) \<and> C(x)" by (rule exI)
qed 

text \<open>--------------------------------------------------------------- 
  Ejercicio 12. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Juana sólo tiene un marido. Juana está casada con Tomás. Tomás es
     delgado y Guillermo no. Luego, Juana no está casada con Guillermo. 
  Usar D(x)   para x es delgado
       C(x,y) para x está casada con y
       g      para Guillermo
       j      para Juana
       t      para Tomás
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_12a:
  assumes "\<exists>x. \<forall>y. C(j,y) \<longleftrightarrow> y = x" 
          "C(j,t)" 
          "D(t) \<and> \<not>D(g)"
  shows   "\<not>C(j,g)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_12b:
  assumes "\<exists>x. \<forall>y. C(j,y) \<longleftrightarrow> y = x" 
          "C(j,t)" 
          "D(t) \<and> \<not>D(g)"
  shows   "\<not>C(j,g)"
proof 
  assume "C(j,g)"
  obtain a where a: "\<forall>y. C(j,y) \<longleftrightarrow> y = a" using assms(1) .. 
  then have "C(j,t) \<longleftrightarrow> t = a" ..
  then have "t = a" using assms(2) ..
  have "C(j,g) \<longleftrightarrow> g = a" using a ..
  then have "g = a" using \<open>C(j,g)\<close> ..
  then have "t = g" using \<open>t = a\<close> by (rule ssubst) 
  then have "D(g) \<and> \<not>D(g)" using assms(3) by (rule subst)
  then have "D(g)" ..
  have "\<not>D(g)" using \<open>D(g) \<and> \<not>D(g)\<close> ..
  then show False using \<open>D(g)\<close> ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_12c:
  assumes "\<exists>x. \<forall>y. C(j,y) \<longleftrightarrow> y = x" 
          "C(j,t)" 
          "D(t) \<and> \<not>D(g)"
  shows   "\<not>C(j,g)"
proof (rule notI)
  assume "C(j,g)"
  obtain a where a: "\<forall>y. C(j,y) \<longleftrightarrow> y = a" using assms(1) by (rule exE) 
  then have "C(j,t) \<longleftrightarrow> t = a" by (rule allE)
  then have "t = a" using assms(2) by (rule iffD1)
  have "C(j,g) \<longleftrightarrow> g = a" using a by (rule allE)
  then have "g = a" using \<open>C(j,g)\<close> by (rule iffD1)
  then have "t = g" using \<open>t = a\<close> by (rule ssubst) 
  then have "D(g) \<and> \<not>D(g)" using assms(3) by (rule subst)
  then have "D(g)" by (rule conjunct1)
  have "\<not>D(g)" using \<open>D(g) \<and> \<not>D(g)\<close> by (rule conjunct2)
  then show False using \<open>D(g)\<close> by (rule notE)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 13. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Sultán no es Chitón. Sultán no obtendrá un plátano a menos que
     pueda resolver cualquier problema. Si el chimpancé Chitón trabaja
     más que Sultán resolverá problemas que Sultán no puede resolver. 
     Todos los chimpancés distintos de Sultán trabajan más que Sultán. 
     Por consiguiente, Sultán no obtendrá un plátano.
  Usar Pl(x)  para x obtiene el plátano
       Pr(x)  para x es un problema
       R(x,y) para x resuelve y
       T(x,y) para x trabaja más que y
       c      para Chitón
       s      para Sultán
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_13a:
  assumes "s \<noteq> c"
          "Pl(s) \<longrightarrow> (\<forall>x. Pr(x) \<longrightarrow> R(s,x))"
          "T(c,s) \<longrightarrow> (\<exists>x. Pr(x) \<and> R(c,x) \<and> \<not>R(s,x))" 
          "\<forall>x. x \<noteq> s \<longrightarrow> T(x,s)"
  shows   "\<not>Pl(s)"
using assms
by metis

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_13b:
  assumes "s \<noteq> c"
          "Pl(s) \<longrightarrow> (\<forall>x. Pr(x) \<longrightarrow> R(s,x))"
          "T(c,s) \<longrightarrow> (\<exists>x. Pr(x) \<and> R(c,x) \<and> \<not>R(s,x))" 
          "\<forall>x. x \<noteq> s \<longrightarrow> T(x,s)"
  shows   "\<not>Pl(s)"
proof
  assume "Pl(s)"
  with assms(2) have "\<forall>x. Pr(x) \<longrightarrow> R(s,x)" ..
  have "c \<noteq> s" using assms(1) by (rule not_sym)
  have "c \<noteq> s \<longrightarrow> T(c,s)" using assms(4) ..
  then have "T(c,s)" using \<open>c \<noteq> s\<close> ..
  with assms(3) have "\<exists>x. Pr(x) \<and> R(c,x) \<and> \<not>R(s,x)" ..
  then obtain a where a: "Pr(a) \<and> R(c,a) \<and> \<not>R(s,a)" ..
  have "R(s,a)" 
  proof -
    have "Pr(a)" using a ..
    have "Pr(a) \<longrightarrow> R(s,a)" using \<open>\<forall>x. Pr(x) \<longrightarrow> R(s,x)\<close> ..
    then show "R(s,a)" using \<open>Pr(a)\<close> ..
  qed
  have "\<not>R(s,a)"
  proof -
    have "R(c,a) \<and> \<not>R(s,a)" using a ..
    then show "\<not>R(s,a)" ..
  qed
  then show False using \<open>R(s,a)\<close> ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_13c:
  assumes "s \<noteq> c"
          "Pl(s) \<longrightarrow> (\<forall>x. Pr(x) \<longrightarrow> R(s,x))"
          "T(c,s) \<longrightarrow> (\<exists>x. Pr(x) \<and> R(c,x) \<and> \<not>R(s,x))" 
          "\<forall>x. x \<noteq> s \<longrightarrow> T(x,s)"
  shows   "\<not>Pl(s)"
proof (rule notI)
  assume "Pl(s)"
  with assms(2) have "\<forall>x. Pr(x) \<longrightarrow> R(s,x)" by (rule mp)
  have "c \<noteq> s" using assms(1) by (rule not_sym)
  have "c \<noteq> s \<longrightarrow> T(c,s)" using assms(4) by (rule allE)
  then have "T(c,s)" using \<open>c \<noteq> s\<close> by (rule mp)
  with assms(3) have "\<exists>x. Pr(x) \<and> R(c,x) \<and> \<not>R(s,x)" by (rule mp)
  then obtain a where a: "Pr(a) \<and> R(c,a) \<and> \<not>R(s,a)" by (rule exE)
  have "R(s,a)" 
  proof -
    have "Pr(a)" using a by (rule conjunct1)
    have "Pr(a) \<longrightarrow> R(s,a)" using \<open>\<forall>x. Pr(x) \<longrightarrow> R(s,x)\<close> by (rule allE)
    then show "R(s,a)" using \<open>Pr(a)\<close> by (rule mp)
  qed
  have "\<not>R(s,a)"
  proof -
    have "R(c,a) \<and> \<not>R(s,a)" using a by (rule conjunct2)
    then show "\<not>R(s,a)" by (rule conjunct2)
  qed
  then show False using \<open>R(s,a)\<close> by (rule notE)
qed

end