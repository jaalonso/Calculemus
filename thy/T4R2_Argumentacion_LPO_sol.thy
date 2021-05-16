section \<open>T4R2: Argumentación en lógica de primer orden\<close>

theory T4R2
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

  --------------------------------------------------------------------- 
\<close>

text \<open>
  Se usarán las reglas notnotI y mt que demostramos a continuación.
\<close>

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
by auto

lemma mt: "\<lbrakk>F \<longrightarrow> G; \<not>G\<rbrakk> \<Longrightarrow> \<not>F"
by auto

lemma no_ex: "\<not>(\<exists>x. P(x)) \<Longrightarrow> \<forall>x. \<not>P(x)"
by auto

lemma no_para_todo: "\<not>(\<forall>x. P(x)) \<Longrightarrow> \<exists>x. \<not>P(x)"
by auto

text \<open>--------------------------------------------------------------- 
  Ejercicio 1. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Sócrates es un hombre. 
     Los hombres son mortales. 
     Luego, Sócrates es mortal.
  Usar s    para Sócrates
       H(x) para x es un hombre          
       M(x) para x es mortal
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_1a:
  "\<lbrakk>H(s); \<forall>x. H(x) \<longrightarrow> M(x)\<rbrakk> \<Longrightarrow> M(s)"
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_1b:
  assumes "H(s)" 
          "\<forall>x. H(x) \<longrightarrow> M(x)"
  shows   "M(s)"
proof -
  have "H(s) \<longrightarrow> M(s)" using assms(2) ..
  then show "M(s)" using assms(1) ..  
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_1c:
  assumes "H(s)" 
          "\<forall>x. H(x) \<longrightarrow> M(x)"
  shows   "M(s)"
proof -
  have "H(s) \<longrightarrow> M(s)" using assms(2) by (rule allE)
  then show "M(s)" using assms(1) by (rule mp)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 2. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Hay estudiantes inteligentes y hay estudiantes trabajadores. Por
     tanto, hay estudiantes inteligentes y trabajadores.
  Usar I(x) para x es inteligente
       T(x) para x es trabajador
  ------------------------------------------------------------------\<close>

\<comment> \<open>La refutación automática es\<close>
lemma ejercicio_2a:
  "(\<exists>x. I(x)) \<and> (\<exists>x. T(x)) \<Longrightarrow> \<exists>x. I(x) \<and> T(x)"
quickcheck
oops

text \<open>
El argumento es incorrecto como muestra el siguiente contraejemplo:
   I = {a\<^isub>1}
   T = {a\<^isub>2}
\<close>

text \<open>--------------------------------------------------------------- 
  Ejercicio 3. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todos los participantes son vencedores. Hay como máximo un
     vencedor. Hay como máximo un participante. Por lo tanto, hay
     exactamente un participante. 
  Usar P(x) para x es un participante
       V(x) para x es un vencedor
  ------------------------------------------------------------------\<close>

\<comment> \<open>La refutación automática es\<close>
lemma ejercicio_3a: 
  "\<lbrakk>\<forall>x. P(x) \<longrightarrow> V(x); 
    \<forall>x y. V(x) \<and> V(y) \<longrightarrow> x=y; 
    \<forall>x y. P(x) \<and> P(y) \<longrightarrow> x=y\<rbrakk>
   \<Longrightarrow> \<exists>x. P(x) \<and> (\<forall>y. P(y) \<longrightarrow> x=y)"
quickcheck  
oops

text \<open>
El argumento es incorrecto como muestra el siguiente contraejemplo:
   V = {}
   P = {}
\<close>

text \<open>--------------------------------------------------------------- 
  Ejercicio 4. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todo aquel que entre en el país y no sea un VIP será cacheado por
     un aduanero. Hay un contrabandista que entra en el país y que solo
     podrá ser cacheado por contrabandistas. Ningún contrabandista es un
     VIP. Por tanto, algún aduanero es contrabandista.
  Usar A(x)    para x es aduanero
       Ca(x,y) para x cachea a y
       Co(x)   para x es contrabandista
       E(x)    para x entra en el pais
       V(x)    para x es un VIP
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_4a:
  "\<lbrakk>\<forall>x. E(x) \<and> \<not>V(x) \<longrightarrow> (\<exists>y. A(y) \<and> Ca(y,x));
    \<exists>x. Co(x) \<and> E(x) \<and> (\<forall>y. Ca(y,x) \<longrightarrow> Co(y));
    \<not>(\<exists>x. Co(x) \<and> V(x))\<rbrakk>
   \<Longrightarrow> \<exists>x. A(x) \<and> Co(x)"
by metis

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_4b:
  assumes "\<forall>x. E(x) \<and> \<not>V(x) \<longrightarrow> (\<exists>y. A(y) \<and> Ca(y,x))"
           "\<exists>x. Co(x) \<and> E(x) \<and> (\<forall>y. Ca(y,x) \<longrightarrow> Co(y))"
           "\<not>(\<exists>x. Co(x) \<and> V(x))"
  shows    "\<exists>x. A(x) \<and> Co(x)"
proof -
  obtain a where a: "Co(a) \<and> E(a) \<and> (\<forall>y. Ca(y,a) \<longrightarrow> Co(y))" 
    using assms(2) ..
  have "\<exists>y. A(y) \<and> Ca(y,a)"
  proof -
    have "E(a) \<and> \<not>V(a) \<longrightarrow> (\<exists>y. A(y) \<and> Ca(y,a))" using assms(1) ..
    moreover
    have "E(a) \<and> \<not>V(a)"
    proof
      have "E(a) \<and> (\<forall>y. Ca(y,a) \<longrightarrow> Co(y))" using a ..
      then show "E(a)" ..
    next
      have "\<forall>x. \<not>(Co(x) \<and> V(x))" using assms(3) by (rule no_ex)
      then have "\<not>(Co(a) \<and> V(a))" ..
      have "Co(a)" using a ..
      show "\<not>V(a)" 
      proof
        assume "V(a)"
        with \<open>Co(a)\<close> have "Co(a) \<and> V(a)" ..
        with \<open>\<not>(Co(a) \<and> V(a))\<close> show False ..
      qed
    qed
    ultimately show "\<exists>y. A(y) \<and> Ca(y,a)" ..
  qed
  then obtain b where "A(b) \<and> Ca(b,a)" ..
  then have "A(b)" ..
  moreover
  have "Co(b)"
    proof -
      have "E(a) \<and> (\<forall>y. Ca(y,a) \<longrightarrow> Co(y))" using a ..
      then have "\<forall>y. Ca(y,a) \<longrightarrow> Co(y)" ..
      then have "Ca(b,a) \<longrightarrow> Co(b)" ..
      have "Ca(b,a)" using \<open>A(b) \<and> Ca(b,a)\<close> ..
      with \<open>Ca(b,a) \<longrightarrow> Co(b)\<close> show "Co(b)" ..
    qed
  ultimately have "A(b) \<and> Co(b)" ..
  then show "\<exists>x. A(x) \<and> Co(x)" ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_4c:
  assumes "\<forall>x. E(x) \<and> \<not>V(x) \<longrightarrow> (\<exists>y. A(y) \<and> Ca(y,x))"
           "\<exists>x. Co(x) \<and> E(x) \<and> (\<forall>y. Ca(y,x) \<longrightarrow> Co(y))"
           "\<not>(\<exists>x. Co(x) \<and> V(x))"
  shows    "\<exists>x. A(x) \<and> Co(x)"
proof -
  obtain a where a: "Co(a) \<and> E(a) \<and> (\<forall>y. Ca(y,a) \<longrightarrow> Co(y))" 
    using assms(2) by (rule exE)
  have "\<exists>y. A(y) \<and> Ca(y,a)"
  proof -
    have "E(a) \<and> \<not>V(a) \<longrightarrow> (\<exists>y. A(y) \<and> Ca(y,a))" using assms(1) by (rule allE)
    moreover
    have "E(a) \<and> \<not>V(a)"
    proof
      have "E(a) \<and> (\<forall>y. Ca(y,a) \<longrightarrow> Co(y))" using a by (rule conjunct2)
      then show "E(a)" by (rule conjunct1)
    next
      have "\<forall>x. \<not>(Co(x) \<and> V(x))" using assms(3) by (rule no_ex)
      then have "\<not>(Co(a) \<and> V(a))" by (rule allE)
      have "Co(a)" using a by (rule conjunct1)
      show "\<not>V(a)" 
      proof (rule notI)
        assume "V(a)"
        with \<open>Co(a)\<close> have "Co(a) \<and> V(a)" by (rule conjI)
        with \<open>\<not>(Co(a) \<and> V(a))\<close> show False by (rule notE)
      qed
    qed
    ultimately show "\<exists>y. A(y) \<and> Ca(y,a)" by (rule mp)
  qed
  then obtain b where "A(b) \<and> Ca(b,a)" by (rule exE)
  then have "A(b)" by (rule conjunct1)
  moreover
  have "Co(b)"
    proof -
      have "E(a) \<and> (\<forall>y. Ca(y,a) \<longrightarrow> Co(y))" using a by (rule conjunct2)
      then have "\<forall>y. Ca(y,a) \<longrightarrow> Co(y)" by (rule conjunct2)
      then have "Ca(b,a) \<longrightarrow> Co(b)" by (rule allE)
      have "Ca(b,a)" using \<open>A(b) \<and> Ca(b,a)\<close> by (rule conjunct2)
      with \<open>Ca(b,a) \<longrightarrow> Co(b)\<close> show "Co(b)" by (rule mp)
    qed
  ultimately have "A(b) \<and> Co(b)" by (rule conjI)
  then show "\<exists>x. A(x) \<and> Co(x)" by (rule exI)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 5. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Juan teme a María. Pedro es temido por Juan. Luego, alguien teme a
     María y a Pedro.
  Usar j      para Juan  
       m      para María
       p      para Pedro
       T(x,y) para x teme a y
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_5a:
  "\<lbrakk>T(j,m); T(j,p)\<rbrakk> \<Longrightarrow> \<exists>x. T(x,m) \<and> T(x,p)"
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_5b:
  assumes "T(j,m)" 
          "T(j,p)"
  shows   "\<exists>x. T(x,m) \<and> T(x,p)"
proof
  show "T(j,m) \<and> T(j,p)" using assms ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_5c:
  assumes "T(j,m)" 
          "T(j,p)"
  shows   "\<exists>x. T(x,m) \<and> T(x,p)"
proof (rule exI)
  show "T(j,m) \<and> T(j,p)" using assms by (rule conjI)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 6. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Los hermanos tienen el mismo padre. Juan es hermano de Luis. Carlos
     es padre de Luis. Por tanto, Carlos es padre de Juan.
  Usar H(x,y) para x es hermano de y
       P(x,y) para x es padre de y
       j      para Juan
       l      para Luis
       c      para Carlos
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_6a:
  assumes "\<forall>x y. H(x,y) \<longrightarrow> H(y,x)"
          "\<forall>x y z. H(x,y) \<and> P(z,x) \<longrightarrow> P(z,y)"
          "H(j,l)"
          "P(c,l)"
  shows   "P(c,j)"
using assms
by metis

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_6b:
  fixes H P :: "'a \<times> 'a \<Rightarrow> bool" 
  assumes "\<forall>x y. H(x,y) \<longrightarrow> H(y,x)"
          "\<forall>x y z. H(x,y) \<and> P(z,x) \<longrightarrow> P(z,y)"
          "H(j,l)"
          "P(c,l)"
  shows   "P(c,j)"
proof -
  have "H(l,j) \<and> P(c,l) \<longrightarrow> P(c,j)" 
  proof -
    have "\<forall>y z. H(l,y) \<and> P(z,l) \<longrightarrow> P(z,y)" using assms(2) ..
    then have "\<forall>z. H(l,j) \<and> P(z,l) \<longrightarrow> P(z,j)" ..
    then show "H(l,j) \<and> P(c,l) \<longrightarrow> P(c,j)" ..
  qed
  moreover
  have "H(l,j) \<and> P(c,l)"
  proof
    have "\<forall>y. H(j,y) \<longrightarrow> H(y,j)" using assms(1) ..
    then have "H(j,l) \<longrightarrow> H(l,j)" .. 
    then show "H(l,j)" using assms(3) ..
  next
    show "P(c,l)" using assms(4) .
  qed
  ultimately show "P(c,j)" .. 
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_6c:
  fixes H P :: "'a \<times> 'a \<Rightarrow> bool" 
  assumes "\<forall>x y. H(x,y) \<longrightarrow> H(y,x)"
          "\<forall>x y z. H(x,y) \<and> P(z,x) \<longrightarrow> P(z,y)"
          "H(j,l)"
          "P(c,l)"
  shows   "P(c,j)"
proof -
  have "H(l,j) \<and> P(c,l) \<longrightarrow> P(c,j)" 
  proof -
    have "\<forall>y z. H(l,y) \<and> P(z,l) \<longrightarrow> P(z,y)" using assms(2) by (rule allE)
    then have "\<forall>z. H(l,j) \<and> P(z,l) \<longrightarrow> P(z,j)" by (rule allE)
    then show "H(l,j) \<and> P(c,l) \<longrightarrow> P(c,j)" by (rule allE)
  qed
  moreover
  have "H(l,j) \<and> P(c,l)"
  proof (rule conjI)
    have "\<forall>y. H(j,y) \<longrightarrow> H(y,j)" using assms(1) by (rule allE)
    then have "H(j,l) \<longrightarrow> H(l,j)" by (rule allE)
    then show "H(l,j)" using assms(3) by (rule mp)
  next
    show "P(c,l)" using assms(4) by this
  qed
  ultimately show "P(c,j)" by (rule mp)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 7. Formalizar, y decidir la corrección, del siguiente
  argumento 
     La existencia de algún canal de TV pública, supone un acicate para
     cualquier canal de TV privada; el que un canal de TV tenga un
     acicate, supone una gran satisfacción para cualquiera de sus
     directivos; en Madrid hay varios canales públicos de TV; TV5 es un
     canal de TV privada; por tanto, todos los directivos de TV5 están
     satisfechos. 
  Usar Pu(x)  para x es un canal de TV pública
       Pr(x)  para x es un canal de TV privada
       A(x)   para x posee un acicate
       D(x,y) para x es un directivo del canal y
       S(x)   para x está satisfecho 
       t      para TV5
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_7a:
  assumes "(\<exists>x. Pu(x)) \<longrightarrow> (\<forall>x. Pr(x) \<longrightarrow> A(x))"
          "\<forall>x. A(x) \<longrightarrow> (\<forall>y. D(y,x) \<longrightarrow> S(y))"
          "\<exists>x. Pu(x)"
          "Pr(t)"
  shows   "\<forall>x. D(x,t) \<longrightarrow> S(x)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_7b:
  assumes "(\<exists>x. Pu(x)) \<longrightarrow> (\<forall>x. Pr(x) \<longrightarrow> A(x))"
          "\<forall>x. A(x) \<longrightarrow> (\<forall>y. D(y,x) \<longrightarrow> S(y))"
          "\<exists>x. Pu(x)"
          "Pr(t)"
  shows   "\<forall>x. D(x,t) \<longrightarrow> S(x)"
proof
  fix a 
  show "D(a,t) \<longrightarrow> S(a)"
  proof
    assume "D(a,t)"
    have "\<forall>x. Pr(x) \<longrightarrow> A(x)" using assms(1) assms(3) ..
    then have "Pr(t) \<longrightarrow> A(t)" ..
    then have "A(t)" using assms(4) ..
    have "A(t) \<longrightarrow> (\<forall>y. D(y,t) \<longrightarrow> S(y))" using assms(2) ..
    then have "\<forall>y. D(y,t) \<longrightarrow> S(y)" using \<open>A(t)\<close> ..
    then have "D(a,t) \<longrightarrow> S(a)" ..
    then show "S(a)" using \<open>D(a,t)\<close> ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_7c:
  assumes "(\<exists>x. Pu(x)) \<longrightarrow> (\<forall>x. Pr(x) \<longrightarrow> A(x))"
          "\<forall>x. A(x) \<longrightarrow> (\<forall>y. D(y,x) \<longrightarrow> S(y))"
          "\<exists>x. Pu(x)"
          "Pr(t)"
  shows   "\<forall>x. D(x,t) \<longrightarrow> S(x)"
proof (rule allI)
  fix a 
  show "D(a,t) \<longrightarrow> S(a)"
  proof (rule impI)
    assume "D(a,t)"
    have "\<forall>x. Pr(x) \<longrightarrow> A(x)" using assms(1) assms(3) by (rule mp)
    then have "Pr(t) \<longrightarrow> A(t)" by (rule allE)
    then have "A(t)" using assms(4) by (rule mp)
    have "A(t) \<longrightarrow> (\<forall>y. D(y,t) \<longrightarrow> S(y))" using assms(2) by (rule allE)
    then have "\<forall>y. D(y,t) \<longrightarrow> S(y)" using \<open>A(t)\<close> by (rule mp)
    then have "D(a,t) \<longrightarrow> S(a)" by (rule allE)
    then show "S(a)" using \<open>D(a,t)\<close> by (rule mp)
  qed
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 8. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Quien intente entrar en un país y no tenga pasaporte, encontrará
     algún aduanero que le impida el paso. A algunas personas
     motorizadas que intentan entrar en un país le impiden el paso
     únicamente personas motorizadas. Ninguna persona motorizada tiene
     pasaporte. Por tanto, ciertos aduaneros están motorizados.
  Usar E(x)   para x entra en un país
       P(x)   para x tiene pasaporte
       A(x)   para x es aduanero
       I(x,y) para x impide el paso a y
       M(x)   para x está motorizada
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_8a:
  assumes "\<forall>x. E(x) \<and> \<not>P(x) \<longrightarrow> (\<exists>y. A(y) \<and> I(y,x))"
          "\<exists>x. M(x) \<and> E(x) \<and> (\<forall>y. I(y,x) \<longrightarrow> M(y))"
          "\<forall>x. M(x) \<longrightarrow> \<not>P(x)"
  shows "\<exists>x. A(x) \<and> M(x)"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_8b:
  assumes "\<forall>x. E(x) \<and> \<not>P(x) \<longrightarrow> (\<exists>y. A(y) \<and> I(y,x))"
          "\<exists>x. M(x) \<and> E(x) \<and> (\<forall>y. I(y,x) \<longrightarrow> M(y))"
          "\<forall>x. M(x) \<longrightarrow> \<not>P(x)"
  shows "\<exists>x. A(x) \<and> M(x)"
proof - 
  obtain a where a: "M(a) \<and> E(a) \<and> (\<forall>y. I(y,a) \<longrightarrow> M(y))" using assms(2) ..
  then have "M(a)" ..
  have "M(a) \<longrightarrow> \<not>P(a)" using assms(3) ..
  then have "\<not>P(a)" using \<open>M(a)\<close> ..
  have a1: "E(a) \<and> (\<forall>y. I(y,a) \<longrightarrow> M(y))" using a ..
  then have "E(a)" ..
  then have "E(a) \<and> \<not>P(a)" using \<open>\<not>P(a)\<close> ..
  have "E(a) \<and> \<not>P(a) \<longrightarrow> (\<exists>y. A(y) \<and> I(y,a))" using assms(1) ..
  then have "\<exists>y. A(y) \<and> I(y,a)" using \<open>E(a) \<and> \<not>P(a)\<close>..
  then obtain b where b: "A(b) \<and> I(b,a)" ..
  have "A(b) \<and> M(b)"
  proof
    show "A(b)" using b ..
  next
    have "I(b,a)" using b ..
    have "\<forall>y. I(y,a) \<longrightarrow> M(y)" using a1 ..
    then have "I(b,a) \<longrightarrow> M(b)" ..
    then show "M(b)" using \<open>I(b,a)\<close> ..
  qed
  then show "\<exists>x. A(x) \<and> M(x)" ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_8c:
  assumes "\<forall>x. E(x) \<and> \<not>P(x) \<longrightarrow> (\<exists>y. A(y) \<and> I(y,x))"
          "\<exists>x. M(x) \<and> E(x) \<and> (\<forall>y. I(y,x) \<longrightarrow> M(y))"
          "\<forall>x. M(x) \<longrightarrow> \<not>P(x)"
  shows "\<exists>x. A(x) \<and> M(x)"
proof - 
  obtain a where a: "M(a) \<and> E(a) \<and> (\<forall>y. I(y,a) \<longrightarrow> M(y))" 
    using assms(2) by (rule exE)
  then have "M(a)" by (rule conjunct1)
  have "M(a) \<longrightarrow> \<not>P(a)" using assms(3) by (rule allE)
  then have "\<not>P(a)" using \<open>M(a)\<close> by (rule mp)
  have a1: "E(a) \<and> (\<forall>y. I(y,a) \<longrightarrow> M(y))" using a by (rule conjunct2)
  then have "E(a)" by (rule conjunct1)
  then have "E(a) \<and> \<not>P(a)" using \<open>\<not>P(a)\<close> by (rule conjI)
  have "E(a) \<and> \<not>P(a) \<longrightarrow> (\<exists>y. A(y) \<and> I(y,a))" 
    using assms(1) by (rule allE)
  then have "\<exists>y. A(y) \<and> I(y,a)" using \<open>E(a) \<and> \<not>P(a)\<close>by (rule mp)
  then obtain b where b: "A(b) \<and> I(b,a)" by (rule exE)
  have "A(b) \<and> M(b)"
  proof (rule conjI)
    show "A(b)" using b by (rule conjunct1)
  next
    have "I(b,a)" using b by (rule conjunct2)
    have "\<forall>y. I(y,a) \<longrightarrow> M(y)" using a1 by (rule conjunct2)
    then have "I(b,a) \<longrightarrow> M(b)" by (rule allE)
    then show "M(b)" using \<open>I(b,a)\<close>by (rule mp)
  qed
  then show "\<exists>x. A(x) \<and> M(x)" by (rule exI)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 9. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Los aficionados al fútbol aplauden a cualquier futbolista
     extranjero. Juanito no aplaude a futbolistas extranjeros. Por
     tanto, si hay algún futbolista extranjero nacionalizado español,
     Juanito no es aficionado al fútbol.
  Usar Af(x)   para x es aficicionado al fútbol
       Ap(x,y) para x aplaude a y
       E(x)    para x es un futbolista extranjero
       N(x)    para x es un futbolista nacionalizado español
       j       para Juanito
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_9a:
  assumes "\<forall>x. Af(x) \<longrightarrow> (\<forall>y. E(y) \<longrightarrow> Ap(x,y))"
          "\<forall>x. E(x) \<longrightarrow> \<not>Ap(j,x)"
  shows   "(\<exists>x. E(x) \<and> N(x)) \<longrightarrow> \<not>Af(j)"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_9b:
  assumes "\<forall>x. Af(x) \<longrightarrow> (\<forall>y. E(y) \<longrightarrow> Ap(x,y))"
          "\<forall>x. E(x) \<longrightarrow> \<not>Ap(j,x)"
  shows   "(\<exists>x. E(x) \<and> N(x)) \<longrightarrow> \<not>Af(j)"
proof
  assume "\<exists>x. E(x) \<and> N(x)"
  then obtain a where a: "E(a) \<and> N(a)" ..
  show "\<not>Af(j)"
  proof
    assume "Af(j)"
    have "Af(j) \<longrightarrow> (\<forall>y. E(y) \<longrightarrow> Ap(j,y))" using assms(1) ..
    then have "\<forall>y. E(y) \<longrightarrow> Ap(j,y)" using \<open>Af(j)\<close> ..
    then have "E(a) \<longrightarrow> Ap(j,a)" ..
    have "E(a)" using a ..
    with \<open>E(a) \<longrightarrow> Ap(j,a)\<close> have "Ap(j,a)" ..
    have "E(a) \<longrightarrow> \<not>Ap(j,a)" using assms(2) ..
    then have "\<not>Ap(j,a)" using \<open>E(a)\<close> ..
    then show False using \<open>Ap(j,a)\<close> ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_9c:
  assumes "\<forall>x. Af(x) \<longrightarrow> (\<forall>y. E(y) \<longrightarrow> Ap(x,y))"
          "\<forall>x. E(x) \<longrightarrow> \<not>Ap(j,x)"
  shows   "(\<exists>x. E(x) \<and> N(x)) \<longrightarrow> \<not>Af(j)"
proof (rule impI)
  assume "\<exists>x. E(x) \<and> N(x)"
  then obtain a where a: "E(a) \<and> N(a)" by (rule exE)
  show "\<not>Af(j)"
  proof (rule notI)
    assume "Af(j)"
    have "Af(j) \<longrightarrow> (\<forall>y. E(y) \<longrightarrow> Ap(j,y))" using assms(1) by (rule allE)
    then have "\<forall>y. E(y) \<longrightarrow> Ap(j,y)" using \<open>Af(j)\<close> by (rule mp)
    then have "E(a) \<longrightarrow> Ap(j,a)" by (rule allE)
    have "E(a)" using a by (rule conjunct1)
    with \<open>E(a) \<longrightarrow> Ap(j,a)\<close> have "Ap(j,a)" by (rule mp)
    have "E(a) \<longrightarrow> \<not>Ap(j,a)" using assms(2) by (rule allE)
    then have "\<not>Ap(j,a)" using \<open>E(a)\<close> by (rule mp)
    then show False using \<open>Ap(j,a)\<close> by (rule notE)
  qed
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 10. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Ningún aristócrata debe ser condenado a galeras a menos que sus
     crímenes sean vergonzosos y lleve una vida licenciosa. En la ciudad
     hay aristócratas que han cometido crímenes vergonzosos aunque su
     forma de vida no sea licenciosa. Por tanto, hay algún aristócrata
     que no está condenado a galeras. 
  Usar A(x)  para x es aristócrata
       G(x)  para x está condenado a galeras
       L(x)  para x lleva una vida licenciosa
       V(x)  para x ha cometido crímenes vergonzoso
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_10a:
  assumes "\<forall>x. A(x) \<and> G(x) \<longrightarrow> L(x) \<and> V(x)"
          "\<exists>x. A(x) \<and> V(x) \<and> \<not>L(x)"
  shows   "\<exists>x. A(x) \<and> \<not>G(x)"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_10b:
  assumes "\<forall>x. A(x) \<and> G(x) \<longrightarrow> L(x) \<and> V(x)"
          "\<exists>x. A(x) \<and> V(x) \<and> \<not>L(x)"
  shows   "\<exists>x. A(x) \<and> \<not>G(x)"
proof -
  obtain b where b: "A(b) \<and> V(b) \<and> \<not>L(b)" using assms(2) ..
  have "A(b) \<and> \<not>G(b)"
  proof
    show "A(b)" using b ..
  next
    show "\<not>G(b)"
    proof
      assume "G(b)"
      have "\<not>L(b)"
      proof -
        have "V(b) \<and> \<not>L(b)" using b ..
        then show "\<not>L(b)" ..
      qed
      moreover have "L(b)"
      proof -
        have "A(b) \<and> G(b) \<longrightarrow> L(b) \<and> V(b)" using assms(1) ..
        have "A(b)" using b ..
        then have "A(b) \<and> G(b)" using \<open>G(b)\<close> ..
        with \<open>A(b) \<and> G(b) \<longrightarrow> L(b) \<and> V(b)\<close> have "L(b) \<and> V(b)" ..
        then show "L(b)" ..
      qed
      ultimately show False ..
    qed
  qed
  then show "\<exists>x. A(x) \<and> \<not>G(x)" ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_10c:
  assumes "\<forall>x. A(x) \<and> G(x) \<longrightarrow> L(x) \<and> V(x)"
          "\<exists>x. A(x) \<and> V(x) \<and> \<not>L(x)"
  shows   "\<exists>x. A(x) \<and> \<not>G(x)"
proof -
  obtain b where b: "A(b) \<and> V(b) \<and> \<not>L(b)" using assms(2) by (rule exE)
  have "A(b) \<and> \<not>G(b)"
  proof (rule conjI)
    show "A(b)" using b by (rule conjunct1)
  next
    show "\<not>G(b)"
    proof (rule notI)
      assume "G(b)"
      have "\<not>L(b)"
      proof -
        have "V(b) \<and> \<not>L(b)" using b by (rule conjunct2)
        then show "\<not>L(b)" by (rule conjunct2)
      qed
      moreover have "L(b)"
      proof -
        have "A(b) \<and> G(b) \<longrightarrow> L(b) \<and> V(b)" using assms(1) by (rule allE)
        have "A(b)" using b by (rule conjunct1)
        then have "A(b) \<and> G(b)" using \<open>G(b)\<close> by (rule conjI)
        with \<open>A(b) \<and> G(b) \<longrightarrow> L(b) \<and> V(b)\<close> have "L(b) \<and> V(b)" by (rule mp)
        then show "L(b)" by (rule conjunct1)
      qed
      ultimately show False by (rule notE)
    qed
  qed
  then show "\<exists>x. A(x) \<and> \<not>G(x)" by (rule exI)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 11. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todo individuo que esté conforme con el contenido de cualquier
     acuerdo internacional lo apoya o se inhibe en absoluto de asuntos
     políticos. Cualquiera que se inhiba de los asuntos políticos, no
     participará en el próximo referéndum. Todo español, está conforme
     con el acuerdo internacional de Maastricht, al que sin embargo no
     apoya. Por tanto, cualquier individuo o no es español, o en otro
     caso, está conforme con el contenido del acuerdo internacional de
     Maastricht y no participará en el próximo referéndum. 
  Usar C(x,y) para la persona x conforme con el contenido del acuerdo y
       A(x,y) para la persona x apoya el acuerdo y
       I(x)   para la persona x se inibe de asuntos políticos
       R(x)   para la persona x participará en el próximo referéndum
       E(x)   para la persona x es española
       m      para el acuerdo de Maastricht
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_11a:
  assumes "\<forall>x y. C(x,y) \<longrightarrow> A(x,y) \<or> I(x)"
          "\<forall>x. I(x) \<longrightarrow> \<not>R(x)"
          "\<forall>x. E(x) \<longrightarrow> C(x,m) \<and> \<not>A(x,m)"
  shows   "\<forall>x. \<not>E(x) \<or> (C(x,m) \<and> \<not>R(x))"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_11b:
  assumes "\<forall>x y. C(x,y) \<longrightarrow> A(x,y) \<or> I(x)"
          "\<forall>x. I(x) \<longrightarrow> \<not>R(x)"
          "\<forall>x. E(x) \<longrightarrow> C(x,m) \<and> \<not>A(x,m)"
  shows   "\<forall>x. \<not>E(x) \<or> (C(x,m) \<and> \<not>R(x))"
proof
  fix a
  have "\<not>E(a) \<or> E(a)" ..
  then show "\<not>E(a) \<or> (C(a,m) \<and> \<not>R(a))"
  proof
    assume "\<not>E(a)"
    then show "\<not>E(a) \<or> (C(a,m) \<and> \<not>R(a))" ..
  next
    assume "E(a)"
    have "E(a) \<longrightarrow> C(a,m) \<and> \<not>A(a,m)" using assms(3) ..
    then have "C(a,m) \<and> \<not>A(a,m)" using \<open>E(a)\<close> ..
    then have "C(a,m)" .. 
    have "\<forall>y. C(a,y) \<longrightarrow> A(a,y) \<or> I(a)" using assms(1) ..
    then have "C(a,m) \<longrightarrow> A(a,m) \<or> I(a)" ..
    then have "A(a,m) \<or> I(a)" using \<open>C(a,m)\<close> ..
    then have "\<not>R(a)"
    proof 
      assume "A(a,m)"
      have "\<not>A(a,m)" using \<open>C(a,m) \<and> \<not>A(a,m)\<close>..
      then show "\<not>R(a)" using \<open>A(a,m)\<close> ..
    next
      assume "I(a)"
      have "I(a) \<longrightarrow> \<not>R(a)" using assms(2) ..
      then show "\<not>R(a)" using \<open>I(a)\<close> ..
    qed
    with \<open>C(a,m)\<close> have "C(a,m) \<and> \<not>R(a)" ..
    then show "\<not>E(a) \<or> (C(a,m) \<and> \<not>R(a))" ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_11c:
  assumes "\<forall>x y. C(x,y) \<longrightarrow> A(x,y) \<or> I(x)"
          "\<forall>x. I(x) \<longrightarrow> \<not>R(x)"
          "\<forall>x. E(x) \<longrightarrow> C(x,m) \<and> \<not>A(x,m)"
  shows   "\<forall>x. \<not>E(x) \<or> (C(x,m) \<and> \<not>R(x))"
proof (rule allI)
  fix a
  have "\<not>E(a) \<or> E(a)" by (rule excluded_middle)
  then show "\<not>E(a) \<or> (C(a,m) \<and> \<not>R(a))" 
  proof (rule disjE)
    assume "\<not>E(a)"
    then show "\<not>E(a) \<or> (C(a,m) \<and> \<not>R(a))" by (rule disjI1)
  next
    assume "E(a)"
    have "E(a) \<longrightarrow> C(a,m) \<and> \<not>A(a,m)" using assms(3) by (rule allE)
    then have "C(a,m) \<and> \<not>A(a,m)" using \<open>E(a)\<close> by (rule mp)
    then have "C(a,m)" by (rule conjunct1)
    have "\<forall>y. C(a,y) \<longrightarrow> A(a,y) \<or> I(a)" using assms(1) by (rule allE)
    then have "C(a,m) \<longrightarrow> A(a,m) \<or> I(a)" by (rule allE)
    then have "A(a,m) \<or> I(a)" using \<open>C(a,m)\<close> by (rule mp)
    then have "\<not>R(a)"
    proof (rule disjE)
      assume "A(a,m)"
      have "\<not>A(a,m)" using \<open>C(a,m) \<and> \<not>A(a,m)\<close>by (rule conjunct2)
      then show "\<not>R(a)" using \<open>A(a,m)\<close> by (rule notE)
    next
      assume "I(a)"
      have "I(a) \<longrightarrow> \<not>R(a)" using assms(2) by (rule allE)
      then show "\<not>R(a)" using \<open>I(a)\<close> by (rule mp)
    qed
    with \<open>C(a,m)\<close> have "C(a,m) \<and> \<not>R(a)" by (rule conjI)
    then show "\<not>E(a) \<or> (C(a,m) \<and> \<not>R(a))" by (rule disjI2)
  qed
qed

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
    then have "\<forall>x. \<not>R(x)" by (rule no_ex)
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

text \<open>--------------------------------------------------------------- 
  Ejercicio 13. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todo deprimido que estima a un submarinista es listo. Cualquiera
     que se estime a sí mismo es listo. Ningún deprimido se estima a sí
     mismo. Por tanto, ningún deprimido estima a un submarinista.
  Usar D(x)   para x está deprimido
       E(x,y) para x estima a y
       L(x)   para x es listo
       S(x)   para x es submarinista
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_13a:
  assumes "\<forall>x. D(x) \<and> (\<exists>y. S(y) \<and> E(x,y)) \<longrightarrow> L(x)"
          "\<forall>x. E(x,x) \<longrightarrow> L(x)"
          "\<not>(\<exists>x. D(x) \<and> E(x,x))"
  shows   "\<not>(\<exists>x. D(x) \<and> (\<exists>y. S(y) \<and> E(x,y)))"
quickcheck
oops

text \<open>
  El argumento es incorrecto como muestra el siguiente contraejemplo:
     Quickcheck found a counterexample:
     D = {a\<^isub>2}
     S = {a\<^isub>1}
     E = {(a\<^isub>2, a\<^isub>1)}
     L = {a\<^isub>2}
\<close>

text \<open>--------------------------------------------------------------- 
  Ejercicio 14. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Todos los robots obedecen a los amigos del programador jefe.
     Alvaro es amigo del programador jefe, pero Benito no le
     obedece. Por tanto, Benito no es un robot.
  Usar R(x)    para x es un robot
       Ob(x,y) para x obedece a y
       A(x)    para x es amigo del programador jefe
       b       para Benito
       a       para Alvaro
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_14a:
  assumes "\<forall>x y. R(x) \<and> A(y) \<longrightarrow> Ob(x,y)"
          "A(a)"
          "\<not>Ob(b,a)"
  shows   "\<not>R(b)"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_14b:
  fixes R A :: "'a \<Rightarrow> bool" and
        Ob :: "'a \<times> 'a \<Rightarrow> bool"
  assumes "\<forall>x y. R(x) \<and> A(y) \<longrightarrow> Ob(x,y)"
          "A(a)"
          "\<not>Ob(b,a)"
  shows   "\<not>R(b)"
proof
  assume "R(b)"
  have "\<forall>y. R(b) \<and> A(y) \<longrightarrow> Ob(b,y)" using assms(1) ..
  then have "R(b) \<and> A(a) \<longrightarrow> Ob(b,a)" ..
  have "R(b) \<and> A(a)" using \<open>R(b)\<close> assms(2) ..
  with \<open>R(b) \<and> A(a) \<longrightarrow> Ob(b,a)\<close> have "Ob(b,a)" ..
  with assms(3) show False ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_14c:
  fixes R A :: "'a \<Rightarrow> bool" and
        Ob :: "'a \<times> 'a \<Rightarrow> bool"
  assumes "\<forall>x y. R(x) \<and> A(y) \<longrightarrow> Ob(x,y)"
          "A(a)"
          "\<not>Ob(b,a)"
  shows   "\<not>R(b)"
proof (rule notI)
  assume "R(b)"
  have "\<forall>y. R(b) \<and> A(y) \<longrightarrow> Ob(b,y)" using assms(1) by (rule allE)
  then have "R(b) \<and> A(a) \<longrightarrow> Ob(b,a)" by (rule allE)
  have "R(b) \<and> A(a)" using \<open>R(b)\<close> assms(2) by (rule conjI)
  with \<open>R(b) \<and> A(a) \<longrightarrow> Ob(b,a)\<close> have "Ob(b,a)" by (rule mp)
  with assms(3) show False by (rule notE)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 15. Formalizar, y decidir la corrección, del siguiente
  argumento 
     En una pecera nadan una serie de peces. Se observa que:
     * Hay algún pez x que para cualquier pez y, si el pez x no se come
       al pez y entonces existe un pez z tal que z es un tiburón o bien
       z protege al pez y. 
     * No hay ningún pez que se coma a todos los demás.
     * Ningún pez protege a ningún otro.
     Por tanto, existe algún tiburón en la pecera.
  Usar C(x,y) para x se come a y 
       P(x,y) para x protege a y
       T(x)   para x es un tiburón
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_15a:
  assumes "\<exists>x. \<forall>y. \<not>C(x,y) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,y))"
          "\<forall>x. \<exists>y. \<not>C(x,y)"
          "\<forall>x y. \<not>P(x,y)"
  shows   "\<exists>x. T(x)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_15b:
  assumes "\<exists>x. \<forall>y. \<not>C(x,y) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,y))"
          "\<forall>x. \<exists>y. \<not>C(x,y)"
          "\<forall>x y. \<not>P(x,y)"
  shows   "\<exists>x. T(x)"
proof - 
  obtain a where  a: "\<forall>y. \<not>C(a,y) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,y))" 
    using assms(1) ..
  have "\<exists>y. \<not>C(a,y)" using assms(2) ..
  then obtain b where "\<not>C(a,b)" ..
  have "\<not>C(a,b) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,b))" using a ..
  then have "\<exists>z. T(z) \<or> P(z,b)" using \<open>\<not>C(a,b)\<close> ..
  then obtain c where "T(c) \<or> P(c,b)" ..
  then show "\<exists>x. T(x)"
  proof 
    assume "T(c)"
    then show "\<exists>x. T(x)" ..
  next
    assume "P(c,b)"
    have "\<forall>y. \<not>P(c,y)" using assms(3) ..
    then have "\<not>P(c,b)" ..
    then show "\<exists>x. T(x)" using \<open>P(c,b)\<close> ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_15c:
  assumes "\<exists>x. \<forall>y. \<not>C(x,y) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,y))"
          "\<forall>x. \<exists>y. \<not>C(x,y)"
          "\<forall>x y. \<not>P(x,y)"
  shows   "\<exists>x. T(x)"
proof - 
  obtain a where  a: "\<forall>y. \<not>C(a,y) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,y))" 
    using assms(1) by (rule exE)
  have "\<exists>y. \<not>C(a,y)" using assms(2) by (rule allE)
  then obtain b where "\<not>C(a,b)" by (rule exE)
  have "\<not>C(a,b) \<longrightarrow> (\<exists>z. T(z) \<or> P(z,b))" using a by (rule allE)
  then have "\<exists>z. T(z) \<or> P(z,b)" using \<open>\<not>C(a,b)\<close> by (rule mp)
  then obtain c where "T(c) \<or> P(c,b)" by (rule exE)
  then show "\<exists>x. T(x)"
  proof (rule disjE)
    assume "T(c)"
    then show "\<exists>x. T(x)" by (rule exI)
  next
    assume "P(c,b)"
    have "\<forall>y. \<not>P(c,y)" using assms(3) by (rule allE)
    then have "\<not>P(c,b)" by (rule allE)
    then show "\<exists>x. T(x)" using \<open>P(c,b)\<close> by (rule notE)
  qed
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 16. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Supongamos conocidos los siguientes hechos acerca del número de
     aprobados de dos asignaturas A y B: 
     * Si todos los alumnos aprueban la asignatura A, entonces todos
       aprueban la asignatura B.
     * Si algún delegado de la clase aprueba A y B, entonces todos los 
       alumnos aprueban A.
     * Si nadie aprueba B, entonces ningún delegado aprueba A.
     * Si Manuel no aprueba B, entonces nadie aprueba B.
     Por tanto, si Manuel es un delegado y aprueba la asignatura A,
     entonces todos los alumnos aprueban las asignaturas A y B.
  Usar A(x,y) para x aprueba la asignatura y
       D(x)   para x es delegado
       m      para Manuel
       a      para la asignatura A
       b      para la asignatura B
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_16a:
  assumes "(\<forall>x. A(x,a)) \<longrightarrow> (\<forall>x. A(x,b))"
          "(\<exists>x. D(x) \<and> A(x,a) \<and> A(x,b)) \<longrightarrow> (\<forall>x. A(x,a))"
          "(\<forall>x. \<not>A(x,b)) \<longrightarrow> (\<forall>x. D(x) \<longrightarrow> \<not>A(x,a))"
          "\<not>A(m,b) \<longrightarrow> (\<forall>x. \<not>A(x,b))"
   shows  "D(m) \<and> A(m,a) \<longrightarrow> (\<forall>x. A(x,a) \<and> A(x,b))"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_16b:
  assumes "(\<forall>x. A(x,a)) \<longrightarrow> (\<forall>x. A(x,b))"
          "(\<exists>x. D(x) \<and> A(x,a) \<and> A(x,b)) \<longrightarrow> (\<forall>x. A(x,a))"
          "(\<forall>x. \<not>A(x,b)) \<longrightarrow> (\<forall>x. D(x) \<longrightarrow> \<not>A(x,a))"
          "\<not>A(m,b) \<longrightarrow> (\<forall>x. \<not>A(x,b))"
   shows  "D(m) \<and> A(m,a) \<longrightarrow> (\<forall>x. A(x,a) \<and> A(x,b))"
proof
  assume "D(m) \<and> A(m,a)"
  then have "D(m)" ..
  have "A(m,a)" using \<open>D(m) \<and> A(m,a)\<close> ..
  have "A(m,b)"
  proof (rule ccontr)
    assume "\<not>A(m,b)"
    with assms(4) have "\<forall>x. \<not>A(x,b)" ..
    with assms(3) have "\<forall>x. D(x) \<longrightarrow> \<not>A(x,a)" ..
    then have "D(m) \<longrightarrow> \<not>A(m,a)" ..
    then have "\<not>A(m,a)" using \<open>D(m)\<close> ..
    then show False using \<open>A(m,a)\<close> ..
  qed
  with \<open>A(m,a)\<close> have "A(m,a) \<and> A(m,b)" ..
  with \<open>D(m)\<close> have "D(m) \<and> A(m,a) \<and> A(m,b)" ..
  then have "\<exists>x. D(x) \<and> A(x,a) \<and> A(x,b)" ..
  with assms(2) have "\<forall>x. A(x,a)" ..
  with assms(1) have "\<forall>x. A(x,b)" ..
  show "\<forall>x. A(x,a) \<and> A(x,b)"
  proof
    fix c
    show "A(c,a) \<and> A(c,b)"
    proof
      show "A(c,a)" using \<open>\<forall>x. A(x,a)\<close> ..
    next
      show "A(c,b)" using \<open>\<forall>x. A(x,b)\<close> ..
    qed
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_16c:
  assumes "(\<forall>x. A(x,a)) \<longrightarrow> (\<forall>x. A(x,b))"
          "(\<exists>x. D(x) \<and> A(x,a) \<and> A(x,b)) \<longrightarrow> (\<forall>x. A(x,a))"
          "(\<forall>x. \<not>A(x,b)) \<longrightarrow> (\<forall>x. D(x) \<longrightarrow> \<not>A(x,a))"
          "\<not>A(m,b) \<longrightarrow> (\<forall>x. \<not>A(x,b))"
   shows  "D(m) \<and> A(m,a) \<longrightarrow> (\<forall>x. A(x,a) \<and> A(x,b))"
proof (rule impI)
  assume "D(m) \<and> A(m,a)"
  then have "D(m)" by (rule conjunct1)
  have "A(m,a)" using \<open>D(m) \<and> A(m,a)\<close> by (rule conjunct2)
  have "A(m,b)"
  proof (rule ccontr)
    assume "\<not>A(m,b)"
    with assms(4) have "\<forall>x. \<not>A(x,b)" by (rule mp)
    with assms(3) have "\<forall>x. D(x) \<longrightarrow> \<not>A(x,a)" by (rule mp)
    then have "D(m) \<longrightarrow> \<not>A(m,a)" by (rule allE)
    then have "\<not>A(m,a)" using \<open>D(m)\<close> by (rule mp)
    then show False using \<open>A(m,a)\<close> by (rule notE)
  qed
  with \<open>A(m,a)\<close> have "A(m,a) \<and> A(m,b)" by (rule conjI)
  with \<open>D(m)\<close> have "D(m) \<and> A(m,a) \<and> A(m,b)" by (rule conjI)
  then have "\<exists>x. D(x) \<and> A(x,a) \<and> A(x,b)" by (rule exI)
  with assms(2) have "\<forall>x. A(x,a)" by (rule mp)
  with assms(1) have "\<forall>x. A(x,b)" by (rule mp)
  show "\<forall>x. A(x,a) \<and> A(x,b)"
  proof (rule allI)
    fix c
    show "A(c,a) \<and> A(c,b)"
    proof (rule conjI)
      show "A(c,a)" using \<open>\<forall>x. A(x,a)\<close> by (rule allE)
    next
      show "A(c,b)" using \<open>\<forall>x. A(x,b)\<close> by (rule allE)
    qed
  qed
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 17. Formalizar, y decidir la corrección, del siguiente
  argumento 
     En cierto país oriental se ha celebrado la fase final del
     campeonato mundial de fútbol. Cierto diario deportivo ha publicado
     las siguientes estadísticas de tan magno acontecimiento: 
     * A todos los porteros que no vistieron camiseta negra les marcó un
       gol algún delantero europeo.  
     * Algún portero jugó con botas blancas y sólo le marcaron goles
       jugadores con botas blancas.  
     * Ningún portero se marcó un gol a sí mismo. 
     * Ningún jugador con botas blancas vistió camiseta negra. 
     Por tanto, algún delantero europeo jugó con botas blancas.
  Usar P(x)   para x es portero
       D(x)   para x es delantero europeo 
       N(x)   para x viste camiseta negra
       B(x)   para x juega con botas blancas 
       M(x,y) para x marcó un gol a y
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_17a:
  assumes "\<forall>x. P(x) \<and> \<not>N(x) \<longrightarrow> (\<exists>y. D(y) \<and> M(y,x))"
          "\<exists>x. P(x) \<and> B(x) \<and> (\<forall>y. M(y,x) \<longrightarrow> B(y))"
          "\<not>(\<exists>x. P(x) \<and> M(x,x))"
          "\<not>(\<exists>x. B(x) \<and> N(x))"
  shows   "\<exists>x. D(x) \<and> B(x)"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_17b:
  assumes "\<forall>x. P(x) \<and> \<not>N(x) \<longrightarrow> (\<exists>y. D(y) \<and> M(y,x))"
          "\<exists>x. P(x) \<and> B(x) \<and> (\<forall>y. M(y,x) \<longrightarrow> B(y))"
          "\<not>(\<exists>x. P(x) \<and> M(x,x))"
          "\<not>(\<exists>x. B(x) \<and> N(x))"
  shows   "\<exists>x. D(x) \<and> B(x)"
proof -
  obtain a where a: "P(a) \<and> B(a) \<and> (\<forall>y. M(y,a) \<longrightarrow> B(y))"
    using assms(2) ..
  have "P(a) \<and> \<not>N(a)" 
  proof 
    show "P(a)" using a ..
  next
    have "B(a) \<and> (\<forall>y. M(y,a) \<longrightarrow> B(y))" using a ..
    then have "B(a)" ..
    have "\<forall>x. \<not>(B(x) \<and> N(x))" using assms(4) by (rule no_ex)
    then have "\<not>(B(a) \<and> N(a))" ..
    show "\<not>N(a)"
    proof
      assume "N(a)"
      with \<open>B(a)\<close> have "B(a) \<and> N(a)" .. 
      with \<open>\<not>(B(a) \<and> N(a))\<close> show False ..
    qed
  qed
  then have "\<exists>y. D(y) \<and> M(y,a)" 
  proof -
    have "P(a) \<and> \<not>N(a) \<longrightarrow> (\<exists>y. D(y) \<and> M(y,a))" using assms(1) ..
    then show "\<exists>y. D(y) \<and> M(y,a)" using \<open>P(a) \<and> \<not>N(a)\<close> ..
  qed
  then obtain b where "D(b) \<and> M(b,a)" ..
  have "D(b) \<and> B(b)" 
  proof
    show "D(b)" using \<open>D(b) \<and> M(b,a)\<close> ..
  next
    have "M(b,a)" using \<open>D(b) \<and> M(b,a)\<close> ..
    have "B(a) \<and> (\<forall>y. M(y,a) \<longrightarrow> B(y))" using a ..
    then have "\<forall>y. M(y,a) \<longrightarrow> B(y)" ..
    then have "M(b,a) \<longrightarrow> B(b)" ..
    then show "B(b)" using \<open>M(b,a)\<close> ..
  qed
  then show "\<exists>x. D(x) \<and> B(x)" ..
qed

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_17c:
  assumes "\<forall>x. P(x) \<and> \<not>N(x) \<longrightarrow> (\<exists>y. D(y) \<and> M(y,x))"
          "\<exists>x. P(x) \<and> B(x) \<and> (\<forall>y. M(y,x) \<longrightarrow> B(y))"
          "\<not>(\<exists>x. P(x) \<and> M(x,x))"
          "\<not>(\<exists>x. B(x) \<and> N(x))"
  shows   "\<exists>x. D(x) \<and> B(x)"
proof -
  obtain a where a: "P(a) \<and> B(a) \<and> (\<forall>y. M(y,a) \<longrightarrow> B(y))"
    using assms(2) by (rule exE)
  have "P(a) \<and> \<not>N(a)" 
  proof (rule conjI)
    show "P(a)" using a by (rule conjunct1)
  next
    have "B(a) \<and> (\<forall>y. M(y,a) \<longrightarrow> B(y))" using a by (rule conjunct2)
    then have "B(a)" by (rule conjunct1)
    have "\<forall>x. \<not>(B(x) \<and> N(x))" using assms(4) by (rule no_ex)
    then have "\<not>(B(a) \<and> N(a))" by (rule allE)
    show "\<not>N(a)"
    proof (rule notI)
      assume "N(a)"
      with \<open>B(a)\<close> have "B(a) \<and> N(a)" by (rule conjI) 
      with \<open>\<not>(B(a) \<and> N(a))\<close> show False by (rule notE)
    qed
  qed
  then have "\<exists>y. D(y) \<and> M(y,a)" 
  proof -
    have "P(a) \<and> \<not>N(a) \<longrightarrow> (\<exists>y. D(y) \<and> M(y,a))" 
      using assms(1) by (rule allE)
    then show "\<exists>y. D(y) \<and> M(y,a)" using \<open>P(a) \<and> \<not>N(a)\<close> by (rule mp)
  qed
  then obtain b where "D(b) \<and> M(b,a)" by (rule exE)
  have "D(b) \<and> B(b)" 
  proof (rule conjI)
    show "D(b)" using \<open>D(b) \<and> M(b,a)\<close> by (rule conjunct1)
  next
    have "M(b,a)" using \<open>D(b) \<and> M(b,a)\<close> by (rule conjunct2)
    have "B(a) \<and> (\<forall>y. M(y,a) \<longrightarrow> B(y))" using a by (rule conjunct2)
    then have "\<forall>y. M(y,a) \<longrightarrow> B(y)" by (rule conjunct2)
    then have "M(b,a) \<longrightarrow> B(b)" by (rule allE)
    then show "B(b)" using \<open>M(b,a)\<close> by (rule mp)
  qed
  then show "\<exists>x. D(x) \<and> B(x)" by (rule exI) 
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 18. Formalizar, y decidir la corrección, del siguiente
  argumento 
     Las relaciones de parentesco verifican la siguientes propiedades
     generales:  
     * Si x es hermano de y, entonces y es hermano de x. 
     * Todo el mundo es hijo de alguien. 
     * Nadie es hijo del hermano de su padre. 
     * Cualquier padre de una persona es también padre de todos los
       hermanos de esa persona. 
     * Nadie es hijo ni hermano de sí mismo. 
     Tenemos los siguientes miembros de la familia Peláez: Don Antonio,
     Don Luis, Antoñito y Manolito y sabemos que Don Antonio y Don Luis
     son hermanos, Antoñito y Manolito son hermanos, y Antoñito es hijo
     de Don Antonio. Por tanto, Don Luis no es el padre de Manolito.
  Usar A       para Don Antonio
       He(x,y) para x es hermano de y 
       Hi(x,y) para x es hijo de y  
       L       para Don Luis
       a       para Antoñito
       m       para Manolito
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_18a:
  assumes "\<forall>x y. He(x,y) \<longrightarrow> He(y,x)"
          "\<forall>x. \<exists>y. Hi(x,y)"
          "\<forall>x y z. Hi(x,y) \<and> He(z,y) \<longrightarrow> \<not>Hi(x,z)"
          "\<forall>x y. Hi(x,y) \<longrightarrow> (\<forall>z. He(z,x) \<longrightarrow> Hi(z,y))"
          "\<forall>x. \<not>Hi(x,x) \<and> \<not>He(x,x)"
          "He(A,L)"
          "He(a,m)"
          "Hi(a,A)"
  shows   "\<not>Hi(m,L)"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_18b:
  assumes "\<forall>x y. He(x,y) \<longrightarrow> He(y,x)"                  
          "\<forall>x. \<exists>y. Hi(x,y)"                          
          "\<forall>x y z. Hi(x,y) \<and> He(z,y) \<longrightarrow> \<not>Hi(x,z)"
          "\<forall>x y. Hi(x,y) \<longrightarrow> (\<forall>z. He(z,x) \<longrightarrow> Hi(z,y))"
          "\<forall>x. \<not>Hi(x,x) \<and> \<not>He(x,x)"
          "He(A,L)"
          "He(a,m)"
          "Hi(a,A)"
  shows   "\<not>Hi(m,L)"
proof
  assume "Hi(m,L)"
  have "He(L,A)"
  proof -
    have "\<forall>y. He(A,y) \<longrightarrow> He(y,A)" using assms(1) ..
    then have "He(A,L) \<longrightarrow> He(L,A)" ..
    then show "He(L,A)" using assms(6) ..
  qed
  have "Hi(a,L)"
  proof -
    have "\<forall>y. Hi(m,y) \<longrightarrow> (\<forall>z. He(z,m) \<longrightarrow> Hi(z,y))" using assms(4) ..
    then have "Hi(m,L) \<longrightarrow> (\<forall>z. He(z,m) \<longrightarrow> Hi(z,L))" ..
    then have "\<forall>z. He(z,m) \<longrightarrow> Hi(z,L)" using \<open>Hi(m,L)\<close> ..
    then have "He(a,m) \<longrightarrow> Hi(a,L)" ..
    then show "Hi(a,L)" using assms(7) ..
  qed 
  have "\<not>Hi(a,L)"
  proof -
    have "Hi(a,A) \<and> He(L,A)" using assms(8) \<open>He(L,A)\<close> .. 
    have "\<forall>y z. Hi(a,y) \<and> He(z,y) \<longrightarrow> \<not>Hi(a,z)" using assms(3) ..
    then have "\<forall>z. Hi(a,A) \<and> He(z,A) \<longrightarrow> \<not>Hi(a,z)" ..
    then have "Hi(a,A) \<and> He(L,A) \<longrightarrow> \<not>Hi(a,L)" ..
    then show "\<not>Hi(a,L)" using \<open>Hi(a,A) \<and> He(L,A)\<close> ..
  qed
  then show False using \<open>Hi(a,L)\<close> ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_18c:
  assumes "\<forall>x y. He(x,y) \<longrightarrow> He(y,x)"                  
          "\<forall>x. \<exists>y. Hi(x,y)"                          
          "\<forall>x y z. Hi(x,y) \<and> He(z,y) \<longrightarrow> \<not>Hi(x,z)"
          "\<forall>x y. Hi(x,y) \<longrightarrow> (\<forall>z. He(z,x) \<longrightarrow> Hi(z,y))"
          "\<forall>x. \<not>Hi(x,x) \<and> \<not>He(x,x)"
          "He(A,L)"
          "He(a,m)"
          "Hi(a,A)"
  shows   "\<not>Hi(m,L)"
proof (rule notI)
  assume "Hi(m,L)"
  have "He(L,A)"
  proof -
    have "\<forall>y. He(A,y) \<longrightarrow> He(y,A)" using assms(1) by (rule allE)
    then have "He(A,L) \<longrightarrow> He(L,A)" by (rule allE)
    then show "He(L,A)" using assms(6) by (rule mp)
  qed
  have "Hi(a,L)"
  proof -
    have "\<forall>y. Hi(m,y) \<longrightarrow> (\<forall>z. He(z,m) \<longrightarrow> Hi(z,y))" 
      using assms(4) by (rule allE)
    then have "Hi(m,L) \<longrightarrow> (\<forall>z. He(z,m) \<longrightarrow> Hi(z,L))" by (rule allE)
    then have "\<forall>z. He(z,m) \<longrightarrow> Hi(z,L)" using \<open>Hi(m,L)\<close> by (rule mp)
    then have "He(a,m) \<longrightarrow> Hi(a,L)" by (rule allE)
    then show "Hi(a,L)" using assms(7) by (rule mp)
  qed 
  have "\<not>Hi(a,L)"
  proof -
    have "Hi(a,A) \<and> He(L,A)" using assms(8) \<open>He(L,A)\<close> by (rule conjI) 
    have "\<forall>y z. Hi(a,y) \<and> He(z,y) \<longrightarrow> \<not>Hi(a,z)" 
      using assms(3) by (rule allE)
    then have "\<forall>z. Hi(a,A) \<and> He(z,A) \<longrightarrow> \<not>Hi(a,z)" by (rule allE)
    then have "Hi(a,A) \<and> He(L,A) \<longrightarrow> \<not>Hi(a,L)" by (rule allE)
    then show "\<not>Hi(a,L)" using \<open>Hi(a,A) \<and> He(L,A)\<close> by (rule mp)
  qed
  then show False using \<open>Hi(a,L)\<close> by (rule notE)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 19. [Problema del apisonador de Schubert (en inglés, 
  "Schubert’s steamroller")] Formalizar, y decidir la corrección, del
  siguiente argumento 
     Si uno de los miembros del club afeita a algún otro (incluido a
     sí mismo), entonces todos los miembros del club lo han afeitado
     a él (aunque no necesariamente al mismo tiempo). Guido, Lorenzo,
     Petruccio y Cesare pertenecen al club de barberos. Guido ha
     afeitado a Cesare. Por tanto, Petruccio ha afeitado a Lorenzo.
  Usar g      para Guido
       l      para Lorenzo
       p      para Petruccio
       c      para Cesare
       B(x)   para x es un miembro del club de barberos
       A(x,y) para x ha afeitado a y
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_19a:
  assumes "\<forall>x. B(x) \<and> (\<exists>y. B(y) \<and> A(x,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,x))"
          "B(g)" 
          "B(l)" 
          "B(p)" 
          "B(c)"
          "A(g,c)"
  shows   "A(p,l)"
using assms
by meson

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_19b:
  assumes "\<forall>x. B(x) \<and> (\<exists>y. B(y) \<and> A(x,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,x))"
          "B(g)" 
          "B(l)" 
          "B(p)" 
          "B(c)"
          "A(g,c)"
  shows   "A(p,l)"
proof -
  have "A(l,g)"
  proof -
    have "B(g) \<and> (\<exists>y. B(y) \<and> A(g,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,g))" 
      using assms(1) ..
    have "B(c) \<and> A(g,c)" using assms(5,6) ..
    then have "(\<exists>y. B(y) \<and> A(g,y))" ..
    with assms(2) have "B(g) \<and> (\<exists>y. B(y) \<and> A(g,y))" .. 
    with \<open>B(g) \<and> (\<exists>y. B(y) \<and> A(g,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,g))\<close> 
    have "(\<forall>z. B(z) \<longrightarrow> A(z,g))" ..
    then have "B(l) \<longrightarrow> A(l,g)" ..
    then show "A(l,g)" using assms(3) ..
  qed
  have "B(l) \<and> (\<exists>y. B(y) \<and> A(l,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,l))" 
    using assms(1) ..
  have "B(g) \<and> A(l,g)" using assms(2) \<open>A(l,g)\<close> ..
  then have "(\<exists>y. B(y) \<and> A(l,y))" ..
  with assms(3) have "B(l) \<and> (\<exists>y. B(y) \<and> A(l,y))" .. 
  with \<open>B(l) \<and> (\<exists>y. B(y) \<and> A(l,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,l))\<close> 
  have "(\<forall>z. B(z) \<longrightarrow> A(z,l))" ..
  then have "B(p) \<longrightarrow> A(p,l)" ..
  then show "A(p,l)" using assms(4) ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_19c:
  assumes "\<forall>x. B(x) \<and> (\<exists>y. B(y) \<and> A(x,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,x))"
          "B(g)" 
          "B(l)" 
          "B(p)" 
          "B(c)"
          "A(g,c)"
  shows   "A(p,l)"
proof -
  have "A(l,g)"
  proof -
    have "B(g) \<and> (\<exists>y. B(y) \<and> A(g,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,g))" 
      using assms(1) by (rule allE)
    have "B(c) \<and> A(g,c)" using assms(5,6) by (rule conjI)
    then have "(\<exists>y. B(y) \<and> A(g,y))" by (rule exI)
    with assms(2) have "B(g) \<and> (\<exists>y. B(y) \<and> A(g,y))" by (rule conjI) 
    with \<open>B(g) \<and> (\<exists>y. B(y) \<and> A(g,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,g))\<close> 
    have "(\<forall>z. B(z) \<longrightarrow> A(z,g))" by (rule mp)
    then have "B(l) \<longrightarrow> A(l,g)" by (rule allE)
    then show "A(l,g)" using assms(3) by (rule mp)
  qed
  have "B(l) \<and> (\<exists>y. B(y) \<and> A(l,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,l))" 
    using assms(1) by (rule allE)
  have "B(g) \<and> A(l,g)" using assms(2) \<open>A(l,g)\<close> by (rule conjI)
  then have "(\<exists>y. B(y) \<and> A(l,y))" by (rule exI)
  with assms(3) have "B(l) \<and> (\<exists>y. B(y) \<and> A(l,y))" by (rule conjI) 
  with \<open>B(l) \<and> (\<exists>y. B(y) \<and> A(l,y)) \<longrightarrow> (\<forall>z. B(z) \<longrightarrow> A(z,l))\<close> 
  have "(\<forall>z. B(z) \<longrightarrow> A(z,l))" by (rule mp)
  then have "B(p) \<longrightarrow> A(p,l)" by (rule allE)
  then show "A(p,l)" using assms(4) by (rule mp)
qed

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
lemma ejercicio_20a:
  assumes "\<forall>x. A(c,x) \<longleftrightarrow> C(x) \<and> \<not>A(x,x)"
          "C(c)"
  shows   "\<not>(\<exists>x. A(c,x))"
using assms
by blast

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_20b:
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
lemma ejercicio_20c:
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

text \<open>--------------------------------------------------------------- 
  Ejercicio 21. Formalizar, y decidir la corrección, del siguiente
  argumento
     Quien desprecia a todos los fanáticos desprecia también a todos los
     políticos. Alguien no desprecia a un determinado político. Por
     consiguiente, hay un fanático al que no todo el mundo desprecia.
   Usar D(x,y) para x desprecia a y
        F(x)   para x es fanático
        P(x)   para x es político
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_21a:
  assumes "\<forall>x. (\<forall>y. F(y) \<longrightarrow> D(x,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(x,y))"
          "\<exists>x y. P(y) \<and> \<not>D(x,y)"
  shows   "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))"
using assms
by blast

\<comment> \<open>La demostración semiautomática es\<close>
lemma ejercicio_21b:
  assumes "\<forall>x. (\<forall>y. F(y) \<longrightarrow> D(x,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(x,y))"
          "\<exists>x y. P(y) \<and> \<not>D(x,y)"
  shows   "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))"
proof -
  obtain a where "\<exists>y. P(y) \<and> \<not>D(a,y)" using assms(2) ..
  then obtain b where "P(b) \<and> \<not>D(a,b)" ..
  then have "\<not>(\<forall>y. P(y) \<longrightarrow> D(a,y))" by auto
  have "(\<forall>y. F(y) \<longrightarrow> D(a,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(a,y))" using assms(1) ..
  then have "\<not>(\<forall>y. F(y) \<longrightarrow> D(a,y))" using \<open>\<not>(\<forall>y. P(y) \<longrightarrow> D(a,y))\<close> by (rule mt)
  then have "\<exists>y. \<not>(F(y) \<longrightarrow> D(a,y))" by (rule no_para_todo)  
  then obtain c where "\<not>(F(c) \<longrightarrow> D(a,c))" ..
  then have "F(c) \<and> \<not>(\<forall>y. D(y,c))" by auto
  then show "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))" ..
qed

\<comment> \<open>En la demostración estructurada usaremos el siguiente lema\<close>
lemma no_implica: 
  assumes "\<not>(p \<longrightarrow> q)"
  shows   "p \<and> \<not>q"
using assms
by auto

\<comment> \<open>La demostración estructurada del lema es\<close>
lemma no_implica_1: 
  assumes "\<not>(p \<longrightarrow> q)"
  shows   "p \<and> \<not>q"
proof
  show "p"
  proof (rule ccontr)
    assume "\<not>p"
    have "p \<longrightarrow> q"
    proof
      assume "p"
      with \<open>\<not>p\<close> show "q" .. 
    qed
    with assms show False ..
  qed
next
  show "\<not>q"
  proof
    assume "q"
    have "p \<longrightarrow> q"
    proof
      assume "p"
      show "q" using \<open>q\<close> .
    qed
    with assms show False ..
  qed
qed

\<comment> \<open>La demostración detallada del lema es\<close>
lemma no_implica_2: 
  assumes "\<not>(p \<longrightarrow> q)"
  shows   "p \<and> \<not>q"
proof (rule conjI)
  show "p"
  proof (rule ccontr)
    assume "\<not>p"
    have "p \<longrightarrow> q"
    proof (rule impI)
      assume "p"
      with \<open>\<not>p\<close> show "q" by (rule notE) 
    qed
    with assms show False by (rule notE) 
  qed
next
  show "\<not>q"
  proof (rule notI)
    assume "q"
    have "p \<longrightarrow> q"
    proof (rule impI)
      assume "p"
      show "q" using \<open>q\<close> by this
    qed
    with assms show False by (rule notE)
  qed
qed

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_21c:
  assumes "\<forall>x. (\<forall>y. F(y) \<longrightarrow> D(x,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(x,y))"
          "\<exists>x y. P(y) \<and> \<not>D(x,y)"
  shows   "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))"
proof -
  obtain a where "\<exists>y. P(y) \<and> \<not>D(a,y)" using assms(2) ..
  then obtain b where b: "P(b) \<and> \<not>D(a,b)" ..
  have "\<not>(\<forall>y. P(y) \<longrightarrow> D(a,y))"
  proof
    assume "\<forall>y. P(y) \<longrightarrow> D(a,y)"
    then have "P(b) \<longrightarrow> D(a,b)" ..
    have "P(b)" using b ..
    with \<open>P(b) \<longrightarrow> D(a,b)\<close> have "D(a,b)" ..
    have "\<not>D(a,b)" using b ..
    then show False using \<open>D(a,b)\<close> ..
  qed
  have "(\<forall>y. F(y) \<longrightarrow> D(a,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(a,y))" using assms(1) ..
  then have "\<not>(\<forall>y. F(y) \<longrightarrow> D(a,y))" using \<open>\<not>(\<forall>y. P(y) \<longrightarrow> D(a,y))\<close> by (rule mt)
  then have "\<exists>y. \<not>(F(y) \<longrightarrow> D(a,y))" by (rule no_para_todo)  
  then obtain c where c: "\<not>(F(c) \<longrightarrow> D(a,c))" ..
  have "F(c) \<and> \<not>(\<forall>y. D(y,c))" 
  proof
    have "F(c) \<and> \<not>D(a,c)" using c by (rule no_implica)
    then show "F(c)" ..
  next
    show "\<not>(\<forall>y. D(y,c))"
    proof
      assume "\<forall>y. D(y,c)"
      then have "D(a,c)" ..
      have "F(c) \<and> \<not>D(a,c)" using c by (rule no_implica)
      then have "\<not>D(a,c)" ..
      then show False using \<open>D(a,c)\<close> ..
    qed
  qed
  then show "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))" ..
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_21d:
  assumes "\<forall>x. (\<forall>y. F(y) \<longrightarrow> D(x,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(x,y))"
          "\<exists>x y. P(y) \<and> \<not>D(x,y)"
  shows   "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))"
proof -
  obtain a where "\<exists>y. P(y) \<and> \<not>D(a,y)" using assms(2) by (rule exE)
  then obtain b where b: "P(b) \<and> \<not>D(a,b)" by (rule exE)
  have "\<not>(\<forall>y. P(y) \<longrightarrow> D(a,y))"
  proof (rule notI)
    assume "\<forall>y. P(y) \<longrightarrow> D(a,y)"
    then have "P(b) \<longrightarrow> D(a,b)" by (rule allE)
    have "P(b)" using b by (rule conjunct1)
    with \<open>P(b) \<longrightarrow> D(a,b)\<close> have "D(a,b)" by (rule mp)
    have "\<not>D(a,b)" using b by (rule conjunct2)
    then show False using \<open>D(a,b)\<close> by (rule notE)
  qed
  have "(\<forall>y. F(y) \<longrightarrow> D(a,y)) \<longrightarrow>  (\<forall>y. P(y) \<longrightarrow> D(a,y))" 
    using assms(1) by (rule allE)
  then have "\<not>(\<forall>y. F(y) \<longrightarrow> D(a,y))" using \<open>\<not>(\<forall>y. P(y) \<longrightarrow> D(a,y))\<close> by (rule mt)
  then have "\<exists>y. \<not>(F(y) \<longrightarrow> D(a,y))" by (rule no_para_todo)  
  then obtain c where c: "\<not>(F(c) \<longrightarrow> D(a,c))" by (rule exE)
  have "F(c) \<and> \<not>(\<forall>y. D(y,c))" 
  proof (rule conjI)
    have "F(c) \<and> \<not>D(a,c)" using c by (rule no_implica)
    then show "F(c)" by (rule conjunct1)
  next
    show "\<not>(\<forall>y. D(y,c))"
    proof (rule notI)
      assume "\<forall>y. D(y,c)"
      then have "D(a,c)" by (rule allE)
      have "F(c) \<and> \<not>D(a,c)" using c by (rule no_implica)
      then have "\<not>D(a,c)" by (rule conjunct2)
      then show False using \<open>D(a,c)\<close> by (rule notE)
    qed
  qed
  then show "\<exists>x. F(x) \<and> \<not>(\<forall>y. D(y,x))" by (rule exI)
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 22. Formalizar, y decidir la corrección, del siguiente
  argumento
     El hombre puro ama todo lo que es puro. Por tanto, el hombre puro
     se ama a sí mismo.
  Usar A(x,y) para x ama a y
       H(x)   para x es un hombre
       P(x)   para x es puro
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_22a:
  assumes "\<forall>x. H(x) \<and> P(x) \<longrightarrow> (\<forall>y. P(y) \<longrightarrow> A(x,y))"
  shows   "\<forall>x. H(x) \<and> P(x) \<longrightarrow> A(x,x)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_22b:
  assumes "\<forall>x. H(x) \<and> P(x) \<longrightarrow> (\<forall>y. P(y) \<longrightarrow> A(x,y))"
  shows   "\<forall>x. H(x) \<and> P(x) \<longrightarrow> A(x,x)"
proof
  fix b
  show "H(b) \<and> P(b) \<longrightarrow> A(b,b)"
  proof
    assume "H(b) \<and> P(b)"
    then have "P(b)" ..
    have "H(b) \<and> P(b) \<longrightarrow> (\<forall>y. P(y) \<longrightarrow> A(b,y))" using assms ..
    then have "\<forall>y. P(y) \<longrightarrow> A(b,y)" using \<open>H(b) \<and> P(b)\<close> ..
    then have "P(b) \<longrightarrow> A(b,b)" ..
    then show "A(b,b)" using \<open>P(b)\<close> ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_22c:
  assumes "\<forall>x. H(x) \<and> P(x) \<longrightarrow> (\<forall>y. P(y) \<longrightarrow> A(x,y))"
  shows   "\<forall>x. H(x) \<and> P(x) \<longrightarrow> A(x,x)"
proof (rule allI)
  fix b
  show "H(b) \<and> P(b) \<longrightarrow> A(b,b)"
  proof (rule impI)
    assume "H(b) \<and> P(b)"
    then have "P(b)" by (rule conjunct2)
    have "H(b) \<and> P(b) \<longrightarrow> (\<forall>y. P(y) \<longrightarrow> A(b,y))" 
      using assms by (rule allE)
    then have "\<forall>y. P(y) \<longrightarrow> A(b,y)" using \<open>H(b) \<and> P(b)\<close> by (rule mp)
    then have "P(b) \<longrightarrow> A(b,b)" by (rule allE)
    then show "A(b,b)" using \<open>P(b)\<close> by (rule mp)
  qed
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 23. Formalizar, y decidir la corrección, del siguiente
  argumento
     Ningún socio del club está en deuda con el tesorero del club. Si
     un socio del club no paga su cuota está en deuda con el tesorero
     del club. Por tanto, si el tesorero del club es socio del club,
     entonces paga su cuota. 
  Usar P(x) para x es socio del club
       Q(x) para x paga su cuota
       R(x) para x está en deuda con el tesorero
       a    para el tesorero del club
   ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_23a:
  assumes "\<not>(\<exists>x. P(x) \<and> R(x))"
          "\<forall>x. P(x) \<and> \<not>Q(x) \<longrightarrow> R(x)"
  shows   "P(a) \<longrightarrow> Q(a)"
using assms
by auto

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_23b:
  assumes "\<not>(\<exists>x. P(x) \<and> R(x))"
          "\<forall>x. P(x) \<and> \<not>Q(x) \<longrightarrow> R(x)"
  shows   "P(a) \<longrightarrow> Q(a)"
proof
  assume "P(a)"
  show "Q(a)"
  proof (rule ccontr)
    assume "\<not>Q(a)"
    with \<open>P(a)\<close> have "P(a) \<and> \<not>Q(a)" ..
    have "P(a) \<and> \<not>Q(a) \<longrightarrow> R(a)" using assms(2) ..
    then have "R(a)" using \<open>P(a) \<and> \<not>Q(a)\<close> ..
    with \<open>P(a)\<close> have "P(a) \<and> R(a)" ..
    then have "\<exists>x. P(x) \<and> R(x)" ..
    with assms(1) show False ..
  qed
qed

\<comment> \<open>La demostración detallada es\<close>
lemma ejercicio_23c:
  assumes "\<not>(\<exists>x. P(x) \<and> R(x))"
          "\<forall>x. P(x) \<and> \<not>Q(x) \<longrightarrow> R(x)"
  shows   "P(a) \<longrightarrow> Q(a)"
proof (rule impI)
  assume "P(a)"
  show "Q(a)"
  proof (rule ccontr)
    assume "\<not>Q(a)"
    with \<open>P(a)\<close> have "P(a) \<and> \<not>Q(a)" by (rule conjI)
    have "P(a) \<and> \<not>Q(a) \<longrightarrow> R(a)" using assms(2) by (rule allE)
    then have "R(a)" using \<open>P(a) \<and> \<not>Q(a)\<close> by (rule mp)
    with \<open>P(a)\<close> have "P(a) \<and> R(a)" by (rule conjI)
    then have "\<exists>x. P(x) \<and> R(x)" by (rule exI)
    with assms(1) show False by (rule notE)
  qed
qed

text \<open>--------------------------------------------------------------- 
  Ejercicio 24. Formalizar, y decidir la corrección, del siguiente
  argumento
     1. Los lobos, zorros, pájaros, orugas y caracoles son animales y
        existen algunos ejemplares de estos animales. 
     2. También hay algunas semillas y las semillas son plantas. 
     3. A todo animal le gusta o bien comer todo tipo de plantas o bien
        le gusta comerse a todos los animales más pequeños que él mismo
        que gustan de comer algunas plantas. 
     4. Las orugas y los caracoles son mucho más pequeños que los
        pájaros, que son mucho más pequeños que los zorros que a su vez
        son mucho más pequeños que los lobos. 
     5. A los lobos no les gusta comer ni zorros ni semillas, mientras
        que a los pájaros les gusta comer orugas pero no caracoles. 
     6. Las orugas y los caracoles gustan de comer algunas plantas. 
     7. Luego, existe un animal al que le gusta comerse un animal al que
        le gusta comer semillas.  
  Usar A(x)    para x es un animal
       Ca(x)   para x es un caracol
       Co(x,y) para x le gusta comerse a y
       L(x)    para x es un lobo
       M(x,y)  para x es más pequeño que y
       Or(x)   para x es una oruga
       Pa(x)   para x es un pájaro
       Pl(x)   para x es una planta
       S(x)    para x es una semilla
       Z(x)    para x es un zorro
  ------------------------------------------------------------------\<close>

\<comment> \<open>La demostración automática es\<close>
lemma ejercicio_24a:
  assumes
   (*  1 *) "\<forall>x. L(x) \<longrightarrow> A(x)"
   (*  2 *) "\<forall>x. Z(x) \<longrightarrow> A(x)"
   (*  3 *) "\<forall>x. Pa(x) \<longrightarrow> A(x)"
   (*  4 *) "\<forall>x. Or(x) \<longrightarrow> A(x)"
   (*  5 *) "\<forall>x. Ca(x) \<longrightarrow> A(x)"
   (*  6 *) "\<exists>x. L(x)"
   (*  7 *) "\<exists>x. Z(x)"
   (*  8 *) "\<exists>x. Pa(x)"
   (*  9 *) "\<exists>x. Or(x)"
   (* 10 *) "\<exists>x. Ca(x)"
   (* 11 *) "\<exists>x. S(x)"
   (* 12 *) "\<forall>x. S(x) \<longrightarrow> Pl(x)"
   (* 13 *) "\<forall>x. A(x) \<longrightarrow> 
                 (\<forall>y. Pl(y) \<longrightarrow> Co(x,y)) \<or> 
                 (\<forall>y. A(y) \<and> M(y,x) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(x,y))"
   (* 14 *) "\<forall>x y. Pa(y) \<and> (Ca(x) \<or> Or(x)) \<longrightarrow> M(x,y)"
   (* 15 *) "\<forall>x y. Pa(x) \<and> Z(y) \<longrightarrow> M(x,y)"
   (* 16 *) "\<forall>x y. Z(x) \<and> L(y) \<longrightarrow> M(x,y)"
   (* 17 *) "\<forall>x y. L(x) \<and> (Z(y)\<or> S(y)) \<longrightarrow> \<not>Co(x,y)"
   (* 18 *) "\<forall>x y. Pa(x) \<and> Or(y) \<longrightarrow> Co(x,y)"
   (* 19 *) "\<forall>x y. Pa(x) \<and> Ca(y) \<longrightarrow> \<not>Co(x,y)"
   (* 20 *) "\<forall>x. Or(x) \<or> Ca(x) \<longrightarrow> (\<exists>y. Pl(y) \<and> Co(x,y))"
  shows
   "\<exists>x y. A(x) \<and> A(y) \<and> (\<exists>z. S(z) \<and> Co(y,z) \<and> Co(x,y))"
using assms
by meson

\<comment> \<open>La demostración semiautomática es\<close>
lemma ejercicio_24b:
  assumes
   (*  1 *) "\<forall>x. L(x) \<longrightarrow> A(x)"
   (*  2 *) "\<forall>x. Z(x) \<longrightarrow> A(x)"
   (*  3 *) "\<forall>x. Pa(x) \<longrightarrow> A(x)"
   (*  4 *) "\<forall>x. Or(x) \<longrightarrow> A(x)"
   (*  5 *) "\<forall>x. Ca(x) \<longrightarrow> A(x)"
   (*  6 *) "\<exists>x. L(x)"
   (*  7 *) "\<exists>x. Z(x)"
   (*  8 *) "\<exists>x. Pa(x)"
   (*  9 *) "\<exists>x. Or(x)"
   (* 10 *) "\<exists>x. Ca(x)"
   (* 11 *) "\<exists>x. S(x)"
   (* 12 *) "\<forall>x. S(x) \<longrightarrow> Pl(x)"
   (* 13 *) "\<forall>x. A(x) \<longrightarrow> 
                 (\<forall>y. Pl(y) \<longrightarrow> Co(x,y)) \<or> 
                 (\<forall>y. A(y) \<and> M(y,x) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(x,y))"
   (* 14 *) "\<forall>x y. Pa(y) \<and> (Ca(x) \<or> Or(x)) \<longrightarrow> M(x,y)"
   (* 15 *) "\<forall>x y. Pa(x) \<and> Z(y) \<longrightarrow> M(x,y)"
   (* 16 *) "\<forall>x y. Z(x) \<and> L(y) \<longrightarrow> M(x,y)"
   (* 17 *) "\<forall>x y. L(x) \<and> (Z(y)\<or> S(y)) \<longrightarrow> \<not>Co(x,y)"
   (* 18 *) "\<forall>x y. Pa(x) \<and> Or(y) \<longrightarrow> Co(x,y)"
   (* 19 *) "\<forall>x y. Pa(x) \<and> Ca(y) \<longrightarrow> \<not>Co(x,y)"
   (* 20 *) "\<forall>x. Or(x) \<or> Ca(x) \<longrightarrow> (\<exists>y. Pl(y) \<and> Co(x,y))"
  shows
   "\<exists>x y. A(x) \<and> A(y) \<and> (\<exists>z. S(z) \<and> Co(y,z) \<and> Co(x,y))"
proof -
  obtain l where l: "L(l)" using assms(6) ..
  obtain z where z: "Z(z)" using assms(7) ..
  obtain p where p: "Pa(p)" using assms(8) ..
  obtain c where c: "Ca(c)" using assms(10) ..
  obtain s where s: "S(s)" using assms(11) ..
  have 1: "Co(p,s)" using p c s assms(3,5,12,13,14,19,20) by meson
  have 2: "\<not>Co(z,s)" using z l s assms(1,2,12,16,17,13) by meson 
  have 3: "M(p,z)" using p z assms(15) by auto
  have 4: "Co(z,p)" using z p s 1 2 3 assms(2,3,12,13) by meson
  then have "Co(z,p) \<and> Co(p,s)" using 1 .. 
  then show "\<exists>x y. A(x) \<and> A(y) \<and> (\<exists>z. S(z) \<and> Co(y,z) \<and> Co(x,y))" 
    using z p s assms(2,3) by meson
qed

lemma instancia:
  assumes "\<forall>x. P(x) \<longrightarrow> Q(x)"
          "P(a)"
  shows   "Q(a)"
proof -
  have "P(a) \<longrightarrow> Q(a)" using assms(1) ..
  then show "Q(a)" using assms(2) ..
qed

lemma mt2:
  assumes "p \<and> q \<and> r \<longrightarrow> s"
          "p"
          "q"
          "\<not>s"
  shows   "\<not>r"
proof
  assume "r"
  with \<open>q\<close> have "q \<and> r" ..
  with \<open>p\<close> have "p \<and> q \<and> r" ..
  with assms(1) have "s" ..
  with \<open>\<not>s\<close> show False ..
qed

lemma mp3: 
  assumes "p \<and> q \<and> r \<longrightarrow> s"
          "p"
          "q"
          "r"
  shows   "s"
proof -
  have "q \<and> r" using assms(3,4) ..
  with \<open>p\<close> have "p \<and> q \<and> r" ..
  with assms(1) show "s" ..
qed

lemma conjI3:
  assumes "p"
          "q"
          "r"
  shows   "p \<and> q \<and> r"
proof -
  have "q \<and> r" using assms(2,3) ..
  with \<open>p\<close> show "p \<and> q \<and> r" ..
qed

\<comment> \<open>La demostración estructurada es\<close>
lemma ejercicio_24c:
  assumes
   (*  1 *) "\<forall>x. L(x) \<longrightarrow> A(x)"
   (*  2 *) "\<forall>x. Z(x) \<longrightarrow> A(x)"
   (*  3 *) "\<forall>x. Pa(x) \<longrightarrow> A(x)"
   (*  4 *) "\<forall>x. Or(x) \<longrightarrow> A(x)"
   (*  5 *) "\<forall>x. Ca(x) \<longrightarrow> A(x)"
   (*  6 *) "\<exists>x. L(x)"
   (*  7 *) "\<exists>x. Z(x)"
   (*  8 *) "\<exists>x. Pa(x)"
   (*  9 *) "\<exists>x. Or(x)"
   (* 10 *) "\<exists>x. Ca(x)"
   (* 11 *) "\<exists>x. S(x)"
   (* 12 *) "\<forall>x. S(x) \<longrightarrow> Pl(x)"
   (* 13 *) "\<forall>x. A(x) \<longrightarrow> 
                 (\<forall>y. Pl(y) \<longrightarrow> Co(x,y)) \<or> 
                 (\<forall>y. A(y) \<and> M(y,x) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(x,y))"
   (* 14 *) "\<forall>x y. Pa(y) \<and> (Ca(x) \<or> Or(x)) \<longrightarrow> M(x,y)"
   (* 15 *) "\<forall>x y. Pa(x) \<and> Z(y) \<longrightarrow> M(x,y)"
   (* 16 *) "\<forall>x y. Z(x) \<and> L(y) \<longrightarrow> M(x,y)"
   (* 17 *) "\<forall>x y. L(x) \<and> (Z(y)\<or> S(y)) \<longrightarrow> \<not>Co(x,y)"
   (* 18 *) "\<forall>x y. Pa(x) \<and> Or(y) \<longrightarrow> Co(x,y)"
   (* 19 *) "\<forall>x y. Pa(x) \<and> Ca(y) \<longrightarrow> \<not>Co(x,y)"
   (* 20 *) "\<forall>x. Or(x) \<or> Ca(x) \<longrightarrow> (\<exists>y. Pl(y) \<and> Co(x,y))"
  shows
   "\<exists>x y. A(x) \<and> A(y) \<and> (\<exists>z. S(z) \<and> Co(y,z) \<and> Co(x,y))"
proof -
  obtain l where l: "L(l)" using assms(6) ..
  obtain z where z: "Z(z)" using assms(7) ..
  obtain p where p: "Pa(p)" using assms(8) ..
  obtain c where c: "Ca(c)" using assms(10) ..
  obtain s where s: "S(s)" using assms(11) ..
  have 1: "Co(p,s)" 
  proof -
    have "\<not>Co(p,c)"
    proof -
      have "Pa(p) \<and> Ca(c)" using p c ..
      have "\<forall>y. Pa(p) \<and> Ca(y) \<longrightarrow> \<not>Co(p,y)" using assms(19) ..
      then have "Pa(p) \<and> Ca(c) \<longrightarrow> \<not>Co(p,c)" ..
      then show "\<not>Co(p,c)" using \<open>Pa(p) \<and> Ca(c)\<close> .. 
    qed
    have "\<exists>y. Pl(y) \<and> Co(c,y)" 
    proof -
      have "Or(c) \<or> Ca(c)" using c ..
      have "Or(c) \<or> Ca(c) \<longrightarrow> (\<exists>y. Pl(y) \<and> Co(c,y))" using assms(20) ..
      then show "\<exists>y. Pl(y) \<and> Co(c,y)" using \<open>Or(c) \<or> Ca(c)\<close> ..
    qed 
    have "M(c,p)"
    proof -
      have "\<forall>y. Pa(y) \<and> (Ca(c) \<or> Or(c)) \<longrightarrow> M(c,y)" using assms(14) ..
      then have "Pa(p) \<and> (Ca(c) \<or> Or(c)) \<longrightarrow> M(c,p)" ..
      have "Ca(c) \<or> Or(c)" using c ..
      with p have "Pa(p) \<and> (Ca(c) \<or> Or(c))" ..
      with \<open>Pa(p) \<and> (Ca(c) \<or> Or(c)) \<longrightarrow> M(c,p)\<close> show "M(c,p)" ..
    qed
    show "Co(p,s)"
    proof -
      have "A(p)" using assms(3) p by (rule instancia)
      have "A(p) \<longrightarrow> (\<forall>y. Pl(y) \<longrightarrow> Co(p,y)) \<or> 
                     (\<forall>y. A(y) \<and> M(y,p) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(p,y))"
        using assms(13) ..
      then have "(\<forall>y. Pl(y) \<longrightarrow> Co(p,y)) \<or> 
             (\<forall>y. A(y) \<and> M(y,p) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(p,y))"
        using \<open>A(p)\<close> ..
      then show "Co(p,s)"
      proof
        assume "\<forall>y. Pl(y) \<longrightarrow> Co(p,y)"
        then have "Pl(s) \<longrightarrow> Co(p,s)" ..
        have "Pl(s)" using assms(12) s by (rule instancia)
        with \<open>Pl(s) \<longrightarrow> Co(p,s)\<close> show "Co(p,s)" ..
      next
        assume "\<forall>y. A(y) \<and> M(y,p) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(p,y)"
        then have "A(c) \<and> M(c,p) \<and> (\<exists>z. Pl(z) \<and> Co(c,z)) \<longrightarrow> Co(p,c)" ..
        have "Co(p,c)"
        proof -
          have "A(c)" using assms(5) c by (rule instancia)
          have "M(c,p) \<and> (\<exists>z. Pl(z) \<and> Co(c,z))" 
            using \<open>M(c,p)\<close> \<open>\<exists>z. Pl(z) \<and> Co(c,z)\<close> ..
          with \<open>A(c)\<close> have "A(c) \<and> M(c,p) \<and> (\<exists>z. Pl(z) \<and> Co(c,z))" ..
          with \<open>A(c) \<and> M(c,p) \<and> (\<exists>z. Pl(z) \<and> Co(c,z)) \<longrightarrow> Co(p,c)\<close>
          show "Co(p,c)" ..
        qed
        with \<open>\<not>Co(p,c)\<close> show "Co(p,s)" ..
      qed
    qed
  qed
  have 2: "\<not>Co(z,s)"
  proof -
    have "M(z,l)"
    proof -
      have "Z(z) \<and> L(l)" using z l ..
      have "\<forall>y. Z(z) \<and> L(y) \<longrightarrow> M(z,y)" using assms(16) ..
      then have "Z(z) \<and> L(l) \<longrightarrow> M(z,l)" ..
      then show "M(z,l)" using \<open>Z(z) \<and> L(l)\<close> ..
    qed
    have "\<not>Co(l,z)" 
    proof -
      have "\<forall>y. L(l) \<and> (Z(y)\<or> S(y)) \<longrightarrow> \<not>Co(l,y)" using assms(17) ..
      then have "L(l) \<and> (Z(z)\<or> S(z)) \<longrightarrow> \<not>Co(l,z)" ..
      have "Z(z)\<or> S(z)" using z ..
      with l have "L(l) \<and> (Z(z)\<or> S(z))" ..
      with \<open>L(l) \<and> (Z(z)\<or> S(z)) \<longrightarrow> \<not>Co(l,z)\<close> show "\<not>Co(l,z)" .. 
    qed
    have "\<not>Co(l,s)"
    proof -
      have "\<forall>y. L(l) \<and> (Z(y)\<or> S(y)) \<longrightarrow> \<not>Co(l,y)" using assms(17) ..
      then have "L(l) \<and> (Z(s)\<or> S(s)) \<longrightarrow> \<not>Co(l,s)" ..
      have "Z(s)\<or> S(s)" using s ..
      with l have "L(l) \<and> (Z(s)\<or> S(s))" ..
      with \<open>L(l) \<and> (Z(s)\<or> S(s)) \<longrightarrow> \<not>Co(l,s)\<close> show "\<not>Co(l,s)" .. 
    qed
    show "\<not>Co(z,s)"
    proof -
      have "A(l)" using assms(1) l by (rule instancia)
      have "A(l) \<longrightarrow> (\<forall>y. Pl(y) \<longrightarrow> Co(l,y)) \<or> 
                     (\<forall>y. A(y) \<and> M(y,l) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(l,y))"
        using assms(13) ..
      then have  "(\<forall>y. Pl(y) \<longrightarrow> Co(l,y)) \<or> 
              (\<forall>y. A(y) \<and> M(y,l) \<and> (\<exists>z. Pl(z) \<and> Co(y,z)) \<longrightarrow> Co(l,y))"
        using \<open>A(l)\<close> ..
      then show "\<not>Co(z,s)"
      proof
        assume "\<forall>y. Pl(y) \<longrightarrow> Co(l,y)"
        then have "Pl(s) \<longrightarrow> Co(l,s)" ..
        have "Pl(s)" using assms(12) s by (rule instancia)
        with \<open>Pl(s) \<longrightarrow> Co(l,s)\<close> have "Co(l,s)" ..
        with \<open>\<not>Co(l,s)\<close> show "\<not>Co(z,s)" ..
      next
        assume "\<forall>y. A(y) \<and> M(y,l) \<and> (\<exists>u. Pl(u) \<and> Co(y,u)) \<longrightarrow> Co(l,y)"
        then have zl: "A(z) \<and> M(z,l) \<and> (\<exists>u. Pl(u) \<and> Co(z,u)) \<longrightarrow> Co(l,z)" ..
        have "A(z)" using assms(2) z by (rule instancia)
        have "\<not>(\<exists>u. Pl(u) \<and> Co(z,u))" 
          using zl \<open>A(z)\<close> \<open>M(z,l)\<close> \<open>\<not>Co(l,z)\<close> by (rule mt2)
        show "\<not>Co(z,s)"
        proof
          assume "Co(z,s)"
          have "Pl(s)" using assms(12) s by (rule instancia)
          then have "Pl(s) \<and> Co(z,s)" using \<open>Co(z,s)\<close> ..
          then have "\<exists>u. Pl(u) \<and> Co(z,u)" ..
          with \<open>\<not>(\<exists>u. Pl(u) \<and> Co(z,u))\<close> show False ..
        qed 
      qed
    qed
  qed
  have 3: "M(p,z)"
  proof -
    have "Pa(p) \<and> Z(z)" using p z ..
    have "\<forall>y. Pa(p) \<and> Z(y) \<longrightarrow> M(p,y)" using assms(15) ..
    then have "Pa(p) \<and> Z(z) \<longrightarrow> M(p,z)" ..
    then show "M(p,z)" using \<open>Pa(p) \<and> Z(z)\<close> ..
  qed
  have 4: "Co(z,p)"
  proof -
    have "A(z)" using assms(2) z by (rule instancia)
    have "A(z) \<longrightarrow> (\<forall>y. Pl(y) \<longrightarrow> Co(z,y)) \<or> 
                   (\<forall>y. A(y) \<and> M(y,z) \<and> (\<exists>u. Pl(u) \<and> Co(y,u)) \<longrightarrow> Co(z,y))"
      using assms(13) ..
    then have "(\<forall>y. Pl(y) \<longrightarrow> Co(z,y)) \<or> 
           (\<forall>y. A(y) \<and> M(y,z) \<and> (\<exists>u. Pl(u) \<and> Co(y,u)) \<longrightarrow> Co(z,y))"
      using \<open>A(z)\<close> ..
    then show "Co(z,p)"
    proof 
      assume "\<forall>y. Pl(y) \<longrightarrow> Co(z,y)"
      then have "Pl(s) \<longrightarrow> Co(z,s)" ..
      have "Pl(s)" using assms(12) s by (rule instancia)
      with \<open>Pl(s) \<longrightarrow> Co(z,s)\<close> have "Co(z,s)" ..
      with \<open>\<not>Co(z,s)\<close> show "Co(z,p)" ..
    next
      assume "\<forall>y. A(y) \<and> M(y,z) \<and> (\<exists>u. Pl(u) \<and> Co(y,u)) \<longrightarrow> Co(z,y)"
      then have pz: "A(p) \<and> M(p,z) \<and> (\<exists>u. Pl(u) \<and> Co(p,u)) \<longrightarrow> Co(z,p)" ..
      have "A(p)" using assms(3) p by (rule instancia)
      have "\<exists>u. Pl(u) \<and> Co(p,u)"
      proof -
        have "Pl(s)" using assms(12) s by (rule instancia)
        then have "Pl(s) \<and> Co(p,s)" using \<open>Co(p,s)\<close> ..  
        then show "\<exists>u. Pl(u) \<and> Co(p,u)" ..
      qed
      show "Co(z,p)" using pz \<open>A(p)\<close> \<open>M(p,z)\<close> \<open>\<exists>u. Pl(u) \<and> Co(p,u)\<close>
        by (rule mp3)
    qed
  qed
  then have "Co(z,p) \<and> Co(p,s)" using 1 .. 
  show "\<exists>x y. A(x) \<and> A(y) \<and> (\<exists>u. S(u) \<and> Co(y,u) \<and> Co(x,y))" 
  proof -
    have "A(z)" using assms(2) z by (rule instancia)
    have "A(p)" using assms(3) p by (rule instancia)
    have "S(s) \<and> Co(p,s) \<and> Co(z,p)" using s \<open>Co(p,s)\<close> \<open>Co(z,p)\<close> 
      by (rule conjI3)
    then have "\<exists>u. S(u) \<and> Co(p,u) \<and> Co(z,p)" ..
    have "A(z) \<and> A(p) \<and> (\<exists>u. S(u) \<and> Co(p,u) \<and> Co(z,p))"
      using \<open>A(z)\<close> \<open>A(p)\<close> \<open>\<exists>u. S(u) \<and> Co(p,u) \<and> Co(z,p)\<close>
      by (rule conjI3)
    then have "\<exists>y. A(z) \<and> A(y) \<and> (\<exists>u. S(u) \<and> Co(y,u) \<and> Co(z,y))" ..
    then show "\<exists>x y. A(x) \<and> A(y) \<and> (\<exists>u. S(u) \<and> Co(y,u) \<and> Co(x,y))" ..
  qed
qed

end