theory ejercicioJuan
  imports Main
begin

lemma ejercicio1: 
  assumes 1: "\<forall>x. P(x) \<longrightarrow> Q(x)" and
          2: "\<forall>x. Q(x) \<longrightarrow> R(x)" and
          3: "P(a)"
        shows "R(a)"
proof -
  have 4: "P(a) \<longrightarrow> Q(a)" using 1 by (rule allE)
  have 5: "Q(a)" using 4 3 by (rule mp)
  have 6: "Q(a) \<longrightarrow> R(a)" using 2 by (rule allE)
  show "R(a)" using 6 5 by (rule mp)
qed
  
   


