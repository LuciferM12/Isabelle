theory actividad25
  imports Main
begin

subsection \<open>Actividad\<close>

lemma ejercicio2:
  assumes 1: "(s\<longrightarrow>t) \<and> (z\<longrightarrow> \<not>t)" and
          2: "s \<and> z"
        shows "p"
proof -
  have 4: "(s\<longrightarrow>t)" using 1 by (rule conjunct1)
  have 5: "s" using 2 by (rule conjunct1)
  have 6: "z" using 2 by (rule conjunct2)
  have 7: "(z\<longrightarrow>\<not>t)" using 1 by (rule conjunct2)
  have 8: "t" using 4 5 by (rule mp)
  have 9: "\<not>t" using 7 6 by (rule mp)
    show "p" using 9 8 by (rule notE)
qed

lemma ejercicioLaboratorio:
  assumes 1: "MgO" and 
         2: "h2" and
         3: "O2" and
        4:  "C" and
        5: "(MgO \<and> h2) \<longrightarrow> Mg \<and> H2O" and
        6: "C \<and> O2 \<longrightarrow> CO2" and
        7: "CO2 \<and> H2O \<longrightarrow> H2CO3"
      shows "H2CO3"
proof -
  have 8: "C \<and> O2" using 4 3 by (rule conjI)
  have 9: "CO2" using 6 8 by (rule mp)
  have 10: "(MgO \<and> h2)" using 1 2 by (rule conjI)
  have 11: "Mg \<and> H2O" using 5 10 by (rule mp)
  have 12: "H2O" using 11 by (rule conjunct2)
  have 13: "CO2 \<and>  H2O" using 9 12 by (rule conjI)
     show "H2CO3" using 7 13 by (rule mp)
qed
  
