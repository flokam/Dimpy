section \<open>Application example from CreditScoring\<close> 
text \<open>\<close>
theory AttendanceScoringLocale
  imports SchoolAttendanceInfrastructure
begin
locale AttendanceScoring = 
fixes AttendanceScoring_actors ::\<open>identity set\<close>
defines AttendanceScoring_actors_def: \<open>AttendanceScoring_actors \<equiv> {''Alice'',''Bob'',''ED''}\<close>

fixes CreditScoring_locations :: "location set"
defines CreditScoring_locations_def: "CreditScoring_locations \<equiv> {Location 0, Location 1, Location 2}"
fixes Coastal :: "location"
defines Coastal_def: "Coastal  \<equiv> Location 0"
fixes NonCoastal :: "location"
defines NonCoastal_def: "NonCoastal \<equiv> Location 1"
fixes London :: "location"
defines London_def: "London \<equiv> Location 2"


fixes ex_loc_ass :: "location \<Rightarrow> identity set"
defines ex_loc_ass_def: "ex_loc_ass \<equiv>
          (\<lambda> x. if x = Coastal then {''Bob''}  
                 else (if x = NonCoastal then {''Alice''} 
                       else (if x = London then {''ED''}
                        else {})))"
fixes ex_loc_ass' :: "location \<Rightarrow> identity set"
defines ex_loc_ass'_def: "ex_loc_ass' \<equiv>
          (\<lambda> x. if x = Coastal then {''Bob''}  
                 else (if x = NonCoastal then {} 
                       else (if x = London then {''Alice'', ''ED''}
                        else {})))"
(* data *)
fixes ex_data :: "identity \<Rightarrow> (dlm \<times> data)"
defines ex_data_def: \<open>ex_data \<equiv> (\<lambda> x :: identity. 
                                     (if x = ''Bob'' then ((Actor ''Bob'',{Actor ''ED''}),(Coastal,{fsm}, male, primary, winter, good, white))
                                      else (if x = ''Alice'' then 
                                                 ((Actor ''Alice'',{Actor ''ED''}),(NonCoastal, {fsm, sen}, female, secondary, winter, good, black))
                                                    else (if x = ''ED'' then 
                                                 ((Actor ''ED'',{}), (London, {fsm, sen, ehc, csc}, null, secondary, winter, good, white))
                                                  else 
                                                    ((Actor '''',{}),(London,{},null,secondary, winter, good, white))))))\<close>

fixes ex_data' :: "identity \<Rightarrow> (dlm \<times> data)"
defines ex_data'_def: \<open>ex_data' \<equiv> (\<lambda> x :: identity. 
                                     (if x = ''Bob'' then ((Actor ''Bob'',{Actor ''ED''}),(Coastal, {}, male, primary, winter, good, white))
                                      else (if x = ''Alice'' then 
                                                 ((Actor ''Alice'',{Actor ''ED''}),(NonCoastal, {fsm, sen}, female, secondary, winter, good, black))
                                            else (if x = ''ED'' then 
                                                 ((Actor ''ED'',{}), (London, {fsm, sen, ehc, csc}, null, secondary, winter, good,  white))
                                                  else 
                                                    ((Actor '''',{}),(London, {}, null, secondary, winter, good,  white))))))\<close>
fixes ex_data'' :: "identity \<Rightarrow> (dlm \<times> data)"
defines ex_data''_def: \<open>ex_data'' \<equiv> (\<lambda> x :: identity. 
                                     (if x = ''Bob'' then ((Actor ''Bob'',{Actor ''ED''}),(Coastal, {}, male, primary, winter, good, white))
                                      else (if x = ''Alice'' then 
                                                 ((Actor ''Alice'',{Actor ''ED''}),(London, {fsm, sen}, female, secondary, winter, good, black))
                                            else (if x = ''ED'' then 
                                                 ((Actor ''ED'',{}), (London, {fsm, sen, ehc, csc}, null, secondary, winter, good, white))
                                                  else 
                                                    ((Actor '''',{}),(London, {}, null, secondary, winter, good, white))))))\<close>


fixes black_box::  "(data \<Rightarrow> bool)"
defines black_box_def: \<open>black_box \<equiv> (\<lambda> (d :: data). 
                            (if (fst d = Coastal) then (card(fst(snd d)) = 0)
                             else (if (fst d = NonCoastal) then (card(fst(snd d)) \<le> 1) 
                              else (if (fst d = London) then (card(fst(snd d)) \<le> 2) else False))))\<close>

fixes ex_attendance :: \<open>(identity \<times> bool option)set\<close>
defines ex_attendance_def: \<open>ex_attendance \<equiv> {}\<close>

fixes ex_attendance' :: \<open>(identity \<times> bool option)set\<close>
defines ex_attendance'_def: \<open>ex_attendance' \<equiv> {(''Bob'', None)}\<close>

fixes ex_attendance'':: \<open>(identity \<times> bool option)set\<close>
defines ex_attendance''_def: \<open>ex_attendance'' \<equiv> {(''Bob'', Some(False))}\<close>

fixes ex_attendance''a:: \<open>(identity \<times> bool option)set\<close>
defines ex_attendance''a_def: \<open>ex_attendance''a \<equiv> {(''Bob'', None), (''Bob'', Some(False))}\<close>

fixes ex_attendance''':: \<open>(identity \<times> bool option)set\<close>
defines ex_attendance'''_def: \<open>ex_attendance''' \<equiv> {(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_attendance'''':: \<open>(identity \<times> bool option)set\<close>
defines ex_attendance''''_def: \<open>ex_attendance'''' \<equiv> {(''Alice'', None),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_attendanceV:: \<open>(identity \<times> bool option)set\<close>
defines ex_attendanceV_def: \<open>ex_attendanceV \<equiv> {(''Alice'', Some(False)),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_attendanceV':: \<open>(identity \<times> bool option)set\<close>
defines ex_attendanceV'_def: \<open>ex_attendanceV' \<equiv> {(''Alice'', None), (''Alice'', Some(False)),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>

fixes ex_attendanceV'':: \<open>(identity \<times> bool option)set\<close>
defines ex_attendanceV''_def: \<open>ex_attendanceV'' \<equiv> {(''Alice'', Some(True)), (''Alice'', Some(False)),(''Bob'', Some(True)), (''Bob'', Some(False))}\<close>


(* Graphs for the various states: initial*)
fixes ex_graph :: "igraph"
defines ex_graph_def: "ex_graph \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data black_box ex_attendance"

(* Bob puts Attendance application in *)
fixes ex_graph' :: "igraph"
defines ex_graph'_def: "ex_graph' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data black_box ex_attendance'"


(* ED evaluates Bob's application negatively *)
fixes ex_graph'' :: "igraph"
defines ex_graph''_def: "ex_graph'' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data black_box ex_attendance''"


(* Next try: now from previous state Bob actions a del to get a disadvantage set removal *)
fixes ex_graph''' :: "igraph"
defines ex_graph'''_def: "ex_graph''' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data' black_box ex_attendance''"

(* Bob puts in a attendance application *)
fixes ex_graph'''' :: "igraph"
defines ex_graph''''_def: "ex_graph'''' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal, London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data' black_box ex_attendance''a"

(* ED evaluates Bob's application - this time positive *)
fixes ex_graphV :: "igraph"
defines ex_graphV_def: "ex_graphV \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data' black_box ex_attendance'''"


(* Now, Alice puts in a attendance application *)
fixes ex_graphV' :: "igraph"
defines ex_graphV'_def: "ex_graphV' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data' black_box ex_attendance''''"

(* Alice's application is evaluated by ED to negative *)
fixes ex_graphV'' :: "igraph"
defines ex_graphV''_def: "ex_graphV'' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass ex_data' black_box ex_attendanceV"

(* Alice now moves to London *)
fixes ex_graphV''' :: "igraph"
defines ex_graphV'''_def: "ex_graphV''' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass' ex_data'' black_box ex_attendanceV"

(* Alice now puts in an application from London *)
fixes ex_graphV'''' :: "igraph"
defines ex_graphV''''_def: "ex_graphV'''' \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal ,London)} 
                                         ex_loc_ass' ex_data'' black_box ex_attendanceV'"

(* This time, ED evaluates to positive *)
fixes ex_graphX :: "igraph"
defines ex_graphX_def: "ex_graphX \<equiv> Lgraph {(Coastal,NonCoastal),(Coastal,London),(NonCoastal,London)} 
                                         ex_loc_ass' ex_data'' black_box ex_attendanceV''"

fixes local_policies :: "[igraph, location] \<Rightarrow> policy set"
defines local_policies_def: "local_policies G \<equiv> 
    (\<lambda> x. if x = Coastal then  {(\<lambda> y. True, {put,delete,move, eval})}
          else (if x = NonCoastal then {(\<lambda> y. True, {put,delete,move,eval})} 
                else (if x = London then  {(\<lambda> y. True, {put,delete,move,eval})} 
                      else {})))"

(* scenario states *)
fixes Ini :: \<open>infrastructure\<close>
defines Ini_def: \<open>Ini \<equiv> Infrastructure ex_graph local_policies\<close>

fixes C :: \<open>infrastructure\<close>
defines C_def: \<open>C \<equiv> Infrastructure ex_graph' local_policies\<close>

fixes CC :: \<open>infrastructure\<close>
defines CC_def: \<open>CC \<equiv> Infrastructure ex_graph'' local_policies\<close>

fixes Ca :: \<open>infrastructure\<close>
defines Ca_def: \<open>Ca \<equiv> Infrastructure ex_graph''' local_policies\<close>

fixes CCa :: \<open>infrastructure\<close>
defines CCa_def: \<open>CCa \<equiv> Infrastructure ex_graph'''' local_policies\<close>

fixes CCCa :: \<open>infrastructure\<close>
defines CCCa_def: \<open>CCCa \<equiv> Infrastructure ex_graphV local_policies\<close>

fixes Cb :: \<open>infrastructure\<close>
defines Cb_def: \<open>Cb \<equiv> Infrastructure ex_graphV' local_policies\<close>

fixes CCb :: \<open>infrastructure\<close>
defines CCb_def: \<open>CCb \<equiv> Infrastructure ex_graphV'' local_policies\<close>

fixes Cc :: \<open>infrastructure\<close>
defines Cc_def: \<open>Cc \<equiv> Infrastructure ex_graphV''' local_policies\<close>

fixes CCc :: \<open>infrastructure\<close>
defines CCc_def: \<open>CCc \<equiv> Infrastructure ex_graphV'''' local_policies\<close>

fixes CCCc :: \<open>infrastructure\<close>
defines CCCc_def: \<open>CCCc \<equiv> Infrastructure ex_graphX local_policies\<close>

(* The School Attendance Kripke structure *)
fixes Attendance_states
defines Attendance_states_def: \<open>Attendance_states \<equiv> {s. Ini \<rightarrow>\<^sub>i* s }\<close>
fixes Attendance_Kripke
defines Attendance_Kripke_def: \<open>Attendance_Kripke \<equiv> Kripke Attendance_states {Ini}\<close>
fixes M
defines M_def: \<open>M \<equiv> Attendance_Kripke\<close>

(* The desirable outcome DO *)
fixes DO :: \<open>identity \<Rightarrow> infrastructure \<Rightarrow> bool\<close>
defines DO_def: \<open>DO a s \<equiv> (a, Some True) \<in> attendance (graphI s)\<close>


fixes ndobob
defines ndobob_def: \<open>ndobob \<equiv> {(s :: infrastructure). \<not>(DO ''Bob''  s)}\<close>

fixes disadvantage_set :: \<open>identity \<Rightarrow> infrastructure \<Rightarrow> disadvantage set\<close>
defines disadvantage_set_def : \<open>(disadvantage_set a s) \<equiv> (fst (snd (snd(dgra (graphI s) a))))\<close>

fixes pc0 
defines pc0_def: \<open>pc0 A s \<equiv> (card(disadvantage_set A s) \<le> 1)\<close>

fixes ndoalice
defines ndoalice_def: \<open>ndoalice \<equiv> {(s :: infrastructure). (pc0 ''Alice'' s) \<and> \<not>(DO ''Alice''  s)}\<close>

fixes pc1
defines pc1_def: \<open>pc1 A s \<equiv> ((card(disadvantage_set A s) = 0) \<and> (A  @\<^bsub>(graphI s)\<^esub> Coastal))\<close>
fixes pc2
defines pc2_def: \<open>pc2 A s \<equiv> ((card(disadvantage_set A s) \<le> 1) \<and> (A  @\<^bsub>(graphI s)\<^esub> NonCoastal))\<close>
fixes pc3
defines pc3_def: \<open>pc3 A s \<equiv> ((card(disadvantage_set A s) \<le> 2) \<and> (A  @\<^bsub>(graphI s)\<^esub> London))\<close>

begin 

(* lemmas for the state transitions: a bit tedious but almost all done by sledgehammer automatically*)
lemma stepI_C: "Ini  \<rightarrow>\<^sub>n C"
proof (rule_tac l = Coastal and a = "''Bob''"  in put)
  show "graphI Ini = graphI Ini" by (rule refl)
next show "''Bob'' @\<^bsub>graphI Ini\<^esub> Coastal"
    by (simp add: Ini_def atI_def ex_graph_def ex_loc_ass_def)
next show "Coastal \<in> nodes (graphI Ini)"
    using Ini_def ex_graph_def nodes_def by auto
next show \<open>enables Ini Coastal (Actor ''Bob'') put\<close>
    by (simp add: Ini_def  enables_def local_policies_def)
next show \<open>C = Infrastructure (put_graph_a ''Bob'' Coastal (graphI Ini)) (delta Ini)\<close>
    by (simp add: C_def Ini_def ex_graph_def ex_graph'_def ex_attendance_def ex_attendance'_def
    put_graph_a_def)
qed


lemma stepC_CC: "C  \<rightarrow>\<^sub>n CC"
proof (rule_tac l = Coastal and a = "''Bob''" and c = "''ED''" in eval)
  show \<open>graphI C = graphI C\<close> by (rule refl)
next show \<open>''Bob'' @\<^bsub>graphI C\<^esub> Coastal\<close>
    by (simp add: C_def atI_def ex_graph'_def ex_loc_ass_def)
next show \<open>Coastal \<in> nodes (graphI C)\<close>
    using C_def ex_graph'_def nodes_def by auto
next show \<open>''ED'' \<in> actors_graph (graphI C)\<close>
    apply (simp add: actors_graph_def)
    by (simp add: C_def ex_graph'_def ex_loc_ass_def London_def NonCoastal_def Coastal_def nodes_def, blast)
next show \<open>Actor ''ED'' \<in> readers (dgra (graphI C) ''Bob'') \<or> Actor ''ED'' = owner (dgra (graphI C) ''Bob'')\<close>
    by (simp add: C_def ex_graph'_def ex_data_def readers_def)
next show \<open>enables C Coastal (Actor ''ED'') eval\<close>
    by (simp add: C_def enables_def local_policies_def)
next show \<open>(''Bob'', None) \<in> attendance (graphI C)\<close>
    by (simp add: C_def ex_attendance'_def ex_graph'_def)
next show \<open> CC = Infrastructure (eval_graph_a ''Bob'' (graphI C)) (delta C)\<close>
    by (simp add: CC_def ex_graph''_def ex_attendance''_def eval_graph_a_def ex_loc_ass_def 
           ex_data_def C_def ex_graph'_def ex_attendance'_def black_box_def local_policies_def)
qed


lemma stepCC_Ca: "CC  \<rightarrow>\<^sub>n Ca"
proof (rule_tac l = Coastal and a = "''Bob''" and d = fsm in delete)
  show "graphI CC = graphI CC" by (rule refl)
next show "''Bob'' @\<^bsub>graphI CC\<^esub> Coastal"
    by (simp add: CC_def atI_def ex_graph''_def ex_loc_ass_def) 
next show \<open>Coastal \<in> nodes (graphI CC)\<close>
    using CC_def ex_graph''_def nodes_def by auto
next show \<open>enables CC Coastal (Actor ''Bob'') delete\<close>
    by (simp add: CC_def enables_def local_policies_def)
next show \<open>fsm \<in> fst (snd (snd (dgra (graphI CC) ''Bob'')))\<close>
    by (simp add: CC_def ex_graph''_def ex_data_def)
next show \<open>''Bob'' \<in> actors_graph (graphI CC)\<close>
    by (simp add: CC_def actors_graph_def ex_graph''_def ex_loc_ass_def London_def NonCoastal_def Coastal_def
            nodes_def, force)
next show \<open>Ca = Infrastructure (delete_graph_a ''Bob'' fsm(graphI CC)) (delta CC) \<close>
    apply (simp add: delete_graph_a_def CC_def Ca_def ex_graph''_def ex_graph'''_def ex_data_def ex_data'_def)
    apply (rule ext)
    by force
qed


lemma stepCa_CCa: "Ca  \<rightarrow>\<^sub>n CCa"
proof (rule_tac l = Coastal and a = "''Bob''" in put)
  show "graphI Ca = graphI Ca" by (rule refl)
next show \<open>''Bob'' @\<^bsub>graphI Ca\<^esub> Coastal\<close>
    by (simp add: Ca_def atI_def ex_graph'''_def ex_loc_ass_def)
next show \<open>Coastal \<in> nodes (graphI Ca)\<close>
    using Ca_def ex_graph'''_def nodes_def by auto
next show \<open>enables Ca Coastal (Actor ''Bob'') put\<close>
    by (simp add: Ca_def enables_def local_policies_def)
next show \<open>CCa = Infrastructure (put_graph_a ''Bob'' Coastal (graphI Ca)) (delta Ca)\<close>
    by (simp add: put_graph_a_def CCa_def Ca_def ex_graph''''_def ex_graph'''_def ex_attendance''_def ex_attendance''a_def)
qed

lemma stepCCa_CCCa: "CCa  \<rightarrow>\<^sub>n CCCa"
proof (rule_tac l = Coastal and a = "''Bob''" and c = \<open>''ED''\<close> in eval)
  show \<open>graphI CCa = graphI CCa\<close> by (rule refl)
next show \<open>''Bob'' @\<^bsub>graphI CCa\<^esub> Coastal\<close>
    by (simp add: CCa_def atI_def ex_graph''''_def ex_loc_ass_def)
next show \<open>Coastal \<in> nodes (graphI CCa)\<close>
    using CCa_def ex_graph''''_def nodes_def by auto
next show \<open>''ED'' \<in> actors_graph (graphI CCa)\<close>
    apply (simp add: actors_graph_def)
    by (simp add: CCa_def ex_graph''''_def ex_loc_ass_def London_def NonCoastal_def Coastal_def nodes_def, blast)
next show \<open>Actor ''ED'' \<in> readers (dgra (graphI CCa) ''Bob'') \<or> Actor ''ED'' = owner (dgra (graphI CCa) ''Bob'')\<close>
    by (simp add: CCa_def ex_graph''''_def ex_data'_def readers_def)
next show \<open>enables CCa Coastal (Actor ''ED'') eval\<close>
    by (simp add: CCa_def enables_def local_policies_def)
next show \<open>(''Bob'', None) \<in> attendance (graphI CCa)\<close>
    by (simp add: CCa_def ex_attendance''a_def ex_graph''''_def)
next show \<open>CCCa = Infrastructure (eval_graph_a ''Bob'' (graphI CCa)) (delta CCa)\<close>
    by (simp add: eval_graph_a_def CCCa_def ex_graphV_def CCa_def ex_graph''''_def 
          ex_attendance'''_def black_box_def ex_attendance''a_def ex_data'_def)
qed

lemma stepCCCa_Cb: "CCCa  \<rightarrow>\<^sub>n Cb"
proof (rule_tac l = NonCoastal and a = "''Alice''"  in put)
  show \<open>graphI CCCa = graphI CCCa\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCCa\<^esub> NonCoastal\<close>
    by (simp add: CCCa_def Coastal_def NonCoastal_def atI_def ex_graphV_def ex_loc_ass_def)
next show \<open>NonCoastal \<in> nodes (graphI CCCa)\<close>
    using CCCa_def ex_graphV_def nodes_def by auto
next show \<open>enables CCCa NonCoastal (Actor ''Alice'') put\<close>
    by (simp add: CCCa_def enables_def local_policies_def)
next show \<open>Cb = Infrastructure (put_graph_a ''Alice'' NonCoastal (graphI CCCa)) (delta CCCa)\<close>
    by (simp add: put_graph_a_def CCCa_def Cb_def ex_graphV'_def ex_graphV_def ex_attendance''''_def ex_attendance'''_def)
qed

lemma stepCb_CCb: "Cb  \<rightarrow>\<^sub>n CCb"
proof (rule_tac l = NonCoastal and a = "''Alice''"  and c = "''ED''" in eval)
  show \<open>graphI Cb = graphI Cb\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI Cb\<^esub> NonCoastal\<close>
    by (simp add: Cb_def Coastal_def NonCoastal_def atI_def ex_graphV'_def ex_loc_ass_def)
next show \<open>NonCoastal \<in> nodes (graphI Cb)\<close>
    using Cb_def ex_graphV'_def nodes_def by auto
next show \<open>''ED'' \<in> actors_graph (graphI Cb)\<close>
    apply (simp add: actors_graph_def)
    by (simp add: Cb_def ex_graphV'_def ex_loc_ass_def London_def NonCoastal_def Coastal_def nodes_def, blast)
next show \<open>Actor ''ED'' \<in> readers (dgra (graphI Cb) ''Alice'') \<or> Actor ''ED'' = owner (dgra (graphI Cb) ''Alice'')\<close>
    by (simp add: Cb_def ex_graphV'_def ex_data'_def readers_def)
next show \<open>enables Cb NonCoastal (Actor ''ED'') eval\<close>
    by (simp add: Cb_def enables_def local_policies_def) 
next show \<open>(''Alice'', None) \<in> attendance (graphI Cb)\<close>
    by (simp add: Cb_def ex_attendance''''_def ex_graphV'_def)
next show \<open>CCb = Infrastructure (eval_graph_a ''Alice'' (graphI Cb)) (delta Cb) \<close>
    apply (simp add: eval_graph_a_def CCb_def ex_graphV''_def Cb_def ex_graphV'_def ex_attendanceV_def ex_attendance''''_def
                     black_box_def NonCoastal_def London_def Coastal_def)
    by (simp add: NonCoastal_def ex_data'_def)
qed

lemma stepCCb_Cc: "CCb  \<rightarrow>\<^sub>n Cc"
proof (rule_tac l = NonCoastal and l' = London and a = "''Alice''"  in move)
  show \<open>graphI CCb = graphI CCb\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCb\<^esub> NonCoastal\<close>
    by (simp add: CCb_def Coastal_def NonCoastal_def atI_def ex_graphV''_def ex_loc_ass_def)
next show \<open>NonCoastal \<in> nodes (graphI CCb)\<close>
    using CCb_def ex_graphV''_def nodes_def by auto
next show \<open>London \<in> nodes (graphI CCb)\<close>
    using CCb_def ex_graphV''_def nodes_def by auto
next show \<open>''Alice'' \<in> actors_graph (graphI CCb)\<close>
    apply (simp add: actors_graph_def CCb_def ex_graphV''_def ex_loc_ass_def London_def NonCoastal_def Coastal_def nodes_def)
    by force
  next show \<open>enables CCb London (Actor ''Alice'') move\<close>
    by (simp add: CCb_def enables_def local_policies_def)
next show \<open>Cc = Infrastructure (move_graph_a ''Alice'' NonCoastal London (graphI CCb)) (delta CCb)\<close>
    apply (simp add: move_graph_a_def Cc_def ex_graphV'''_def CCb_def ex_graphV''_def ex_loc_ass_def
             ex_loc_ass'_def ex_data'_def ex_data''_def Coastal_def NonCoastal_def London_def)
    apply (rule conjI)
    apply (rule ext)
     apply (simp add: NonCoastal_def London_def)
    apply (rule ext)
    by (simp add: Coastal_def London_def)
qed

lemma stepCc_CCc: "Cc  \<rightarrow>\<^sub>n CCc"
proof (rule_tac l = London and a = "''Alice''"  in put)
  show \<open>graphI Cc = graphI Cc\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI Cc\<^esub> London\<close>
    by (simp add: Cc_def atI_def ex_graphV'''_def ex_loc_ass'_def London_def NonCoastal_def Coastal_def) 
next show \<open> London \<in> nodes (graphI Cc)\<close>
    using Cc_def ex_graphV'''_def nodes_def by auto
next show \<open> enables Cc London (Actor ''Alice'') put\<close>
    by (simp add: Cc_def enables_def local_policies_def)
next show \<open>CCc = Infrastructure (put_graph_a ''Alice'' London (graphI Cc)) (delta Cc)\<close>
    apply (simp add: put_graph_a_def CCc_def ex_graphV'''_def ex_loc_ass'_def Cc_def ex_graphV''''_def)
    by (simp add: ex_attendanceV_def
                     ex_attendanceV'_def)
qed

lemma stepCCc_CCCc: "CCc  \<rightarrow>\<^sub>n CCCc"
proof (rule_tac l = London and a = "''Alice''" and c = "''ED''" in eval)
  show \<open>graphI CCc = graphI CCc\<close> by (rule refl)
next show \<open>''Alice'' @\<^bsub>graphI CCc\<^esub> London\<close>
    by (simp add: CCc_def atI_def ex_graphV''''_def ex_loc_ass'_def London_def Coastal_def NonCoastal_def)
next show \<open>London \<in> nodes (graphI CCc)\<close>
    using CCc_def ex_graphV''''_def nodes_def by auto
next show \<open>''ED'' \<in> actors_graph (graphI CCc)\<close>
    apply (simp add: actors_graph_def CCc_def ex_graphV''''_def nodes_def ex_loc_ass'_def London_def NonCoastal_def Coastal_def)
    by blast 
next show \<open>Actor ''ED'' \<in> readers (dgra (graphI CCc) ''Alice'') \<or> Actor ''ED'' = owner (dgra (graphI CCc) ''Alice'')\<close>
    by (simp add: CCc_def ex_graphV''''_def ex_data''_def readers_def)
next show \<open>enables CCc London (Actor ''ED'') eval\<close>
    by (simp add: CCc_def enables_def local_policies_def)
next show \<open>(''Alice'', None) \<in> attendance (graphI CCc)\<close>
    by (simp add: CCc_def ex_attendanceV'_def ex_graphV''''_def)
next show \<open>CCCc = Infrastructure (eval_graph_a ''Alice'' (graphI CCc)) (delta CCc)\<close>
    apply (simp add: eval_graph_a_def CCCc_def ex_graphX_def black_box_def CCc_def ex_graphV''''_def
               ex_attendanceV'_def ex_attendanceV''_def)
    apply (rule conjI)
     apply (simp add: NonCoastal_def London_def Coastal_def ex_data''_def)
    apply (simp add: NonCoastal_def London_def Coastal_def)
    by (simp add: ex_graphX_def CCc_def ex_graphV''''_def ex_attendanceV'_def
                  ex_attendanceV''_def black_box_def ex_data''_def London_def)
qed

(* Another interation would be great in which Charlie tries to get attendance scoring and the reduses his
   disadvantage set by one as Bob did. That would then fully give the pc as pc1 \<or> pc2 \<or> pc3*)

(* Application of PCR cycle *)

(* Step 1: find an attack *)
lemma att_ndobob_Kripke: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndobob)\<^esup>)\<close>
proof (subst att_and, simp, rule conjI)
  show \<open>\<turnstile>\<N>\<^bsub>({Ini}, {C})\<^esub>\<close>
    apply (simp add: att_base)
    using state_transition_infra_def stepI_C by fastforce
next show \<open>\<turnstile>[\<N>\<^bsub>({C}, ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({C}, ndobob)\<^esup>\<close>
    apply (subst att_and, simp)
    apply (simp add: ndobob_def is_attack_tree.simps(1) state_transition_infra_def)
    apply (rule_tac x = CC in exI)
    apply (rule conjI)
    prefer 2
    using stepC_CC apply blast
    by (simp add: DO_def CC_def ex_graph''_def ex_attendance''_def)
qed

(* The attack gives us the CTL formula by Correctness of AT *)
lemma Attendance_att: "M \<turnstile> EF ndobob"
proof -
  have a: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndobob)\<^esup>)\<close> by (rule att_ndobob_Kripke)
  hence "({Ini}, ndobob) = attack (([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},ndobob)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndobob)\<^esup>))" by simp
  hence \<open>Kripke {s::infrastructure. \<exists>i::infrastructure\<in> {Ini}. i \<rightarrow>\<^sub>i* s} {Ini} \<turnstile> EF ndobob\<close>
    using AT_EF att_ndobob_Kripke by fastforce
  thus \<open>M \<turnstile> EF ndobob\<close>
    by (simp add: Attendance_Kripke_def Attendance_states_def M_def)
qed



(* Step 2: Now, apply counterfactuals to find a close state with DO and first precondition:
  Find an initial precondition that yields the desirable outcome DO 
  in a closest state using counterfactuals. *) 


(* Application of counterfactuals to find that closest state with DO is CCCa *)
lemma counterfactual_CCCa: \<open>CCCa \<in> (counterfactuals CC (\<lambda> s. DO ''Bob'' s))\<close>
  apply (simp add: counterfactuals_def)
  apply (rule conjI)
   apply (simp add: CCCa_def DO_def ex_graphV_def ex_attendance'''_def)
  apply (rule_tac x = CC in exI)
  apply (rule conjI)
   apply (subgoal_tac \<open>CC \<rightarrow>\<^sub>n* Ca\<close>)
  apply (subgoal_tac \<open>Ca \<rightarrow>\<^sub>n* CCa\<close>)
  apply (subgoal_tac \<open>CCa \<rightarrow>\<^sub>n* CCCa\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCa_CCCa)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCa_CCa)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCC_Ca)
(* *)
  apply (simp add: closest_def)
  apply (rule conjI)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
    apply (subgoal_tac \<open>CC \<rightarrow>\<^sub>n* Ca\<close>)
  apply (subgoal_tac \<open>Ca \<rightarrow>\<^sub>n* CCa\<close>)
  apply (subgoal_tac \<open>CCa \<rightarrow>\<^sub>n* CCCa\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCa_CCCa)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCa_CCa)
by (simp add: r_into_rtrancl state_transition_in_refl_def stepCC_Ca)


(* As a result the new (first) precondition is pc0 \<equiv> card(disadvantage_set A s) \<le> 1 *)
(*Step 3: Generalisation *)
(* Try to generalize over all actors, that is, try to show for all actors A
    AG {w. pc0 \<longrightarrow> DO A s }*)
(* Attack tree analysis shows that this fails because for Alice there is a path to
   a failure state where pc0 holds but not DO. *)

(*
lemma att_nodoalice_Kripke: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},{CC})\<^esub>,\<N>\<^bsub>({CC},{Ca})\<^esub>,\<N>\<^bsub>({Ca},{CCa})\<^esub>, 
                        \<N>\<^bsub>({CCa},{CCCa})\<^esub>, \<N>\<^bsub>({CCCa},{Cb})\<^esub>,\<N>\<^bsub>({Cb},ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndoalice)\<^esup>)\<close>
proof (subst att_and, simp, rule conjI)
  show \<open>\<turnstile>\<N>\<^bsub>({Ini}, {C})\<^esub>\<close>
    by (simp add: AT.att_base state_transition_infra_def stepI_C)
next show \<open> \<turnstile>[\<N>\<^bsub>({C}, {CC})\<^esub>, \<N>\<^bsub>({CC}, {Ca})\<^esub>, \<N>\<^bsub>({Ca}, {CCa})\<^esub>, \<N>\<^bsub>({CCa}, {CCCa})\<^esub>, \<N>\<^bsub>({CCCa}, {Cb})\<^esub>, 
              \<N>\<^bsub>({Cb}, ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({C}, ndoalice)\<^esup>\<close>
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepC_CC)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCC_Ca)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCa_CCa)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCCa_CCCa)
    apply (subst att_and, simp, rule conjI)
     apply (simp add: att_base)
     apply (simp add: state_transition_infra_def stepCCCa_Cb)
    apply (subst att_and, simp add: ndoalice_def)
    apply (simp add: att_base)
    apply (rule_tac x = CCb in exI)
    apply (rule conjI)
     apply (simp add: CCb_def ex_graphV''_def pc0_def disadvantage_set_def ex_data'_def)
    sorry
     apply (rule conjI)
     apply (simp add: DO_def CCb_def ex_graphV''_def ex_attendanceV_def)
    by (simp add: state_transition_infra_def stepCb_CCb)
qed
*)

(* Application of counterfactuals to find that the closest state to  CCb where DO holds is CCc.
   This isnpires the next precondition pc1 as in CCCc we have 
   salary A s \<ge> 0 \<and> A  @\<^bsub>(graphI s)\<^esub> Coastal) *)
(*lemma counterfactual_CCCc: \<open>CCCc \<in> (counterfactuals CCb (\<lambda> s. DO ''Alice'' s))\<close>
  apply (simp add: counterfactuals_def)
  apply (rule conjI)
  apply (simp add: CCCc_def DO_def ex_graphX_def ex_requestsV''_def)
  apply (rule_tac x = CCb in exI)
  apply (rule conjI)
   apply (subgoal_tac \<open>CCb \<rightarrow>\<^sub>n* Cc\<close>)
   apply (subgoal_tac \<open>Cc \<rightarrow>\<^sub>n* CCc\<close>)
   apply (subgoal_tac \<open>CCc \<rightarrow>\<^sub>n* CCCc\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
     apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCc_CCCc)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCc_CCc)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCb_Cc)
  apply (simp add: closest_def)
  apply (rule conjI)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
   apply (subgoal_tac \<open>CCb \<rightarrow>\<^sub>n* Cc\<close>)
   apply (subgoal_tac \<open>Cc \<rightarrow>\<^sub>n* CCc\<close>)
   apply (subgoal_tac \<open>CCc \<rightarrow>\<^sub>n* CCCc\<close>)
      apply (simp add: state_transition_infra_def state_transition_in_refl_def)
     apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCCc_CCCc)
  apply (simp add: r_into_rtrancl state_transition_in_refl_def stepCc_CCc)
  by (simp add: r_into_rtrancl state_transition_in_refl_def stepCCb_Cc)
*)

(*
(* The attack gives us the CTL formula of reachability of the failure state by Correctness of AT *)
lemma Attendance_att': "M \<turnstile> EF ndoalice"
proof -
  have a: \<open>\<turnstile>([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},{CC})\<^esub>,\<N>\<^bsub>({CC},{Ca})\<^esub>,\<N>\<^bsub>({Ca},{CCa})\<^esub>, 
                        \<N>\<^bsub>({CCa},{CCCa})\<^esub>, \<N>\<^bsub>({CCCa},{Cb})\<^esub>,\<N>\<^bsub>({Cb},ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndoalice)\<^esup>)\<close> 
    by (rule att_nodoalice_Kripke)
  hence "({Ini}, ndoalice) = attack ([\<N>\<^bsub>({Ini},{C})\<^esub>, \<N>\<^bsub>({C},{CC})\<^esub>,\<N>\<^bsub>({CC},{Ca})\<^esub>,\<N>\<^bsub>({Ca},{CCa})\<^esub>, 
                        \<N>\<^bsub>({CCa},{CCCa})\<^esub>, \<N>\<^bsub>({CCCa},{Cb})\<^esub>,\<N>\<^bsub>({Cb},ndoalice)\<^esub>] \<oplus>\<^sub>\<and>\<^bsup>({Ini},ndoalice)\<^esup>)" by simp
  hence \<open>Kripke {s::infrastructure. \<exists>i::infrastructure\<in> {Ini}. i \<rightarrow>\<^sub>i* s} {Ini} \<turnstile> EF ndoalice\<close>
    using AT_EF att_nodoalice_Kripke by fastforce
  thus \<open>M \<turnstile> EF ndoalice\<close>
    by (simp add: Attendance_Kripke_def Attendance_states_def M_def)
qed
*)


(* Next iteration: go back to 2 with the new precondition 
   pc1 A s  \<equiv>  ((card(disadvantage_set A s) \<le> 1) \<and> (A  @\<^bsub>(graphI s)\<^esub> Coastal)).
   Now the generalisation step succeeds. *)
lemma Alice_Bob_in_Attendance_Kripke: "s \<in> states(Attendance_Kripke)  \<Longrightarrow> 
      actors_graph (graphI s) = {''Alice'',''Bob'',''ED''}"
  apply (subgoal_tac \<open>(Ini, s) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<close>)
  prefer 2
   apply (smt (verit, del_insts) CollectD Collect_cong Attendance_Kripke_def Attendance_states_def split_cong state_transition_infra_def state_transition_refl_def states.simps)
  apply (subgoal_tac \<open>actors_graph (graphI Ini) =  {''Alice'',''Bob'',''ED''}\<close>)
   apply (erule subst)
   apply (rule sym)
   apply (erule same_actors)
  apply (simp add: Ini_def ex_graph_def actors_graph_def ex_loc_ass_def London_def NonCoastal_def Coastal_def nodes_def)
  apply (rule equalityI)
   apply fastforce
  apply (rule subsetI)
  apply (rule CollectI)
  apply (subgoal_tac \<open>x = ''Alice'' \<or> x = ''Bob'' \<or> x = ''ED''\<close>)
   apply (metis (no_types, lifting) location.inject n_not_Suc_n numeral_2_eq_2 zero_neq_numeral)
  by force


lemma step_rtrancl: \<open>a \<rightarrow>\<^sub>n b \<Longrightarrow> a \<rightarrow>\<^sub>i* b\<close>
  by (simp add: r_into_rtrancl state_transition_infra_def state_transition_refl_def)


lemma enables_move0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> 
     \<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y). enables y l (Actor a) move\<close>
proof (erule rtrancl_induct)
  show \<open>\<forall>a\<in>actors_graph (graphI Ini). \<forall>l\<in>nodes (graphI Ini). enables Ini l (Actor a) move\<close>
  proof (clarify, simp add: Ini_def ex_graph_def local_policies_def  nodes_def enables_def
         London_def Coastal_def NonCoastal_def, erule exE, blast)
  qed
next show \<open>\<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). \<forall>l\<in>nodes (graphI y). enables y l (Actor a) move \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). \<forall>l\<in>nodes (graphI z). enables z l (Actor a) move\<close>
    apply (clarify, simp add: Ini_def ex_graph_def local_policies_def  nodes_def enables_def
         London_def Coastal_def NonCoastal_def, erule exE)
    apply (erule state_transition_in.cases)
    sorry
(*
    apply (smt (z3) delta_simps graphI_simps igraph.sel(1) init_state_policy local_policies_def put put_graph_a_def same_actors0)
    apply (smt (z3) London_def Coastal_def One_nat_def NonCoastal_def delta_simps empty_iff eval eval_graph_a_def ex_graph_def graphI_simps igraph.sel(1) init_state_policy insert_commute local_policies_def same_actors0)
    apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
proof -
  fix yb :: infrastructure and z :: infrastructure and a :: "char list" and l :: location and ya :: location and G :: igraph and I :: infrastructure and aa :: "char list" and la :: location and l' :: location and I' :: infrastructure and x :: "(actor \<Rightarrow> bool) \<times> action set"
  assume a1: "case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor aa)"
assume a2: "x \<in> delta I (graphI I) l'"
  assume a3: "(Infrastructure (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass ex_data black_box ex_attendance) local_policies, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  then have "local_policies (graphI I) l' = {(\<lambda>a. True, {get, move, put, eval})}"
    sorry
    using a2 by (metis (no_types) delta_simps empty_iff init_state_policy local_policies_def)
    then show "case x of (p, A) \<Rightarrow> move \<in> A \<and> p (Actor a)"
using a3 a2 a1 init_state_policy by fastforce
next show \<open>\<And>y z a l ya G I aa la l' I' x.
       (Infrastructure
         (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass
           ex_data black_box ex_attendance)
         local_policies,
        I)
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall>a\<in>actors_graph (graphI I).
          \<forall>l. (\<exists>y. (l, y) \<in> gra (graphI I) \<or> (y, l) \<in> gra (graphI I)) \<longrightarrow>
              (\<exists>x\<in>delta I (graphI I) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)) \<Longrightarrow>
       a \<in> actors_graph (move_graph_a aa la l' (graphI I)) \<Longrightarrow>
       (l, ya) \<in> gra (move_graph_a aa la l' (graphI I)) \<or> (ya, l) \<in> gra (move_graph_a aa la l' (graphI I)) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = Infrastructure (move_graph_a aa la l' (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>graphI I\<^esub> la \<Longrightarrow>
       la \<in> nodes (graphI I) \<Longrightarrow>
       l' \<in> nodes (graphI I) \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       I' = Infrastructure (move_graph_a aa la l' (graphI I)) (delta I) \<Longrightarrow>
       x \<in> delta I (graphI I) l' \<Longrightarrow>
       case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor aa) \<Longrightarrow> x \<in> delta I (move_graph_a aa la l' (graphI I)) l\<close>
    apply (simp add: move_graph_a_def local_policies_def init_state_policy)
    by (smt (z3) delta_simps empty_iff init_state_policy local_policies_def)
next show \<open>\<And>y z a l ya G I aa la I' m.
       (Infrastructure
         (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass
           ex_data black_box ex_attendance)
         local_policies,
        y)
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall>a\<in>actors_graph (graphI y).
          \<forall>l. (\<exists>ya. (l, ya) \<in> gra (graphI y) \<or> (ya, l) \<in> gra (graphI y)) \<longrightarrow>
              (\<exists>x\<in>delta y (graphI y) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)) \<Longrightarrow>
       a \<in> actors_graph (graphI z) \<Longrightarrow>
       (l, ya) \<in> gra (graphI z) \<or> (ya, l) \<in> gra (graphI z) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> nodes G \<Longrightarrow>
       enables I la (Actor aa) get \<Longrightarrow>
       I' = Infrastructure (get_graph_a aa la m G) (delta I) \<Longrightarrow>
       \<exists>x\<in>delta z (graphI z) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a) \<close>
     apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
proof -
fix yb :: infrastructure and z :: infrastructure and a :: "char list" and l :: location and ya :: location and G :: igraph and I :: infrastructure and aa :: "char list" and la :: location and I' :: infrastructure and m :: nat and x :: "(actor \<Rightarrow> bool) \<times> action set"
  assume "G = graphI I"
  assume a1: "x \<in> delta I (graphI I) la"
assume "(Infrastructure (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass ex_data black_box ex_attendance) local_policies, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  then have f2: "delta I = local_policies"
    by (smt (z3) delta_simps init_state_policy)
  have "\<forall>p pa. \<exists>paa A. ((case p of (x::actor \<Rightarrow> bool, xa::action set) \<Rightarrow> pa x xa) \<or> (paa, A) = p) \<and> (\<not> pa paa A \<or> (case p of (x, xa) \<Rightarrow> pa x xa))"
  by auto
then show "case x of (p, A) \<Rightarrow> move \<in> A \<and> p (Actor a)"
  using f2 a1 by (smt (z3) empty_iff fst_conv insertI1 insert_iff local_policies_def snd_conv)
next show \<open>\<And>y z a l ya G I aa la I' m x.
       (Infrastructure
         (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass
           ex_data black_box ex_attendance)
         local_policies,
        I)
       \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall>a\<in>actors_graph (graphI I).
          \<forall>l. (\<exists>ya. (l, ya) \<in> gra (graphI I) \<or> (ya, l) \<in> gra (graphI I)) \<longrightarrow>
              (\<exists>x\<in>delta I (graphI I) l. case x of (p, e) \<Rightarrow> move \<in> e \<and> p (Actor a)) \<Longrightarrow>
       a \<in> actors_graph (get_graph_a aa la m (graphI I)) \<Longrightarrow>
       (l, ya) \<in> gra (get_graph_a aa la m (graphI I)) \<or> (ya, l) \<in> gra (get_graph_a aa la m (graphI I)) \<Longrightarrow>
       y = I \<Longrightarrow>
       z = Infrastructure (get_graph_a aa la m (graphI I)) (delta I) \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>graphI I\<^esub> la \<Longrightarrow>
       la \<in> nodes (graphI I) \<Longrightarrow>
       I' = Infrastructure (get_graph_a aa la m (graphI I)) (delta I) \<Longrightarrow>
       x \<in> delta I (graphI I) la \<Longrightarrow>
       case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor aa) \<Longrightarrow> x \<in> delta I (get_graph_a aa la m (graphI I)) l \<close>
    apply (simp add: get_graph_a_def init_state_policy local_policies_def actors_graph_def atI_def, erule exE)
    by (smt (z3) delta_simps empty_iff init_state_policy local_policies_def)
qed
*)
qed

lemma enables_move: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) move\<close>
  using enables_move0 by blast


(*
lemma enables_get0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           \<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y). enables y l (Actor a) get\<close>
proof (erule rtrancl_induct)
  show \<open>\<forall>a\<in>actors_graph (graphI Ini). \<forall>l\<in>nodes (graphI Ini). enables Ini l (Actor a) get\<close>
    by (simp add: Ini_def enables_def ex_graph_def local_policies_def nodes_def)
next show \<open>\<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). \<forall>l\<in>nodes (graphI y). enables y l (Actor a) get \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). \<forall>l\<in>nodes (graphI z). enables z l (Actor a) get \<close>
    apply (clarify, simp add: Ini_def ex_graph_def local_policies_def  nodes_def enables_def
         London_def Coastal_def NonCoastal_def, erule exE)
    apply (erule state_transition_in.cases)
    apply (smt (z3) Coastal_def delta_simps igraph.sel(1) graphI_simps init_state_policy local_policies_def put put_graph_a_def same_actors0)
    apply (smt (z3) London_def Coastal_def One_nat_def NonCoastal_def delta_simps empty_iff eval eval_graph_a_def ex_graph_def igraph.sel(1) graphI_simps init_state_policy local_policies_def same_actors0)
     apply (simp add: enables_def)
    apply (erule bexE)
       apply (rule_tac x = x in bexI)
    sorry
    apply (smt (z3) bex_empty case_prodI2 delta_simps fst_conv init_state_policy insert_iff local_policies_def snd_conv)
    apply (simp add: move_graph_a_def local_policies_def init_state_policy)
    apply (smt (z3) all_not_in_conv delta_simps init_state_policy local_policies_def)
     apply (simp add: enables_def)
    apply (erule bexE)
     apply (rule_tac x = x in bexI)
    apply (smt (z3) Pair_inject bex_empty case_prodE case_prodI2 delta_simps init_state_policy insertE local_policies_def)
    apply (simp add: get_graph_a_def local_policies_def init_state_policy)
proof -
fix yb :: infrastructure and z :: infrastructure and a :: "char list" and l :: location and ya :: location and G :: igraph and I :: infrastructure and aa :: "char list" and la :: location and I' :: infrastructure and m :: nat and x :: "(actor \<Rightarrow> bool) \<times> action set"
  assume a1: "G = graphI I"
  assume a2: "x \<in> delta I (graphI I) la"
  assume a3: "(l, ya) \<in> gra (graphI I) \<or> (ya, l) \<in> gra (graphI I)"
  assume a4: "\<forall>a\<in>actors_graph (graphI I). \<forall>l. (\<exists>y. (l, y) \<in> gra (graphI I) \<or> (y, l) \<in> gra (graphI I)) \<longrightarrow> (\<exists>x\<in>delta I (graphI I) l. case x of (p, e) \<Rightarrow> get \<in> e \<and> p (Actor a))"
  assume a5: "(Infrastructure (Lgraph {(Location 0, Location (Suc 0)), (Location 0, Location 2), (Location (Suc 0), Location 2)} ex_loc_ass ex_data black_box ex_attendance) local_policies, I) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>*"
  assume a6: "a \<in> actors_graph (Lgraph (gra (graphI I)) (agra (graphI I)) ((dgra (graphI I)) (aa := (fst (dgra (graphI I) aa), fst (snd (dgra (graphI I) aa)), m, snd (snd (snd (dgra (graphI I) aa)))))) (bb (graphI I)) (attendancce (graphI I)))"
  assume "I' = Infrastructure (Lgraph (gra (graphI I)) (agra (graphI I)) ((dgra (graphI I)) (aa := (fst (dgra (graphI I) aa), fst (snd (dgra (graphI I) aa)), m, snd (snd (snd (dgra (graphI I) aa)))))) (bb (graphI I)) (attendance (graphI I))) (delta I)"
  have f7: "a \<in> {cs. \<exists>l. l \<in> {l. \<exists>la. (l, la) \<in> gra G \<or> (la, l) \<in> gra G} \<and> cs \<in> agra G l}"
    using a6 a1 by (simp add: actors_graph_def nodes_def)
  have "\<forall>l cs. \<exists>p. \<forall>la lb. ((l, la) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> p \<in> delta I (graphI I) l) \<and> ((lb, l) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> p \<in> delta I (graphI I) l)"
    using a4 by blast
  then obtain pp :: "location \<Rightarrow> char list \<Rightarrow> (actor \<Rightarrow> bool) \<times> action set" where
    f8: "\<And>l la cs lb. ((l, la) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> pp l cs \<in> delta I (graphI I) l) \<and> ((lb, l) \<notin> gra (graphI I) \<or> cs \<notin> actors_graph (graphI I) \<or> pp l cs \<in> delta I (graphI I) l)"
    by (metis (no_types))
  then have f9: "\<And>l la. (l, la) \<notin> gra G \<or> pp la a \<in> delta I G la"
    using f7 a1 actors_graph_def nodes_def by blast
  have "\<And>l la. (l, la) \<notin> gra G \<or> pp l a \<in> delta I G l"
    using f8 f7 a1 actors_graph_def nodes_def by blast
  then show "x \<in> delta I (Lgraph (gra (graphI I)) (agra (graphI I)) ((dgra (graphI I)) (aa := (fst (dgra (graphI I) aa), fst (snd (dgra (graphI I) aa)), m, snd (snd (snd (dgra (graphI I) aa)))))) (bb (graphI I)) (attendance (graphI I))) l"
    using f9 a5 a3 a2 a1 by (smt (z3) delta_simps empty_iff init_state_policy local_policies_def)
qed
qed
*)


(*
lemma enables_get: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) get\<close>
  using enables_get0 by blast
*)

lemma enables_put0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
       \<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y). enables y l (Actor a) put\<close>
proof (erule rtrancl_induct)
  show \<open>\<forall>a\<in>actors_graph (graphI Ini). \<forall>l\<in>nodes (graphI Ini). enables Ini l (Actor a) put\<close>
   by (simp add: Ini_def enables_def ex_graph_def local_policies_def nodes_def)
next show \<open>\<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). \<forall>l\<in>nodes (graphI y). enables y l (Actor a) put \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). \<forall>l\<in>nodes (graphI z). enables z l (Actor a) put \<close>
    by (smt (verit, ccfv_threshold) Ini_def case_prod_conv delta_simps delta_invariant enables_def enables_move0 init_state_policy local_policies_def mem_Collect_eq same_actors0 same_nodes0)
qed


lemma enables_put: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) put\<close>
  using enables_put0 by blast



lemma enables_eval0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> 
              \<forall> a \<in> actors_graph (graphI y). \<forall> l \<in> nodes (graphI y). enables y l (Actor a) eval\<close>
proof (erule rtrancl_induct)
  show \<open>\<forall>a\<in>actors_graph (graphI Ini). \<forall>l\<in>nodes (graphI Ini). enables Ini l (Actor a) eval\<close>
    by (simp add: Ini_def enables_def ex_graph_def local_policies_def nodes_def actors_graph_def 
           Coastal_def London_def NonCoastal_def ex_loc_ass_def)
 next show \<open> \<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). \<forall>l\<in>nodes (graphI y). enables y l (Actor a) eval \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). \<forall>l\<in>nodes (graphI z). enables z l (Actor a) eval \<close>
     by (smt (verit, best) Ini_def enables_def infrastructure.sel(2) init_state_policy local_policies_def r_into_rtrancl same_actors same_nodes)
 qed

lemma enables_eval: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> a \<in> actors_graph (graphI y)
                   \<Longrightarrow> l \<in> nodes (graphI y) \<Longrightarrow>  enables y l (Actor a) eval\<close>
  using enables_eval0 by blast



lemma dgra_inv0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> \<forall> a \<in> actors_graph (graphI y). fst (dgra (graphI Ini) a) = fst (dgra (graphI y) a)\<close>
proof (erule rtrancl_induct, rule ballI, rule refl)
  show \<open> \<And>y z. (Ini, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI y). fst (dgra (graphI Ini) a) = fst (dgra (graphI y) a) \<Longrightarrow>
           \<forall>a\<in>actors_graph (graphI z). fst (dgra (graphI Ini) a) = fst (dgra (graphI z) a)\<close>
    apply (clarify, simp add: Ini_def ex_graph_def ex_data_def)
    apply (erule state_transition_in.cases)
    apply (smt (verit) fun_upd_apply igraph.sel(3) infrastructure.sel(1) list.sel(3) list.simps(3) move move_graph_a_def prod.sel(1) same_actors0)
    apply (smt (z3) char.inject igraph.sel(3) fst_conv graphI_simps list.inject put put_graph_a_def same_actors0)
     apply (simp add: move_graph_a_def same_actors0)
    apply (smt (verit) delete delete_graph_a_def fst_conv fun_upd_apply igraph.sel(3) infrastructure.sel(1) list.sel(3) list.simps(3) same_actors0)
    by (smt (verit) eval eval_graph_a_def fst_conv igraph.sel(3) infrastructure.sel(1) list.sel(3) list.simps(3) same_actors0)
qed

lemma dgra_inv: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> a \<in> actors_graph (graphI y) \<Longrightarrow> fst (dgra (graphI Ini) a) = fst (dgra (graphI y) a)\<close>
  using dgra_inv0 by blast


text \<open>The above lemma is all great but it doesn't reflect really what we had in mind because we want to
use the precondition to simplify the proof. Luckily, we can use the CTL formulas more flexibly than in the usual
CTL as in usual modelcheckers since our formulas are HOL. \<close>

lemma same_dgra_loc0[rule_format]: \<open>\<forall> z z'. (z \<rightarrow>\<^sub>n z') \<longrightarrow> 
   (\<forall> l \<in> nodes (graphI z).
   (\<forall> a \<in> actors_graph (graphI z). ((fst (snd (dgra (graphI z) a))) = l) = (a \<in> (agra (graphI z) l))))
\<longrightarrow> (\<forall> l \<in>  nodes (graphI z').
   (\<forall> a \<in> actors_graph (graphI z'). ((fst (snd (dgra (graphI z') a))) = l) = (a \<in> (agra (graphI z') l))))\<close>
proof (clarify, erule state_transition_in.cases)
  show \<open>\<And>z z' l a G I aa la I'.
       \<forall>l\<in>nodes (graphI z).
          \<forall>a\<in>actors_graph (graphI z). (fst (snd (dgra (graphI z) a)) = l) = (a \<in> agra (graphI z) l) \<Longrightarrow>
       l \<in> nodes (graphI z') \<Longrightarrow>
       a \<in> actors_graph (graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> nodes G \<Longrightarrow>
       enables I la (Actor aa) put \<Longrightarrow>
       I' = Infrastructure (put_graph_a aa la G) (delta I) \<Longrightarrow>
       (fst (snd (dgra (graphI z') a)) = l) = (a \<in> agra (graphI z') l)\<close>
    by (simp add: actors_graph_def nodes_def put_graph_a_def)
next show \<open>\<And>z z' l a G I aa la c I'.
       \<forall>l\<in>nodes (graphI z).
          \<forall>a\<in>actors_graph (graphI z). (fst (snd (dgra (graphI z) a)) = l) = (a \<in> agra (graphI z) l) \<Longrightarrow>
       l \<in> nodes (graphI z') \<Longrightarrow>
       a \<in> actors_graph (graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> nodes G \<Longrightarrow>
       c \<in> actors_graph G \<Longrightarrow>
       Actor c \<in> readers (dgra G aa) \<or> Actor c = owner (dgra G aa) \<Longrightarrow>
       enables I la (Actor c) eval \<Longrightarrow>
       I' = Infrastructure (eval_graph_a aa G) (delta I) \<Longrightarrow>
       (fst (snd (dgra (graphI z') a)) = l) = (a \<in> agra (graphI z') l) \<close>
    by (simp add: actors_graph_def eval_graph_a_def nodes_def)
next show \<open>\<And>z z' l a G I aa la l' I'.
       \<forall>l\<in>nodes (graphI z).
          \<forall>a\<in>actors_graph (graphI z). (fst (snd (dgra (graphI z) a)) = l) = (a \<in> agra (graphI z) l) \<Longrightarrow>
       l \<in> nodes (graphI z') \<Longrightarrow>
       a \<in> actors_graph (graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> nodes G \<Longrightarrow>
       l' \<in> nodes G \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       enables I l' (Actor aa) move \<Longrightarrow>
       I' = Infrastructure (move_graph_a aa la l' G) (delta I) \<Longrightarrow>
       (fst (snd (dgra (graphI z') a)) = l) = (a \<in> agra (graphI z') l)\<close>
    apply (simp add: move_graph_a_def move atI_def nodes_def actors_graph_def)
    apply (rule conjI)
     apply (metis (no_types, lifting))
    apply (rule impI)+
    apply (rule conjI)
     apply (erule exE)+
     apply (rule impI)+
     apply (rule conjI)
      apply (erule conjE)+
      apply (erule exE)+
    apply (rule impI)+
    apply (rule conjI)
       apply force
      apply (rule impI)
    apply auto[1]
      apply (rule impI)
     apply (rule conjI)
      apply (erule conjE)+
      apply (erule exE)+
      apply (rule impI)
    apply (smt (z3) fun_upd_apply insertCI insertE insert_Diff)
      apply (erule conjE)+
      apply (erule exE)+
      apply (rule impI)
    apply metis
      apply (erule exE)+
      apply (erule conjE)+
      apply (erule exE)+
    apply (rule impI)+
    apply (rule conjI)
     apply (rule impI)
     apply (rule conjI)
      apply (rule impI)
    apply (smt (z3) Diff_iff fun_upd_apply insert_iff)
      apply (rule impI)
    apply metis
      apply (rule impI)
     apply (rule conjI)
    apply (smt (z3) Diff_iff fun_upd_apply insert_iff)
      apply (rule impI)
    by auto[1]
next show \<open>\<And>z z' l a G I aa la d I'.
       \<forall>l\<in>nodes (graphI z).
          \<forall>a\<in>actors_graph (graphI z). (fst (snd (dgra (graphI z) a)) = l) = (a \<in> agra (graphI z) l) \<Longrightarrow>
       l \<in> nodes (graphI z') \<Longrightarrow>
       a \<in> actors_graph (graphI z') \<Longrightarrow>
       z = I \<Longrightarrow>
       z' = I' \<Longrightarrow>
       G = graphI I \<Longrightarrow>
       aa @\<^bsub>G\<^esub> la \<Longrightarrow>
       la \<in> nodes G \<Longrightarrow>
       aa \<in> actors_graph (graphI I) \<Longrightarrow>
       d \<in> fst (snd (snd (dgra G aa))) \<Longrightarrow>
       enables I la (Actor aa) delete \<Longrightarrow>
       I' = Infrastructure (delete_graph_a aa d G) (delta I) \<Longrightarrow>
       (fst (snd (dgra (graphI z') a)) = l) = (a \<in> agra (graphI z') l)\<close>
    by (smt (z3) igraph.sel(2) igraph.sel(3) fst_conv fun_upd_apply delete delete_graph_a_def graphI_simps same_actors0 same_nodes0 snd_conv)
qed


lemma same_dgra_loc: \<open>(I, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> 
(\<forall> l \<in> nodes (graphI I).
   (\<forall> a \<in> actors_graph (graphI I).((fst (snd (dgra (graphI I) a))) = l) = (a \<in> (agra (graphI I) l))))
\<longrightarrow>
(\<forall> l \<in> nodes (graphI y).
   (\<forall> a \<in> actors_graph (graphI y).
((fst (snd (dgra (graphI y) a))) = l) = (a \<in> (agra (graphI y) l)))) \<close>
proof (erule rtrancl_induct)
  show \<open>(\<forall>l\<in>nodes (graphI I).
        \<forall>a\<in>actors_graph (graphI I). (fst (snd (dgra (graphI I) a)) = l) = (a \<in> agra (graphI I) l)) \<longrightarrow>
    (\<forall>l\<in>nodes (graphI I). \<forall>a\<in>actors_graph (graphI I). (fst (snd (dgra (graphI I) a)) = l) = (a \<in> agra (graphI I) l))\<close>
    by blast
next show \<open>\<And>y z. (I, y) \<in> {(x, y). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow>
           (y, z) \<in> {(x, y). x \<rightarrow>\<^sub>n y} \<Longrightarrow>
           (\<forall>l\<in>nodes (graphI I).
               \<forall>a\<in>actors_graph (graphI I). (fst (snd (dgra (graphI I) a)) = l) = (a \<in> agra (graphI I) l)) \<longrightarrow>
           (\<forall>l\<in>nodes (graphI y).
               \<forall>a\<in>actors_graph (graphI y). (fst (snd (dgra (graphI y) a)) = l) = (a \<in> agra (graphI y) l)) \<Longrightarrow>
           (\<forall>l\<in>nodes (graphI I).
               \<forall>a\<in>actors_graph (graphI I). (fst (snd (dgra (graphI I) a)) = l) = (a \<in> agra (graphI I) l)) \<longrightarrow>
           (\<forall>l\<in>nodes (graphI z).
               \<forall>a\<in>actors_graph (graphI z). (fst (snd (dgra (graphI z) a)) = l) = (a \<in> agra (graphI z) l)) \<close>
    using same_dgra_loc0 by force
qed

lemma same_dgra_loc_Ini: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* 
                   \<Longrightarrow> 
(\<forall> l \<in> nodes (graphI Ini).
   (\<forall> a \<in> actors_graph (graphI Ini).((fst (snd (dgra (graphI Ini) a))) = l) = (a \<in> (agra (graphI Ini) l))))
\<Longrightarrow>
(\<forall> l \<in> nodes (graphI y).
   (\<forall> a \<in> actors_graph (graphI y).
((fst (snd (dgra (graphI y) a))) = l) = (a \<in> (agra (graphI y) l)))) \<close>
  using AttendanceScoring.same_dgra_loc by presburger

lemma same_dgra_loc_Ini0: \<open>(Ini, y) \<in> {(x::infrastructure, y::infrastructure). x \<rightarrow>\<^sub>n y}\<^sup>* \<Longrightarrow> 
       (\<forall> l \<in> nodes (graphI Ini). \<forall> a \<in> actors_graph (graphI Ini).
       ((fst (snd (dgra (graphI Ini) a))) = l) = (a \<in> (agra (graphI Ini) l))) \<Longrightarrow> 
       l \<in> nodes (graphI Ini) \<Longrightarrow> a \<in> actors_graph (graphI Ini) \<Longrightarrow>
       ((fst (snd (dgra (graphI y) a))) = l) = (a \<in> (agra (graphI y) l)) \<close>
  using same_actors same_dgra_loc_Ini same_nodes by blast

lemma same_gra_loc_Ini_ini: \<open>\<forall>l\<in>nodes (graphI Ini).
            \<forall>a\<in>actors_graph (graphI Ini). (fst (snd (dgra (graphI Ini) a)) = l) = (a \<in> agra (graphI Ini) l)\<close>
  by (simp add: actors_graph_def Ini_def ex_graph_def ex_data_def ex_loc_ass_def)



text \<open>This formulation does in fact use the precondition as intended. Since we have a HIL-CTL we can
have a CTL formula within another one. Thereby, we can draw the pc1 as a proper precondition in front
(bound under AG) and have the EF part only after the implication. The following proof is thus
much simpler because we can assume that the actor is at N3 and has a salary greater than 40K 
provided by pc1 and on that assumption we only have to show that from there we can achieve that the
credit will be approved. \<close>
lemma pc3_AG: \<open>\<forall> A \<in> AttendanceScoring_actors. M \<turnstile> AG {s. pc3 A s \<longrightarrow> s \<in> EF{x. DO A x}}\<close>
  proof (simp add: AttendanceScoring_actors_def M_def Attendance_Kripke_def check_def, rule conjI)
  show \<open>Ini \<in> Attendance_states\<close>
    by (simp add: Attendance_states_def state_transition_refl_def)
next show \<open>Ini \<in> AG {s. pc3 ''Alice'' s \<longrightarrow> s \<in> EF (Collect (DO ''Alice''))} \<and>
    Ini \<in> Attendance_states \<and>
    Ini \<in> AG {s. pc3 ''Bob'' s \<longrightarrow> s \<in> EF (Collect (DO ''Bob''))} \<and>
    Ini \<in> Attendance_states \<and> Ini \<in> AG {s. pc3 ''ED'' s \<longrightarrow> s \<in> EF (Collect (DO ''ED''))}\<close>
  proof
    show \<open>Ini \<in> AG {s. pc3 ''Alice'' s \<longrightarrow> s \<in> EF (Collect (DO ''Alice''))}\<close>
      apply (rule AG_all_sO)
      apply (rule allI, rule impI)
      apply (rule CollectI)
      apply (rule impI)
(* That's what we wanted to have as a proof goal; pc1 implies the DO is reachable:
\<And>y. Ini \<rightarrow>\<^sub>i* y \<Longrightarrow> pc1 ''Alice'' y \<Longrightarrow> y \<in> EF (Collect (DO ''Alice''))*)
      apply (simp add: pc3_def)
      apply (erule conjE)
      apply (rule_tac y = \<open>Infrastructure (
                             eval_graph_a ''Alice'' (
                             put_graph_a ''Alice'' London (graphI y))) (delta y)\<close> in EF_step_star)
         prefer 2
       apply (simp add: eval_graph_a_def put_graph_a_def DO_def disadvantage_set_def)
         apply (subgoal_tac \<open>bb (graphI y) = bb(graphI Ini)\<close>)
        apply (subgoal_tac \<open>bb (graphI y) = black_box\<close>)
         apply (rule disjI1)
      apply (rotate_tac -1)
         apply (erule ssubst)
         apply (simp add: black_box_def NonCoastal_def Coastal_def London_def Ini_def atI_def)
      thm same_dgra_loc
         apply (rule impI)
         apply (subgoal_tac \<open>(fst (snd (dgra (graphI y) ''Alice''))) = Location 2\<close>)
      apply simp
         apply (subst same_dgra_loc_Ini0)
    apply (smt (z3) Collect_cong Ini_def le_boolD order_refl prod.split_sel_asm state_transition_infra_def state_transition_refl_def)
      using same_gra_loc_Ini_ini apply blast
      using Ini_def London_def ex_graph_def nodes_def apply auto[1]
      using Alice_Bob_in_Attendance_Kripke AttendanceScoring.step_rtrancl Attendance_Kripke_def Attendance_states_def same_actors0 stepI_C apply force
         apply assumption
        apply (simp add: black_box_def Ini_def ex_graph_def)
         apply (rule sym, rule same_bb)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
(* *)
      apply (subgoal_tac \<open>y \<rightarrow>\<^sub>i*  Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y)\<close>)
      apply (subgoal_tac \<open>Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y) \<rightarrow>\<^sub>i*
                          Infrastructure (eval_graph_a ''Alice'' 
                                           (put_graph_a ''Alice'' London (graphI y))) (delta y)\<close>)
        apply (simp add: state_transition_infra_def state_transition_refl_def)  
       prefer 2
        apply (rule step_rtrancl)
       apply (rule_tac G = \<open>graphI y\<close> and a = \<open>''Alice''\<close> and l = London in state_transition_in.put)
      apply (rule refl)
          apply assumption
      apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: same_nodes Ini_def ex_graph_def nodes_def, blast)
        apply (rule enables_put)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
              apply (simp add: actors_graph_def atI_def)
      using Alice_Bob_in_Attendance_Kripke Attendance_Kripke_def Attendance_states_def actors_graph_def  apply auto[1]
         apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
      using Ini_def ex_graph_def nodes_def apply auto[1]
       apply (rule refl)
(* 1 *)
         apply (rule step_rtrancl)
        apply (rule_tac G = \<open>put_graph_a ''Alice'' London (graphI y)\<close> and a = \<open>''Alice''\<close> and
                         l = London and c = \<open>''ED''\<close> in state_transition_in.eval)
      apply simp
            apply (simp add: atI_def eval_graph_a_def put_graph_a_def)
      thm same_nodes
           apply (subgoal_tac "nodes (graphI(Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y))) = nodes (graphI Ini)")
      using Ini_def ex_graph_def nodes_def apply auto[1]
           apply (rule sym)
           apply (subgoal_tac \<open>nodes (graphI Ini) = nodes(graphI y)\<close>)
      apply (subgoal_tac \<open>nodes(graphI y) = nodes (graphI (Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y)))\<close>)
             apply simp
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def Ini_def put_graph_a_def)
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (smt (verit, ccfv_SIG) Alice_Bob_in_Attendance_Kripke CollectI Collect_cong Attendance_Kripke_def Attendance_states_def graphI_simps insertI1 insert_commute le_boolD order_refl prod.split_sel_asm same_actors state_transition_infra_def state_transition_refl_def states.simps)
         apply (simp add: put_graph_a_def)
        apply (rule disjI1)
        apply (subgoal_tac \<open>fst (dgra (graphI Ini) ''Alice'') = fst (dgra (graphI y) ''Alice'')\<close>)
         apply (subgoal_tac \<open>fst (dgra (graphI y) ''Alice'') = fst(dgra (put_graph_a ''Alice'' London (graphI y)) ''Alice'')\<close>)
          apply (unfold readers_def)
          apply (rotate_tac -1)
          apply (erule subst)
          apply (erule subst)
          apply (simp add: Ini_def ex_graph_def ex_data_def)
         apply (simp add: put_graph_a_def)
        apply (rule dgra_inv)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: Alice_Bob_in_Attendance_Kripke Attendance_Kripke_def Attendance_states_def)
          apply (rule enables_eval)
          apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (smt (verit, best) Alice_Bob_in_Attendance_Kripke CollectI Collect_cong Attendance_Kripke_def Attendance_states_def insertI1 insert_commute le_boolD order_refl prod.split_sel_asm same_actors state_transition_infra_def state_transition_refl_def states.simps)
           apply (subgoal_tac "nodes (graphI(Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y))) = nodes (graphI Ini)")
      using Ini_def ex_graph_def nodes_def apply auto[1]
           apply (rule sym)
           apply (subgoal_tac \<open>nodes (graphI Ini) = nodes(graphI y)\<close>)
      apply (subgoal_tac \<open>nodes(graphI y) = nodes (graphI (Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y)))\<close>)
             apply simp
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def Ini_def put_graph_a_def)
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (subgoal_tac \<open>(delta (Infrastructure (put_graph_a ''Alice'' London (graphI y)) (delta y))) = delta y\<close>)
       apply simp
      using delta_simps by blast
   next show \<open>Ini \<in> Attendance_states \<and>
    Ini \<in> AG {s. pc3 ''Bob'' s \<longrightarrow> s \<in> EF (Collect (DO ''Bob''))} \<and>
    Ini \<in> Attendance_states \<and> Ini \<in> AG {s. pc3 ''ED'' s \<longrightarrow> s \<in> EF (Collect (DO ''ED''))}\<close>
    proof
      show \<open> Ini \<in> Attendance_states\<close>     
        by (simp add: Attendance_states_def state_transition_refl_def)
    next show \<open>Ini \<in> AG {s. pc3 ''Bob'' s \<longrightarrow> s \<in> EF (Collect (DO ''Bob''))} \<and>
    Ini \<in> Attendance_states \<and> Ini \<in> AG {s. pc3 ''ED'' s \<longrightarrow> s \<in> EF (Collect (DO ''ED''))}\<close>
      proof 
        show \<open>Ini \<in> AG {s. pc3 ''Bob'' s \<longrightarrow> s \<in> EF (Collect (DO ''Bob''))}\<close>
      apply (rule AG_all_sO)
      apply (rule allI, rule impI)
      apply (rule CollectI)
          apply (rule impI)
(* *)
      apply (simp add: pc3_def)
      apply (erule conjE)
      apply (rule_tac y = \<open>Infrastructure (
                             eval_graph_a ''Bob'' (
                             put_graph_a ''Bob'' London (graphI y))) (delta y)\<close> in EF_step_star)
           prefer 2
       apply (simp add: eval_graph_a_def put_graph_a_def DO_def disadvantage_set_def)
         apply (subgoal_tac \<open>bb (graphI y) = bb(graphI Ini)\<close>)
        apply (subgoal_tac \<open>bb (graphI y) = black_box\<close>)
         apply (rule disjI1)
      apply (rotate_tac -1)
      apply (erule ssubst)
             apply (simp add: black_box_def NonCoastal_def Coastal_def London_def Ini_def atI_def)
         apply (rule impI)
         apply (subgoal_tac \<open>(fst (snd (dgra (graphI y) ''Bob''))) = Location 2\<close>)
              apply simp
         apply (subst same_dgra_loc_Ini0)
      apply (smt (z3) Collect_cong Ini_def le_boolD order_refl prod.split_sel_asm state_transition_infra_def state_transition_refl_def)
      using same_gra_loc_Ini_ini apply blast
      using Ini_def London_def ex_graph_def nodes_def apply auto[1]
      using Alice_Bob_in_Attendance_Kripke AttendanceScoring.step_rtrancl Attendance_Kripke_def Attendance_states_def same_actors0 stepI_C apply force
         apply assumption
        apply (simp add: black_box_def Ini_def ex_graph_def)
         apply (rule sym, rule same_bb)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
(* *)
      apply (subgoal_tac \<open>y \<rightarrow>\<^sub>i*  Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y)\<close>)
      apply (subgoal_tac \<open>Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y) \<rightarrow>\<^sub>i*
                          Infrastructure (eval_graph_a ''Bob'' 
                                           (put_graph_a ''Bob'' London (graphI y))) (delta y)\<close>)
        apply (simp add: state_transition_infra_def state_transition_refl_def)  
       prefer 2
        apply (rule step_rtrancl)
       apply (rule_tac G = \<open>graphI y\<close> and a = \<open>''Bob''\<close> and l = London in state_transition_in.put)
      apply (rule refl)
          apply assumption
      apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: same_nodes Ini_def ex_graph_def nodes_def, blast)
        apply (rule enables_put)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
              apply (simp add: actors_graph_def atI_def)
      using Alice_Bob_in_Attendance_Kripke Attendance_Kripke_def Attendance_states_def actors_graph_def apply auto[1]
         apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
      using Ini_def ex_graph_def nodes_def apply auto[1]
       apply (rule refl)
(* 1 *)
         apply (rule step_rtrancl)
        apply (rule_tac G = \<open>put_graph_a ''Bob'' London (graphI y)\<close> and a = \<open>''Bob''\<close> and
                         l = London and c = \<open>''ED''\<close> in state_transition_in.eval)
      apply simp
            apply (simp add: atI_def eval_graph_a_def put_graph_a_def)
           apply (subgoal_tac "nodes (graphI(Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y))) = nodes (graphI Ini)")
      using Ini_def ex_graph_def nodes_def apply auto[1]
           apply (rule sym)
           apply (subgoal_tac \<open>nodes (graphI Ini) = nodes(graphI y)\<close>)
      apply (subgoal_tac \<open>nodes(graphI y) = nodes (graphI (Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y)))\<close>)
             apply simp
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def Ini_def put_graph_a_def)
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (smt (verit, ccfv_SIG) Alice_Bob_in_Attendance_Kripke CollectI Collect_cong Attendance_Kripke_def Attendance_states_def graphI_simps insertI1 insert_commute le_boolD order_refl prod.split_sel_asm same_actors state_transition_infra_def state_transition_refl_def states.simps)
         apply (simp add: put_graph_a_def)
        apply (rule disjI1)
        apply (subgoal_tac \<open>fst (dgra (graphI Ini) ''Bob'') = fst (dgra (graphI y) ''Bob'')\<close>)
         apply (subgoal_tac \<open>fst (dgra (graphI y) ''Bob'') = fst(dgra (put_graph_a ''Bob'' London (graphI y)) ''Bob'')\<close>)
          apply (unfold readers_def)
          apply (rotate_tac -1)
          apply (erule subst)
          apply (erule subst)
          apply (simp add: Ini_def ex_graph_def ex_data_def)
         apply (simp add: put_graph_a_def)
        apply (rule dgra_inv)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: Alice_Bob_in_Attendance_Kripke Attendance_Kripke_def Attendance_states_def)
          apply (rule enables_eval)
          apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (smt (verit, best) Alice_Bob_in_Attendance_Kripke CollectI Collect_cong Attendance_Kripke_def Attendance_states_def insertI1 insert_commute le_boolD order_refl prod.split_sel_asm same_actors state_transition_infra_def state_transition_refl_def states.simps)
           apply (subgoal_tac "nodes (graphI(Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y))) = nodes (graphI Ini)")
      using Ini_def ex_graph_def nodes_def apply auto[1]
           apply (rule sym)
           apply (subgoal_tac \<open>nodes (graphI Ini) = nodes(graphI y)\<close>)
      apply (subgoal_tac \<open>nodes(graphI y) = nodes (graphI (Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y)))\<close>)
             apply simp
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def Ini_def put_graph_a_def)
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (subgoal_tac \<open>(delta (Infrastructure (put_graph_a ''Bob'' London (graphI y)) (delta y))) = delta y\<close>)
       apply simp
      using delta_simps by blast
  next show \<open>Ini \<in> Attendance_states \<and> Ini \<in> AG {s. pc3 ''ED'' s \<longrightarrow> s \<in> EF (Collect (DO ''ED''))} \<close>
        proof 
          show \<open>Ini \<in> Attendance_states\<close>
        by (simp add: Attendance_states_def state_transition_refl_def)
    next show \<open> Ini \<in> AG {s. pc3 ''ED'' s \<longrightarrow> s \<in> EF (Collect (DO ''ED''))} \<close>
      apply (rule AG_all_sO)
      apply (rule allI, rule impI)
      apply (rule CollectI)
        apply (rule impI)
(* *)
      apply (simp add: pc3_def)
      apply (erule conjE)
      apply (rule_tac y = \<open>Infrastructure (
                             eval_graph_a ''ED'' (
                             put_graph_a ''ED'' London (graphI y))) (delta y)\<close> in EF_step_star)
           prefer 2
       apply (simp add: eval_graph_a_def put_graph_a_def DO_def disadvantage_set_def)
         apply (subgoal_tac \<open>bb (graphI y) = bb(graphI Ini)\<close>)
        apply (subgoal_tac \<open>bb (graphI y) = black_box\<close>)
         apply (rule disjI1)
      apply (rotate_tac -1)
      apply (erule ssubst)
         apply (simp add: black_box_def NonCoastal_def Coastal_def London_def Ini_def atI_def)
         apply (rule impI)
         apply (subgoal_tac \<open>(fst (snd (dgra (graphI y) ''ED''))) = Location 2\<close>)
      apply simp
         apply (subst same_dgra_loc_Ini0)
      apply (smt (z3) Collect_cong Ini_def le_boolD order_refl prod.split_sel_asm state_transition_infra_def state_transition_refl_def)
      using same_gra_loc_Ini_ini apply blast
      using Ini_def London_def ex_graph_def nodes_def apply auto[1]
      using Alice_Bob_in_Attendance_Kripke AttendanceScoring.step_rtrancl Attendance_Kripke_def Attendance_states_def same_actors0 stepI_C apply force
         apply assumption
        apply (simp add: black_box_def Ini_def ex_graph_def)
         apply (rule sym, rule same_bb)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
(* *)
      apply (subgoal_tac \<open>y \<rightarrow>\<^sub>i*  Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y)\<close>)
      apply (subgoal_tac \<open>Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y) \<rightarrow>\<^sub>i*
                          Infrastructure (eval_graph_a ''ED''
                                           (put_graph_a ''ED'' London (graphI y))) (delta y)\<close>)
        apply (simp add: state_transition_infra_def state_transition_refl_def)  
       prefer 2
        apply (rule step_rtrancl)
       apply (rule_tac G = \<open>graphI y\<close> and a = \<open>''ED''\<close> and l = London in state_transition_in.put)
      apply (rule refl)
          apply assumption
      apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: same_nodes Ini_def ex_graph_def nodes_def, blast)
        apply (rule enables_put)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
              apply (simp add: actors_graph_def atI_def)
      using Alice_Bob_in_Attendance_Kripke Attendance_Kripke_def Attendance_states_def actors_graph_def apply auto[1]
         apply (subst same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
              apply (simp add: actors_graph_def atI_def)
      using Ini_def ex_graph_def nodes_def apply auto[1]
       apply (rule refl)
(* 1 *)
         apply (rule step_rtrancl)
        apply (rule_tac G = \<open>put_graph_a ''ED'' London (graphI y)\<close> and a = \<open>''ED''\<close> and
                         l = London and c = \<open>''ED''\<close> in state_transition_in.eval)
      apply simp
            apply (simp add: atI_def eval_graph_a_def put_graph_a_def)
           apply (subgoal_tac "nodes (graphI(Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y))) = nodes (graphI Ini)")
      using Ini_def ex_graph_def nodes_def apply auto[1]
           apply (rule sym)
           apply (subgoal_tac \<open>nodes (graphI Ini) = nodes(graphI y)\<close>)
      apply (subgoal_tac \<open>nodes(graphI y) = nodes (graphI (Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y)))\<close>)
             apply simp
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def Ini_def put_graph_a_def)
           apply (rule sym)
             apply (rule same_nodes)
           apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (smt (verit, ccfv_SIG) Alice_Bob_in_Attendance_Kripke CollectI Collect_cong Attendance_Kripke_def Attendance_states_def graphI_simps insertI1 insert_commute le_boolD order_refl prod.split_sel_asm same_actors state_transition_infra_def state_transition_refl_def states.simps)
         apply (simp add: put_graph_a_def)
        apply (rule disjI2)
        apply (subgoal_tac \<open>fst (dgra (graphI Ini) ''ED'') = fst (dgra (graphI y) ''ED'')\<close>)
         apply (subgoal_tac \<open>fst (dgra (graphI y) ''ED'') = fst(dgra (put_graph_a ''ED'' London (graphI y)) ''ED'')\<close>)
          apply (unfold owner_def)
          apply (rotate_tac -1)
          apply (erule subst)
          apply (erule subst)
          apply (simp add: Ini_def ex_graph_def ex_data_def)
         apply (simp add: put_graph_a_def)
        apply (rule dgra_inv)
        apply (simp add: state_transition_infra_def state_transition_refl_def)
        apply (simp add: Alice_Bob_in_Attendance_Kripke Attendance_Kripke_def Attendance_states_def)
          apply (rule enables_eval)
          apply (simp add: state_transition_infra_def state_transition_refl_def)
      apply (smt (verit, best) Alice_Bob_in_Attendance_Kripke CollectI Collect_cong Attendance_Kripke_def Attendance_states_def insertI1 insert_commute le_boolD order_refl prod.split_sel_asm same_actors state_transition_infra_def state_transition_refl_def states.simps)
           apply (subgoal_tac "nodes (graphI(Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y))) = nodes (graphI Ini)")
      using Ini_def ex_graph_def nodes_def apply auto[1]
           apply (rule sym)
           apply (subgoal_tac \<open>nodes (graphI Ini) = nodes(graphI y)\<close>)
      apply (subgoal_tac \<open>nodes(graphI y) = nodes (graphI (Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y)))\<close>)
             apply simp
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def Ini_def put_graph_a_def)
           apply (rule sym)
             apply (rule same_nodes)
        apply (simp add: state_transition_infra_def state_transition_refl_def)

      
      apply (subgoal_tac \<open>(delta (Infrastructure (put_graph_a ''ED'' London (graphI y)) (delta y))) = delta y\<close>)
       apply simp
      using delta_simps by blast
    qed
  qed
qed
qed
qed


end
