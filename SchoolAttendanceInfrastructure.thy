section \<open>Infrastructures for School Attendance\<close>
text \<open>This theory provides the adaptation of the IIIf for School attendance.\<close>
subsection \<open>Actors, actions, and data labels\<close>
theory SchoolAttendanceInfrastructure
  imports Refinement
begin
datatype action = get | move | eval | put

typedecl actor 
type_synonym identity = string
consts Actor :: "string \<Rightarrow> actor"
type_synonym policy = "((actor \<Rightarrow> bool) * action set)"

definition ID :: "[actor, string] \<Rightarrow> bool"
  where "ID a s \<equiv> (a = Actor s)"

subsection \<open>Infrastructure graphs and policies\<close>
text\<open>Actors are contained in an infrastructure graph. An @{text \<open>igraph\<close>} contains
a set of location pairs representing the topology of the infrastructure
as a graph of nodes and a list of actor identities associated to each node 
(location) in the graph. \<close>
datatype location = Location nat

text \<open>The Decentralised Label Model (DLM) \cite{ml:98} introduced the idea to
label data by owners and readers. We pick up this idea and formalize
a new type to encode the owner and the set of readers as a pair.
The first element is the owner of a data item, the second one is the
set of all actors that may access the data item.
This enables the unique security 
labelling of data within the system additionally taking the ownership into 
account.\<close>
type_synonym dob = nat
datatype gender = male | female 
datatype ethnicity = black |  white | asian
(* special educational needs, free school meal, education health and care,
   ... *)
datatype disadvantaged = sen | fsm | ehc | csc | none
datatype year = nursery | reception | year1 | year2 | year3 | year4
  | year5 |year6 | year7 | year8 | year9 | year10 | year11 | year12
type_synonym data = \<open>location \<times> gender \<times> year \<times> ethnicity\<close>
type_synonym dlm = \<open>actor \<times> actor set\<close>
type_synonym absence = nat

datatype igraph = Lgraph 
                    (gra: \<open>(location \<times> location)set\<close>)
                    (agra: \<open>location \<Rightarrow> identity set\<close>)
                    (dgra: \<open> identity \<Rightarrow> dlm \<times> data\<close>)
                    (bb: \<open> data \<Rightarrow> bool\<close>)
                    (attendance: \<open>(identity \<times> absence)set\<close>)


end