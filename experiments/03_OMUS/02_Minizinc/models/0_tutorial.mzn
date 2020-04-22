% By Tias, for Holy Grail Challenge
%
% http://logicgridpuzzles.com/puzzles/logic_tutorial.php
%
% Let us first start by looking at our information. We have 4 people: Annabelle, Heather, Kassidy and Tatum. We have 4 different income levels, 54k, 128k, 144k and 158k. We also have 4 different colored houses: Blue, Cyan, Lime and Purple. Finally, we have 4 different medications: Benazepril, Enalapril, Fosinopril and Ramipril.
%
% 1) The 4 people were Tatum, the patient who was prescribed enalapril, the employee with the $54,000 salary, and the owner of the purple house.
% 2) Of Tatum and Annabelle, one earns $144,000 per year and the other lives in the cyan colored house.
% 2b) Of n1 and n2, one v1 and other c1
% 3) The patient who was prescribed enalapril is not Heather. 
% 4) Either the employee with the $144,000 salary or the employee with the $158,000 salary lives in the blue colored house.
% 5) Kassidy earns less than Heather.
% 6) The owner of the blue house earns more than Kassidy.
% 7) The patient who was prescribed ramipril is not Annabelle.
% 8) The owner of the lime house was prescribed enalapril for their heart condition.
% 9) The employee with the $144,000 salary was prescribed benazepril for their heart condition.


include "globals.mzn";

% Values
enum Name = {Annabelle, Heather, Kassidy, Tatum};
enum Salary = {v54000, v128000, v144000, v158000};
array[Salary] of int: vSalary = [54000, 128000, 144000, 158000];
enum House = {Blue, Cyan, Lime, Purple};
enum Prescribed = {Benazepril, Enalapril, Fosinopril, Ramipril};

% Matrix variables, all views
% Name:
array[Salary] of var Name: Name_Salary;
array[House] of var Name: Name_House;
array[Prescribed] of var Name: Name_Prescribed;
% vSalary:
array[Name] of var dom_array(vSalary): vSalary_Name;
array[House] of var dom_array(vSalary): vSalary_House;
array[Prescribed] of var dom_array(vSalary): vSalary_Prescribed;
% House:
array[Name] of var House: House_Name;
array[Salary] of var House: House_Salary;
array[Prescribed] of var House: House_Prescribed;
% Prescribed:
array[Name] of var Prescribed: Prescribed_Name;
array[Salary] of var Prescribed: Prescribed_Salary;
array[House] of var Prescribed: Prescribed_House;

% Uniqueness constraints, all
constraint all_different(Name_Salary) /\ all_different(Name_House) /\ all_different(Name_Prescribed);
constraint all_different(vSalary_Name) /\ all_different(vSalary_House) /\ all_different(vSalary_Prescribed);
constraint all_different(House_Name) /\ all_different(House_Salary) /\ all_different(House_Prescribed);
constraint all_different(Prescribed_Name) /\ all_different(Prescribed_Salary) /\ all_different(Prescribed_House);

% Symmetry connection constraints, upper triangle
constraint forall (s in Salary) ( vSalary_Name[Name_Salary[s]] = vSalary[s] );
constraint forall (s in Salary) ( vSalary_House[House_Salary[s]] = vSalary[s] );
constraint forall (s in Salary) ( vSalary_Prescribed[Prescribed_Salary[s]] = vSalary[s] );
constraint forall (n in Name) ( Name_House[House_Name[n]] = n );
constraint forall (n in Name) ( Name_Prescribed[Prescribed_Name[n]] = n );
constraint forall (h in House) ( House_Prescribed[Prescribed_House[h]] = h );

% Transitive connection constraints, upper triangle
% Name: Salary + House, Salary + Prescribed, House + Prescribed
constraint forall (s in Salary) ( Name_Salary[s] = Name_House[House_Salary[s]] );
constraint forall (s in Salary) ( Name_Salary[s] = Name_Prescribed[Prescribed_Salary[s]] );
constraint forall (h in House) ( Name_House[h] = Name_Prescribed[Prescribed_House[h]] );
% Prescribed: Salary + House, (Salary + Prescribed, House + Prescribed)
constraint forall (s in Salary) ( Prescribed_Salary[s] = Prescribed_House[House_Salary[s]] );
% (House: Salary + Prescribed)

% Alt: constraint forall (h in House, c in Prescribed) ( Name_House[h] = Name_Prescribed[c] <-> Prescribed_House[h] = c );
% constraint forall (h in House) ( Name_House[i] = Name_Prescribed[Prescribed_House[i]] );


% Clue constraints
% 1) The 4 people were Tatum, the patient who was prescribed enalapril, the employee with the $54,000 salary, and the owner of the purple house.
constraint all_different([Tatum, Name_Prescribed[Enalapril], Name_Salary[v54000], Name_House[Purple]]);
% Alt: Name_Prescribed[Enalapril] != Tatum /\
%      Name_Salary[v54000] != Tatum /\ Name_Salary[v54000] != Name_Prescribed[Enalapril] /\
%      Name_House[Purple] != Tatum /\ Name_House[Purple] != Name_Prescribed[Enalapril] /\ Name_House[Purple] != Name_Salary[v54000]

% 2) Of Tatum and Annabelle, one earns $144,000 per year and the other lives in the cyan colored house.
constraint Name_Salary[v144000] != Name_House[Cyan] /\
           Name_Salary[v144000] in {Tatum, Annabelle} /\
           Name_House[Cyan] in {Tatum, Annabelle};

% 3) The patient who was prescribed enalapril is not Heather. 
constraint Name_Prescribed[Enalapril] != Heather;

% 4) Either the employee with the $144,000 salary or the employee with the $158,000 salary lives in the blue colored house.
constraint vSalary_House[Blue] in {144000, 158000};

% 5) Kassidy earns less than Heather.
constraint vSalary_Name[Kassidy] < vSalary_Name[Heather];

% 6) The owner of the blue house earns more than Kassidy.
constraint vSalary_House[Blue] > vSalary_Name[Kassidy];

% 7) The patient who was prescribed ramipril is not Annabelle.
constraint Name_Prescribed[Ramipril] != Annabelle;

% 8) The owner of the lime house was prescribed enalapril for their heart condition.
% literal: Prescribed_Name[Name_House[Lime]] = Enalapril;
constraint Prescribed_House[Lime] = Enalapril;

% 9) The employee with the $144,000 salary was prescribed benazepril for their heart condition.
% literal: Prescribed_Name[Name_Salary[v144000]] = Benazepril;
constraint Prescribed_Salary[v144000] = Benazepril;

solve satisfy;

