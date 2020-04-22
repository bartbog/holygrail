% By Tias, for Holy Grail Challenge
%
% http://logicgridpuzzles.com/puzzles/logic_tutorial.php
%
% Let us first start by looking at our information. We have 4 people: Annabelle, Heather, Kassidy and Tatum. We have 4 different income levels, 54k, 128k, 144k and 158k. We also have 4 different colored houses: Blue, Cyan, Lime and Purple. Finally, we have 4 different medications: Benazepril, Enalapril, Fosinopril and Ramipril.
%
% 1) The 4 people were Tatum, the patient who was prescribed enalapril, the employee with the $54,000 salary, and the owner of the purple house.
% 2) Of Tatum and Annabelle, one earns $144,000 per year and the other lives in the cyan colored house.
% 3) The patient who was prescribed enalapril is not Heather. 
% 4) Either the employee with the $144,000 salary or the employee with the $158,000 salary lives in the blue colored house.
% 5) Kassidy earns less than Heather.
% 6) The owner of the blue house earns more than Kassidy.
% 7) The patient who was prescribed ramipril is not Annabelle.
% 8) The owner of the lime house was prescribed enalapril for their heart condition.
% 9) The employee with the $144,000 salary was prescribed benazepril for their heart condition.


include "globals.mzn";

% options
enum Name = {Annabelle, Heather, Kassidy, Tatum};
enum Salary = {v54000, v128000, v144000, v158000};
array[Salary] of int: vSalary = [54000, 128000, 144000, 158000];
enum House = {Blue, Cyan, Lime, Purple};
enum Prescribed = {Benazepril, Enalapril, Fosinopril, Ramipril};

% matrix variables
% Q: should we build the full matrix, so also the reverse indexed?, now for values, depends on having right order...
% this matrix actually swapped (name not first row), so perhaps we should
array[Salary] of var Name: Name_Salary;
array[House] of var Name: Name_House;
array[Prescribed] of var Name: Name_Prescribed;
array[House] of var dom_array(vSalary): vSalary_House;
array[Prescribed] of var dom_array(vSalary): vSalary_Prescribed;
array[House] of var Prescribed: Prescribed_House;

% uniqueness constraints
constraint all_different(Name_House) /\ all_different(Name_Prescribed) /\ all_different(Name_Salary);
constraint all_different(vSalary_House) /\ all_different(vSalary_Prescribed);
constraint all_different(Prescribed_House);

% connection constraints
constraint forall (i in House, c in Prescribed) (
                Name_House[i] = Name_Prescribed[c] <-> Prescribed_House[i] = c );
constraint forall (i in House, s in Salary) (
                Name_House[i] = Name_Salary[s] <-> vSalary_House[i] = vSalary[s] );
constraint forall (c in Prescribed, s in Salary) (
                Name_Prescribed[c] = Name_Salary[s] <-> vSalary_Prescribed[c] = vSalary[s] );

% Clue constraints
% 1) The 4 people were Tatum, the patient who was prescribed enalapril, the employee with the $54,000 salary, and the owner of the purple house.
constraint all_different(Tatum, Name_Prescribed[Enalapril], Name_Salary[v54000], Name_House[Purple]);
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
% XXX NEED different matrix view here!!
constraint vSalary_Name[Kassidy] < vSalary_Name[Heather];

% 6) The owner of the blue house earns more than Kassidy.
constraint vSalary_House[Blue] > vSalary_Name[Kassidy];

% 7) The patient who was prescribed ramipril is not Annabelle.
constraint Name_Prescribed[Ramipril] != Annabelle;

% 8) The owner of the lime house was prescribed enalapril for their heart condition.
% literal: Prescribed_Name[Name_House[Lime]] = Enalapril;
constraint Prescribed_House[Lime] = Enalapril;

% 9) The employee with the $144,000 salary was prescribed benazepril for their heart condition.
% literal: Prescribed_Name[Name_Salary[i144000]] = Benazepril;
% XXX NEED different matrix view here!!
constraint Prescribed_Salary[i144000] = Benazepril;




% 1) The blue jacket was not bought by Benny.
constraint Prescribed_House[Jacket] = Blue /\
           % Name_House[Jacket] = Name_Prescribed[Blue]
           Name_House[Jacket] != Benny /\ Name_Prescribed[Blue] != Benny;

% 2) Daniella was pleased to have $9.00 knocked off the House she bought.
constraint Name_Salary[i90] = Daniella;

% 3) The red House had more knocked off than the umbrella.
constraint vSalary_Prescribed[Red] > vSalary_House[Umbrella];

% 4) The trousers did not have $5.00 knocked off and were not bought by Benny or Carla.
constraint vSalary_House[Trousers] != 50 /\
           Name_House[Trousers] != Benny /\ Name_House[Trousers] != Carla;

solve satisfy;

