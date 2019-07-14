:- module(problemHolyGrail, [problem/2]).

problem(tias, problem(4, 4, [
        % "The 4 people were Tatum, the patient who was prescribed enalapril, the employee with the $54,000 salary, and the owner of the purple house",
% CHANGED TO: ( "with the salary")
        "The 4 people were tatum, the patient who was prescribed enalapril, the employee who earns 54000, and the owner of the purple house",
        "The patient who was prescribed enalapril is not heather",
        "The patient who was prescribed ramipril is not annabelle",
        "kassidy earns less than heather",
        "The owner of the blue house earns more than kassidy",
%%    "Of tatum and annabelle, one earns 144000 per year and the other lives in the cyan colored house",
%% CHANGED TO: (drop: colored)
        "Of tatum and annabelle, one earns 144000 per year and the other lives in the cyan house",
%%        "Either the employee with the 144000 salary or the employee with the 158000 salary lives in the blue colored house",
%% CHANGED TO: (drop colored, change the ...salara) 
        "Either the employee who earns 144000  or the employee who earns 158000 lives in the blue house",
        "The owner of the lime house was prescribed enalapril for their heart condition",
%%        "The employee with the 144000 salary was prescribed benazepril for their heart condition"
%% CHANGED TO:
        "The employee who earns 144000 was prescribed benazepril for their heart condition"
                     ], [
                        noun([patient], [patients]),
                        noun([person], [people]),
                        noun([year], [years]),
                        noun([employee], [employees]),
                        noun([salary], [salaries]),
                        noun([owner], [owners]),
                        pn([tatum]),
                        pn([annabelle]),
                        pn([heather]),
                        pn([kassidy]),
                        pn([benazepril]),
                        pn([enalapril]),
                        pn([ramipril]),
                        pn([fosinopril]),
                        prep([of]),
                        ppn([the, blue, house]),
                        ppn([the, lime, house]),
                        ppn([the, cyan, house]),
                        ppn([the, purple, house]),
                        tv([owns], [own]),
                        tvGap([earns], [per, year], [earn]),
                        tvGap([was, prescribed], [for, their, heart, condition], [prescribe]),
                        tvPrep([lives], [in], [live], [lived])
                     ])).

problem(p2_types, problem(4,5, [
                        "Of the contestant who scored 41 points and the person who threw the white darts, one was from Worthington and the other was Ira",
                        "Bill was from Mount union",
                        "Ira scored 21 points higher than the contestant from Worthington",
                        "Oscar scored somewhat higher than the player who threw the orange darts",
                        "The contestant from Mount union threw the black darts",
                        "Pedro didn't finish with 55 points",
                        "The player who threw the red darts was either Colin or the contestant who scored 48 points",
                        "Of the contestant who scored 41 points and the person who threw the orange darts, one was from Gillbertville and the other was from Worthington",
                        "Ira scored 7 points lower than the player from Lohrville"
        ], [
                        noun([contestant], [contestants]),
                        noun([person], [persons]),
                        noun([player], [players]),
                        noun([point], [points]),
                        pn([bill], A),
                        pn([colin], A),
                        pn([ira], A),
                        pn([oscar], A),
                        pn([pedro], A),
                        pn([mount, union], B),
                        pn([gillbertville], B),
                        pn([lohrville], B),
                        pn([worthington], B),
                        pn([yorktown], B),
                        ppn([the, black, darts], C),
                        ppn([the, orange, darts], C),
                        ppn([the, red, darts], C),
                        ppn([the, white, darts], C),
                        ppn([the, yellow, darts], C),
                        tv([threw], [throw]),
                        tv([scored], [score]),
                        tvPrep([finishes], [with], [finish], [finished]),
                        prep([from])
        ])).
