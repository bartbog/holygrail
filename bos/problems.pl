:- module(problems, [problem/2]).

:- use_module(problemsPosterEvaluation, [problem/2 as problemPosterEvaluation]).

problem(X, Y) :-
    problemPosterEvaluation(X, Y).

problem(tias, problem(4, 4, [
        % "The 4 people were Tatum, the patient who was prescribed enalapril, the employee with the $54,000 salary, and the owner of the purple house",
% CHANGED TO: ( "with the salary")
        "The 4 people were tatum, the patient who was prescribed enalapril, the person who earns 54000, and the person who owns the purple house",
	"The patient who was prescribed enalapril is not heather",
	"The patient who was prescribed ramipril is not annabelle",
	"kassidy earns less than heather",
	"The owner of the blue house earns more than kassidy",
%%    "Of tatum and annabelle, one earns 144000 per year and the other lives in the cyan colored house",
%% CHANGED TO: (drop: colored)
    "Of tatum and annabelle, one earns 144000 per year and the other lives in the cyan house",
%%	"Either the employee with the 144000 salary or the employee with the 158000 salary lives in the blue colored house",
%% CHANGED TO: (drop colored, change the ...salara) 
	"Either the employee who earns 144000  or the employee who earns 158000 lives in the blue house",
	"The owner of the lime house was prescribed enalapril for their heart condition",
%%	"The employee with the 144000 salary was prescribed benazepril for their heart condition"
%% CHANGED TO:
	"The employee who earns 144000 was prescribed benazepril for their heart condition"
                     ], [
                        noun([patient], [patients]),
                        noun([person], [people]),
                        noun([year], [years]),
                        noun([employee], [employees]),
                        noun([salary], [salaries]),
                        noun([owner], [owners]),
                        noun([people], [people]),
                        pn([tatum]),
                        pn([annabelle]),
                        pn([heather]),
                        pn([kassidy]),
                        pn([benazepril]),
                        pn([enalapril]),
                        pn([ramipril]),
                        pn([fosinopril]),
                        prep([of]),
                        prep([who]),
                        ppn([the, blue, house]),
                        ppn([the, lime, house]),
                        ppn([the, cyan, house]),
                        ppn([the, purple, house]),
                        tv([owns], [own]),
                        tvGap([earns], [per, year], [earn]),
                        tvGap([was, prescribed], [for, their, heart, condition], [prescribe]),
                        tvPrep([lives], [in], [live], [lived])
                     ])).



problem(p1, problem(4,5, [
                        "The perens pig lives in Slovakia and was recognized as endangered in 2009",
                        "The eldar elk has a population size of 210",
                        "The byengo bat doesn't live in Ghana",
                        "The animal that lives in Slovakia was listed sometime before the animal from Russia",
                        "Of the species with a population size of 490 and the eldar elk, one lives in Poland and the other was recognized as endangered in 2009",
                        "Neither the nibner newt nor the byengo bat has a surviving population size of 525",
                        "The species that lives in Ghana was listed 2 years after the nibner newt",
                        "The animal that lives in Russia doesn't have a surviving population size of 315"
        ], [
                        noun([species], [species]),
                        noun([animal], [animals]),
                        noun([year], [years]),
                        pn([the, perens, pig]),
                        pn([the, byengo, bat]),
                        pn([the, nibner, newt]),
                        pn([the, eldar, elk]),
                        pn([the, osbele, oryx]),
                        pn([ghana]),
                        pn([honduras]),
                        pn([poland]),
                        pn([russia]),
                        pn([slovakia]),
                        tvPrep([lives], [in], [live], [lived]),
                        tvPrep([recognized, as, endangered], [in], [recognize, as, endangered], [recognized, as, endangered]),
                        tvPrep([listed], [in], [list], [listed]),
                        tvPrep([has, a, population, size], [of], [have, a, population, size], [had, a, population, size]),
                        tvPrep([has, a, surviving, population, size], [of], [have, a, surviving, population, size], [had, a, surviving, population, size]),
                        prep([from]),
                        prep([with, a, population, size, of])
        ])).
problem(p1b, problem(4,5, [
                        "The perens pig lives in Slovakia and was recognized as endangered in 2009",
                        "The eldar elk has a population size of 210",
                        "The byengo bat doesn't live in Ghana",
                        "The animal that lives in Slovakia was listed sometime before the animal from Russia",
                        "Of the species with a population size of 490 and the eldar elk, one lives in Poland and the other was recognized as endangered in 2009",
                        "Neither the nibner newt nor the byengo bat has a surviving population size of 525",
                        "The species that lives in Ghana was listed 2 years after the nibner newt",
                        "The animal that lives in Russia doesn't have a surviving population size of 315"
        ], [
                        noun([species], [species]),
                        noun([animal], [animals]),
                        noun([year], [years]),
                        noun([population, size], [population, sizes]),
                        noun([surviving, population, size], [surviving, population, sizes]),
                        pn([the, perens, pig]),
                        pn([the, byengo, bat]),
                        pn([the, nibner, newt]),
                        pn([the, eldar, elk]),
                        pn([the, osbele, oryx]),
                        pn([ghana]),
                        pn([honduras]),
                        pn([poland]),
                        pn([russia]),
                        pn([slovakia]),
                        tv([has], [have]),
                        tvPrep([lives], [in], [live], [lived]),
                        tvPrep([recognized, as, endangered], [in], [recognize, as, endangered], [recognized, as, endangered]),
                        tvPrep([listed], [in], [list], [listed]),
                        prep([from]),
                        prep([with]),
                        prep([of])
        ])).

problem(p2, problem(4,5, [
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
                        pn([bill]),
                        pn([colin]),
                        pn([ira]),
                        pn([oscar]),
                        pn([pedro]),
                        pn([mount, union]),
                        pn([gillbertville]),
                        pn([lohrville]),
                        pn([worthington]),
                        pn([yorktown]),
                        ppn([the, black, darts]),
                        ppn([the, orange, darts]),
                        ppn([the, red, darts]),
                        ppn([the, white, darts]),
                        ppn([the, yellow, darts]),
                        tv([threw], [throw]),
                        tv([scored], [score]),
                        tvPrep([finishes], [with], [finish], [finished]),
                        prep([from])
        ])).
problem(p2b, problem(4,5, [
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
                        noun([darts], [darts]),
                        pn([bill]),
                        pn([colin]),
                        pn([ira]),
                        pn([oscar]),
                        pn([pedro]),
                        pn([mount, union]),
                        pn([gillbertville]),
                        pn([lohrville]),
                        pn([worthington]),
                        pn([yorktown]),
                        ppn([black]),
                        ppn([orange]),
                        ppn([red]),
                        ppn([white]),
                        ppn([yellow]),
                        tv([threw], [throw]),
                        tv([scored], [score]),
                        tvPrep([finishes], [with], [finish], [finished]),
                        prep([from])
        ])).

problem(p3, problem(4, 5, [
                        "The team that finished with 739 points wore orange shirts",
                        "Of the squad in the blue shirts and the team from Stacyville, one had a final score of 715 points and the other was the Oddballs",
                        "Of the Turkey Rolls and the team from Lathrop, one wore orange shirts and the other wore red",
                        "The rowdy rollers finished 12 points below the team in orange shirts",
                        "The squad that finished with 727 points was either the team in the orange shirts or the squad from Woodstock",
                        "The Turkey Rolls weren't from Castro Valley",
                        "The Alley Cats had a final score of 763 points",
                        "The team in the blue shirts, the Splitters, the squad from Lathrop and the Rowdy Rollers were all different teams",
                        "The squad that finished with 715 points didn't wear lime green shirts"
                    ], [
                        noun([team], [teams]),
                        noun([point], [points]),
                        noun([squad], [squads]),
                        pn([orange, shirts]),
                        pn([blue, shirts]),
                        pn([stacyville]),
                        pn([lathrop]),
                        pn([red]),
                        pn([woodstock]),
                        pn([castro, valley]),
                        pn([lime, green, shirts]),
                        ppn([oddballs]),
                        ppn([turkey, rolls]),
                        ppn([rowdy, rollers]),
                        ppn([alley, cats]),
                        ppn([splitters]),
                        tv([wore], [wear]),
                        tvPrep([finished], [with], [finish], [finished]),
                        tvPrep([had, a, final, score], [of], [have, a, final, score, of], [had, a, final, score, of]),
                        prep([in]),
                        prep([from])
                    ])).

%ADAPTED
% dropped now from clue 7
% adapted clue 8 to be a real enumeration
% dropped "currently" from clue 10
problem(p4, problem(4, 5, [
                        "Michael isn't from Eldon",
                        "The 2008 graduate is either Jackie or Michael",
                        "The 2006 graduate is either Ivan or Orlando",
                        "The Dodgers player didn't graduate in 2007 or 2008",
                        "Jackie graduated 2 years before the player from York",
                        "The 2007 graduate isn't playing for the Giants",
                        "Of Lonnie and the person from Frenchboro, one is with the Dodgers and the other graduated in 2005",
                        %% "The five players are the person from Frenchboro, Ivan, and the three players currently with the Indians, Mariners and Giants",
                        "The five players are the person from Frenchboro, Ivan, the player with the Indians, the person with the Mariners and the graduate that plays for the Giants",
                        "The person who graduated in 2005 is from Unity",
                        "Lonnie plays for the Mariners"
                     ], [
                        noun([graduate], [graduates]),
                        noun([player], [players]),
                        noun([year], [years]),
                        noun([person], [persons]),
                        pn([michael]),
                        pn([eldon]),
                        pn([jackie]),
                        pn([ivan]),
                        pn([orlando]),
                        pn([dodgers]),
                        pn([york]),
                        pn([giants]),
                        pn([lonnie]),
                        pn([frenchboro]),
                        pn([indians]),
                        pn([mariners]),
                        pn([unity]),
                        tvPrep([graduated], [in], [graduate], [graduated]),
                        tvPrep([plays], [for], [play], [playing]),
                        prep([from]),
                        prep([with])
                     ])).

problem(p5, problem(4, 5, [
                        "Mattie is 113 years old",
                        "The person who lives in Tehama is a native of either Kansas or Oregon",
                        "The Washington native is 1 year older than Ernesto",
                        "Roxanne is 2 years younger than the Kansas native",
                        "The person who lives in Zearing isn't a native of Alaska",
                        "The person who is 111 years old doesn't live in Plymouth",
                        "The Oregon native is either Zachary or the person who lives in Tehama",
                        "The person who lives in Shaver Lake is 1 year younger than Roxanne",
                        "The centenarian who lives in Plymouth isn't a native of Alaska",
                        "Of the person who lives in Tehama and Mattie, one is a native of Alaska and the other is from Kansas"
                     ], [
                        noun([year], [years]),
                        noun([person], [persons]),
                        noun([native], [natives]),
                        noun([centenarian], [centenarians]),
                        pn([mattie]),
                        pn([tehama]),
                        pn([kansas]),
                        pn([oregon]),
                        pn([washington]),
                        pn([ernesto]),
                        pn([roxanne]),
                        pn([zearing]),
                        pn([alaska]),
                        pn([plymouth]),
                        pn([zachary]),
                        pn([shaver, lake]),
                        tvPrep([lives], [in], [live], [lived]),
                        copGap([], [old]),
                        prep([of]),
                        prep([from]),
                        comp(higher, [older, than]),
                        comp(lower, [younger, than])
                     ])).


% ADAPTED
% clue 4: of the two dogs who graduated in March and April -> of the dog who graduated in March and the dog who graduated in April, ...
problem(p6, problem(4, 5, [
                        "Officer Quinn's dog graduated in either March or April",
                        "Aries didn't graduate in March, May or June",
                        "The dog who graduated in March didn't go to Cole County",
                        "Of the dog who graduated in March and the dog who graduated in April, one went to Tanager County and the other was assigned to Officer Ingram",
                        "Aries wasn't assigned to Officer Ingram",
                        "Barca didn't go to Kermit County",
                        "The dog sent to Kermit County, the K-9 unit assigned to Officer Lyons and the canine who graduated in June are three different dogs",
                        "The dog assigned to Officer Salinas graduated 2 months after Aries",
                        "Of the dog sent to Sycamore County and Tinkerbell, one graduated in July and the other was assigned to Officer Underwood",
                        "Jaws graduated sometime after the dog sent to Tanager County",
                        "McGruff went to Sycamore County"
        ], [
                        pn([officer, quinn]),
                        pn([aries]),
                        pn([barca]),
                        pn([cole, county]),
                        pn([tanager, county]),
                        pn([officer, ingram]),
                        pn([kermit, county]),
                        pn([officer, salinas]),
                        pn([sycamore, county]),
                        pn([tinkerbell]),
                        pn([officer, underwood]),
                        pn([officer, lyons]),
                        pn([jaws]),
                        pn([mcgruff]),
                        noun([dog], [dogs]),
                        noun([k9, unit], [k9, units]),
                        noun([canine], [canines]),
                        noun([month], [months]),
                        tvPrep([graduated], [in], [graduate], [graduated]),
                        tvPrep([went], [to], [go], [went]),
                        tvPrep([assigned], [to], [assign], [assigned]),
                        tvPrep([sent], [to], [send], [sent]),
                        pnn([march], 3),
                        pnn([april], 4),
                        pnn([may], 5),
                        pnn([june], 6),
                        pnn([july], 7)
        ])).

% ADAPTED
% CLUE 1 and 2: May 18 -> in May
% CLUE 2: from Norway, from Canada -> The Norwegian, The Canadian
% CLUE 3, 8 and 9: ADD "birthday" to end of clue
problem(p7, problem(4, 5, [
                        "The Norwegian's birthday is in May",
                        %% "Of Bill and the traveler born in June, one is from Norway and the other is from Canada",
                        "Of Bill and the traveler born in June, one is the Norwegian and the other is the Canadian",
                        "Izzy's birthday is 1 month after the politician's birthday",
                        %% "The engineer is from France",
                        "The engineer is the frenchman",
                        "The South African's birthday is in either April or May",
                        "The musician's birthday isn't in April",
                        %% "Jeffrey is either French or South African",
                        "Jeffrey is either the Frenchman or the South African",
                        "The Canadian's birthday is 1 month after the surgeon's birthday",
                        "Harry's birthday is sometime before Bill's birthday"
        ], [
                        noun([birthday], [birthdays]),
                        noun([traveler], [travelers]),
                        noun([month], [months]),
                        pn([norwegian]),
                        pn([bill]),
                        pn([canadian]),
                        pn([izzy]),
                        pn([politician]),
                        pn([engineer]),
                        pn([frenchman]),
                        pn([musician]),
                        pn([jeffrey]),
                        pn([harry]),
                        pn([south, african]),
                        pn([surgeon]),
                        pnn([may], 5),
                        pnn([june], 6),
                        pnn([april], 4),
                        tvPrep([born], [in], [born], [born]),
                        prep([in])
        ])).

% ADAPTED almost completely
problem(p7b, problem(4, 5, [
                        "The traveler from Norway is born in May",
                        "Of Bill and the traveler born in June, one is from Norway and the other is from Canada",
                        "Izzy is born 1 month after the traveler acting as politician",
                        "The traveler acting as engineer is from France",
                        "The traveler from South Africa is born in either April or May",
                        "The musician's birthday isn't in April",
                        "Jeffrey is from either France or South Africa",
                        "The traveler from Canada is born 1 month after the traveler acting as surgeon",
                        "Harry is born sometime before Bill"
        ], [
                        noun([birthday], [birthdays]),
                        noun([traveler], [travelers]),
                        noun([month], [months]),
                        pn([norway]),
                        pn([bill]),
                        pn([canada]),
                        pn([izzy]),
                        pn([politician]),
                        pn([engineer]),
                        pn([france]),
                        pn([musician]),
                        pn([jeffrey]),
                        pn([harry]),
                        pn([south, africa]),
                        pn([surgeon]),
                        pnn([may], 5),
                        pnn([june], 6),
                        pnn([april], 4),
                        tvPrep([born], [in], [borned], [born]),
                        tvPrep([acts], [as], [act], [acting]),
                        prep([from]),
                        prep([in])
        ])).

% ADAPTED
% CLUE 4: orange -> in orange
% CLUE 5 and 7: 5 fewer minutes -> 5 minutes fewer, moved to print to the end
% CLUE 9: just 10 -> 10 minutes to print
problem(p8, problem(4, 5, [
                        "The flower printed in 25 minutes",
                        "Adrienne's design took 15 minutes to print",
                        "The piece that printed in 30 minutes wasn't the mask",
                        "Of the item that printed in 10 minutes and Bertha's piece, one was the flower and the other was in orange",
                        "The orange item required 5 minutes fewer than the yellow design to print",
                        "Adrienne's design was either the phone case or the item that printed in 30 minutes",
                        "The white item took 10 minutes more than Stella's piece",
                        "Raquel's piece wasn't the mask",
                        "Of the whistle and the blue piece, one took 30 minutes to print and the other took 10 to print"
        ], [
                        noun([minute], [minutes]),
                        noun([design], [designs]),
                        noun([piece], [pieces]),
                        noun([item], [items]),
                        pn([flower]),
                        pn([mask]),
                        pn([phone, case]),
                        pn([whistle]),
                        pn([adrienne]),
                        pn([bertha]),
                        pn([raquel]),
                        pn([stella]),
                        pn([orange]),
                        pn([yellow]),
                        pn([blue]),
                        pn([white]),
                        tvPrep([printed], [in], [print], [printed]),
                        tvGap([took], [to, print], [take]),
                        tvGap([required], [to, print], [require]),
                        prep([in]),
                        comp(lower, [fewer, than])
        ])).

% ADAPTED
% clue 2, 4, 5 and 6: 2 sentences each
% clue 9: youngest => 15 years old
problem(p9, problem(4, 5, [
                        "The client with the 10 am class isn't 17 or 21 years old",
                        "Opal isn't 20 years old and is scheduled 2 hours after Harold",
                        "Harold is being trained by Mr Terry and isn't 17 years old",
                        "Mr alford's client isn't 17 years old and is scheduled sometime before the trainee who is 15 year old and 2 hours after Harold",
                        "Mr french's trainee isn't 20 years old and is scheduled 1 hour after mr terry's client",
                        "Elmer is being trained by Mr underwood and is scheduled 2 hours after jerry",
                        %% "Elmer isn't the youngest student"
                        "Elmer isn't 15 years old"
        ], [
                        noun([client], [clients]),
                        noun([hour], [hours]),
                        noun([year], [years]),
                        noun([trainee], [trainees]),
                        noun([student], [students]),
                        noun([am], [ams]),
                        noun([class], [classes]),
                        pn([opal]),
                        pn([harold]),
                        pn([mr, terry]),
                        pn([mr, alford]),
                        pn([mr, french]),
                        pn([elmer]),
                        pn([mr, underwood]),
                        pn([jerry]),
                        tvPrep([scheduled], [at], [schedule], [scheduled]),
                        tvPrep([is, being, trained], [by], [be, trained], [trained]),
                        copGap([], [old]),
                        prep([with])
        ])).

% ADAPTED
% integer dollars
% order: only for pasta, not for sauce (-> clue 4: chose ipv order)
problem(p10, problem(4, 5, [
                         "Angie didn't order capellini",
                         "Whoever did order capellini paid $11",
                         "Damon's bill came to $8",
                         "Claudia, the person who paid $9 and whoever chose arrabiata sauce were three different people",
                         "Angie was either the runner who ordered rotini or the diner who paid $11",
                         "The competitor who chose marinara sauce paid $2 less than the runner who ordered tagliolini",
                         "Elisa paid $2 less than the person who chose puttanesca sauce",
                         "Of Claudia and whoever paid $7, one chose bolognese sauce and the other ordered tagliolini",
                         "Damon had either farfalle or rotini"
        ], [
                        noun([person], [people]),
                        noun([runner], [runners]),
                        noun([diner], [diners]),
                        noun([competitor], [competitors]),
                        noun([bill], [bills]),
                        pn([angie]),
                        pn([capellini]),
                        pn([damon]),
                        pn([claudia]),
                        pn([arrabiata, sauce]),
                        pn([rotini]),
                        pn([marinara, sauce]),
                        pn([tagliolini]),
                        pn([puttanesca, sauce]),
                        pn([bolognese, sauce]),
                        pn([farfalle]),
                        pn([elisa]),
                        tv([ordered], [order]),
                        tv([chose], [chose]),
                        tv([had], [have]),
                        tv([paid], [pay]),
                        tvPrep([came], [to], [come], [come])
        ])).
