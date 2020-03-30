:- module(problemPosterEvaluation, [problem/2]).

%% % ADAPTED!!!
%% % ~~~~CLUE 1: added a [that]
%% % CLUE 3: active form
%% % ~~~~CLUE 5: added a [that]
%% % CLUE 9: in the health-care sector -> the health-care stock
%% % PROBLEM: Sector and name both refer to the same stock => flat types doesn't work
%% % => sold for for name->price vs being expensive for sector->price

%% % purchase(person, sector)
%% % buy(person, name)
%% % stock = sector
%% % position = name
%% % being_expensive(sector, price)
%% % sold_for(name, price)
%% % named(sector, name)
%% problem(p11, problem(4, 5, [
%%                          "The utilities stock was $1 per share less expensive than the stock Geraldo purchased",
%%                          "GXTV sold for $2 per share less than QMZ",
%%                          %% "The financial stock wasn't purchased by Edith",
%%                          "Edith didn't purchase the financial stock",
%%                          "PSTO sold for $29 per share",
%%                          "The position Abigail bought was either KMPP or JMO",
%%                          "The health-care stock was $2 per share more expensive than the financial stock",
%%                          "The energy stock was less expensive than the JMO stock",
%%                          "Heathcliff purchased the real estate stock",
%%                          %% "Of QMZ and GXTV, one sold for $26 per share and the other was in the health-care sector",
%%                          "Of QMZ and GXTV, one sold for $26 per share and the other was the health-care stock position",
%%                          "Abigail didn't purchase the stock that was $25 per share worth"
%%                      ], [
%%                          noun([per, share], [per, shares]),
%%                          noun([stock], [stocks]),
%%                          noun([position], [positions]),
%%                          pn([utilities, stock]),
%%                          pn([geraldo]),
%%                          pn([gxtv]),
%%                          pn([qmz]),
%%                          pn([financial, stock]),
%%                          pn([psto]),
%%                          pn([abigail]),
%%                          pn([kmpp]),
%%                          pn([jmo]),
%%                          pn([healthcare, stock]),
%%                          pn([energy, stock]),
%%                          pn([heathcliff]),
%%                          pn([real, estate, stock]),
%%                          pn([edith]),
%%                          tv([bought], [buy]),
%%                          tv([purchased], [purchase]),
%%                          tvPrep([sold], [for], [sell], [sold]),
%%                          %% tvPrep([purchased], [by], [purchase], [purchased]),
%%                          copGap([], [worth]),
%%                          prep([with, the, name]),
%%                          comp(lower, [less, expensive, than]),
%%                          comp(higher, [more, expensive, than])
%%                      ])).

problem(p11, problem(4, 5, [
                         "The utilities stock was $1 per share less expensive than the stock Geraldo bought",
                         "GXTV was $2 per share less expensive than QMZ",
                         %% "The financial stock wasn't purchased by Edith",
                         "Edith didn't purchase the financial stock",
                         "PSTO sold for $29 per share",
                         "The stock Abigail bought was either KMPP or JMO",
                         "The health-care stock was $2 per share more expensive than the financial stock",
                         "The energy stock was less expensive than JMO",
                         "Heathcliff purchased the real estate stock",
                         "Of QMZ and GXTV, one sold for $26 per share and the other was in the health-care sector",
                         "Abigail didn't purchase the stock that sold for $25 per share"
                     ], [
                         noun([per, share], [per, shares]),
                         noun([stock], [stocks]),
                         noun([sector], [sectors]),
                         pn([utilities]),
                         pn([geraldo]),
                         pn([gxtv]),
                         pn([qmz]),
                         pn([financial]),
                         pn([psto]),
                         pn([abigail]),
                         pn([kmpp]),
                         pn([jmo]),
                         pn([healthcare]),
                         pn([energy]),
                         pn([heathcliff]),
                         pn([real, estate]),
                         pn([edith]),
                         tv([bought], [buy]),
                         tv([purchased], [purchase]),
                         tvPrep([sold], [for], [sell], [sold]),
                         copGap([], [worth]),
                         prep([with, the, name]),
                         comp(lower, [less, expensive, than]),
                         comp(higher, [more, expensive, than]),
                         prep([in])
                     ])).


% ADAPTED
% integer prices
% clue 3: whoever -> the person who
% clue 3: had -> ordered (had is for drinking)
% clue 7: the one -> the person
problem(p12, problem(4, 5, [
                         "The order with the lemonade cost $1 more than the order with the water",
                         "Homer paid $7",
                         "Glen paid $3 less than whoever ordered the sloppy joe",
                         "Wallace didn't have the iced tea",
                         "Of the diner who paid $6 and Homer, one ordered the spaghetti and the other drank the water",
                         "Oliver ordered the hamburger",
                         "The five diners were whoever ordered the turkey plate, Oliver, Glen, the person who got the iced tea and the person who paid $5",
                         "Glen didn't have the orange soda"
                     ], [
                         noun([order], [orders]),
                         noun([person], [people]),
                         noun([diner], [diners]),
                         pn([lemonade]),
                         pn([water]),
                         pn([homer]),
                         pn([glen]),
                         pn([wallace]),
                         pn([oliver]),
                         pn([sloppy, joe]),
                         pn([iced, tea]),
                         pn([spaghetti]),
                         pn([hamburger]),
                         pn([turkey, plate]),
                         pn([orange, soda]),
                         tv([cost], [cost]),
                         tv([paid], [pay]),
                         tv([had], [have]),
                         tv([ordered], [order]),
                         tv([drank], [drink]),
                         tv([got], [get]),
                         prep([with])
                     ])).

% ADAPTED
% clue 6: lucas's puppet -> the puppet from Lucas
% clue 7: nicole's puppet -> the puppet from Nicole
% clue 8: isabel's -> from isabel
% clue 9: the one -> the puppet
% clue 10: of the $1000 and $1250 dummies -> of the $1000 dummy and the $1250 dummy
% clue 10: herman's -> from herman
problem(p13, problem(4, 5, [
                         "Kelly's piece didn't cost $1250",
                         "Valencia cost somewhat more than Isabel's dummy",
                         "The puppet going to Vancouver, the $750 dummy and the $1500 piece are three different dummies",
                         "Waldarama didn't cost $750 or $1500",
                         "Kelly's puppet isn't going to Ypsilanti",
                         "The dummy going to Mexico City is either Tombawomba or Lucas's puppet",
                         "Nicole's puppet, the $1000 piece and the puppet going to Ypsilanti are three different dummies",
                         "Of the $750 puppet and the piece going to Mexico City, one is Tombawomba and the other is Isabel's puppet",
                         "The puppet going to Ypsilanti cost $250 more than the puppet going to St. Moritz.",
                         "Of the $1000 dummy and the $1250 dummy, one is from Herman and the other is going to Mexico City",
                         "Sniffletoe sold for $1000"
                     ], [
                         noun([piece], [pieces]),
                         noun([dummy], [dummies]),
                         noun([puppet], [puppets]),
                         pn([kelly]),
                         pn([valencia]),
                         pn([isabel]),
                         pn([vancouver]),
                         pn([waldarama]),
                         pn([ypsilanti]),
                         pn([tombawomba]),
                         pn([lucas]),
                         pn([mexico, city]),
                         pn([nicole]),
                         pn([st, moritz]),
                         pn([herman]),
                         pn([sniffletoe]),
                         tv([cost], [cost]),
                         %% copGap([going, to], []),
                         tvPrep([go], [to], [go], [going]),
                         tvPrep([sold], [for], [sell], [sold]),
                         prep([from])
                     ])).

% 1 + 3) the one -> the shell
% 11) monk's fin -> monk's fin shell
% use "is in" because "is" doesn't work
% use "discovered in" instead of "found in" for places (only 1 type per verb)
problem(p14, problem(4, 5, [
                         "The baby's ear shell was found 3 years before the shell from Jamaica",
                         "The seashell discovered in Puerto Rico isn't in black and white",
                         "The shell found in 1992 isn't in blue and white",
                         "The blue and white shell, the shark eye shell and the shell discovered in Barbuda are three different specimens",
                         "The piece discovered in Saint Lucia was found 6 years after the honey cerith shell",
                         "Of the baby's ear shell and the black and white shell, one was found in 2004 and the other was discovered in Saint Lucia",
                         "The monk's fin shell isn't in black and white",
                         "The seashell found in 2001 is in brown and yellow",
                         "The shell found in 1995 is in pink and yellow",
                         "The baby's ear shell was found 3 years after the shell discovered in Aruba",
                         "The shell found in 2001 is either the monk's fin shell or the coquina"
                     ], [
                         noun([shell], [shells]),
                         noun([seashell], [seashells]),
                         noun([specimen], [specimens]),
                         noun([year], [years]),
                         noun([piece], [pieces]),
                         pn([baby, s, ear, shell]),
                         pn([jamaica]),
                         pn([seashell]),
                         pn([puerto, rico]),
                         pn([black, and, white]),
                         pn([blue, and, white]),
                         pn([shark, eye, shell]),
                         pn([barbuda]),
                         pn([saint, lucia]),
                         pn([honey, cerith, shell]),
                         pn([monk, s, fin, shell]),
                         pn([brown, and, yellow]),
                         pn([pink, and, yellow]),
                         pn([coquina]),
                         pn([aruba]),
                         tvPrep([found], [in], [find], [found]),
                         tvPrep([discovered], [in], [discover], [discovered]),
                         prep([in]),
                         prep([from])
                     ])).

% whoever -> the person who
% clue 6: drop the also
% clue 10: of the two presentation -> of the presentation on ... and the presentation on ...
% clue 11,12: the one -> the presentation
% clue 13: the lowest grade -> D
%% % clue 11: got -> received (only 1 meaning per verb)

% PROBLEM: intermediate type "presentation" can not be represented
problem(p15, problem(4, 5, [
                         "The student who got the B-minus talked about Augustus",
                         "Johnnie, the student who gave the presentation on Augustus and whoever got the B-plus were three different students",
                         "Gina didn't get the B-plus",
                         "The student who spoke for 10 minutes didn't get the C-Minus",
                         "Gina didn't talk about Galerius",
                         "Yolanda didn't give a presentation on Galerius",
                         "Yolanda, the student who gave the presentation on Caligula and the student who got the B-minus were three different children",
                         "Gina didn't get the A",
                         "The student who spoke for 8 minutes talked about Galerius",
                         %% "Of the presentation on Augustus and the presentation on Caligula, one was given by Catherine and the other lasted for 10 minutes",
                         %% "The presentation that received the A was 4 minutes shorter than the presentation on Caligula",
                         %% "The B-minus presentation was 6 minutes longer than the presentation that got the D",
                         %% "The talk on Nero was 2 minutes shorter than the presentation that got the D"
                         "Of the person that talked about Augustus and the student that talked about Caligula, one was Catherine and the other spoke for 10 minutes",
                         "The child that got the A spoke for 4 minutes shorter than the student on Caligula",
                         "The B-minus student spoke 6 minutes more than the student that got the D",
                         "The student on Nero spoke 2 minutes less than the child that got the D"
                     ], [
                         noun([student], [students]),
                         noun([person], [persons]),
                         noun([minute], [minutes]),
                         noun([child], [children]),
                         pn([augustus]),
                         pn([caligula]),
                         pn([galerius]),
                         pn([nero]),
                         pn([johnnie]),
                         pn([gina]),
                         pn([yolanda]),
                         pn([catherine]),
                         pn([a]),
                         pn([bplus]),
                         pn([bminus]),
                         pn([cminus]),
                         pn([d]),
                         tv([got], [get]),
                         tvPrep([talked], [about], [talk], [talked]),
                         tvPrep([spoke], [for], [speak], [spoken]),
                         tvPrep([given], [by], [give], [given]),
                         tvPrep([lasted], [for], [last], [lasted]),
                         copGap([], [long]),
                         comp(lower, [shorter, than]),
                         comp(higher, [longer, than]),
                         %% noun([presentation], [presentations]),
                         %% noun([talk], [talks]),
                         %% tv([gave], [give]),
                         %% tv([received], [receive]),
                         %% prep([on])
                         tvPrep([gave, the, presentation], [on], [give, the, presentation], [given, the, presentation]),
                         tvPrep([gave, a, presentation], [on], [give, a, presentation], [given, a, presentation]),
                         prep([on])
                     ])).


% whoever -> the person who
% clue 6: drop the also
% clue 10: of the two presentation -> of the presentation on ... and the presentation on ...
% clue 11,12: the one -> the presentation
% clue 13: the lowest grade -> D
% clue 11,12,13: got -> received (only 1 meaning per verb)

% got(student, grade)
% talked_about(student, topic)
% on(presentation, topic)
% gave(student, presentation)
% spoke_for(student, minutes)
% given_by(presentation, student)
% lasted_for(presentation minutes)
% received(presentation, grade)
% was_long(presentation, minutes)
problem(p15b, problem(4, 5, [
                         "The student who got the B-minus talked about Augustus",
                         "Johnnie, the student who gave the presentation on Augustus and whoever got the B-plus were three different students",
                         "Gina didn't get the B-plus",
                         "The student who spoke for 10 minutes didn't get the C-Minus",
                         "Gina didn't talk about Galerius",
                         "Yolanda didn't give a presentation on Galerius",
                         "Yolanda, the student who gave the presentation on Caligula and the student who got the B-minus were three different children",
                         "Gina didn't get the A",
                         "The student who spoke for 8 minutes talked about Galerius",
                         "Of the presentation on Augustus and the presentation on Caligula, one was given by Catherine and the other lasted for 10 minutes",
                         "The presentation that received the A was 4 minutes shorter than the presentation on Caligula",
                         "The B-minus presentation was 6 minutes longer than the presentation that received the D",
                         "The talk on Nero was 2 minutes shorter than the presentation that received the D"
                     ], [
                         noun([student], [students]),
                         noun([person], [persons]),
                         noun([minute], [minutes]),
                         noun([child], [children]),
                         pn([augustus]),
                         pn([caligula]),
                         pn([galerius]),
                         pn([nero]),
                         pn([johnnie]),
                         pn([gina]),
                         pn([yolanda]),
                         pn([catherine]),
                         pn([a]),
                         pn([bplus]),
                         pn([bminus]),
                         pn([cminus]),
                         pn([d]),
                         tv([got], [get]),
                         tvPrep([talked], [about], [talk], [talked]),
                         tvPrep([spoke], [for], [speak], [spoken]),
                         tvPrep([given], [by], [give], [given]),
                         tvPrep([lasted], [for], [last], [lasted]),
                         copGap([], [long]),
                         comp(lower, [shorter, than]),
                         comp(higher, [longer, than]),
                         noun([presentation], [presentations]),
                         noun([talk], [talks]),
                         tv([gave], [give]),
                         tv([received], [receive]),
                         prep([on])
                         %% tvPrep([gave, the, presentation], [on], [give, the, presentation], [given, the, presentation]),
                         %% tvPrep([gave, a, presentation], [on], [give, a, presentation], [given, a, presentation]),
                         %% prep([on])
                     ])).

% 1, 7) the one -> juggler
% 10) dropped "always"
problem(p16, problem(4, 5, [
                         "The juggler who went fourth was either the performer from Quasqueton or the juggler who used rings",
                         "The juggler who used flashlights performed one spot after the person who used mobile phones",
                         "The performer from Kingsburg performed one spot before Howard",
                         "Otis wasn't from Carbon",
                         "Of the performer who went second and the juggler who used rings, one was from Carbon and the other is Howard",
                         "The performer who went third, Gerald and the person from Kingsburg are three different people",
                         "Floyd was either the juggler who went second or the juggler from Quasqueton",
                         "The person who went third used rings",
                         "The juggler who went second wasn't from Nice",
                         "Floyd juggles rubber balls"
                     ], [
                         noun([juggler], [jugglers]),
                         noun([performer], [performers]),
                         noun([person], [people]),
                         noun([spot], [spots]),
                         pn([quasqueton]),
                         pn([rings]),
                         pn([flashlights]),
                         pn([mobile, phones]),
                         pn([kingsburg]),
                         pn([howard]),
                         pn([otis]),
                         pn([carbon]),
                         pn([gerald]),
                         pn([nice]),
                         pn([floyd]),
                         pn([rubber, balls]),
                         pnn([second], 2),
                         pnn([third], 3),
                         pnn([fourth], 4),
                         tv([went], [go]),
                         tv([used], [use]),
                         tv([performed], [perform]),
                         tv([juggles], [juggle]),
                         prep([from])
                     ])).

% 2, 9) the one -> the outing
% 5, 7) add "trip" to ...'s
% 9) starting at -> beginning at (type)

% begin is for time, start for place
% add 10 to group sizes: they overlap!!!
% Add extra type!!!
problem(p17, problem(4, 5, [
                         "The 11 am tour won't start at high park",
                         "Zachary's outing will begin 1 hour before the outing starting at Casa Loma",
                         "The tour with 7 people will begin 3 hours before the group of 6",
                         "The tour with 2 people will start at Yorkville",
                         "Zachary's trip will begin 3 hours before Janice's trip",
                         "Zachary's outing will begin 2 hours before the tour starting at Yorkville",
                         "Of the 7 am tour and Oscar's tour, one will start at Yorkville and the other will start at City Hall",
                         "The outing from Whitney isn't with 5 people",
                         "The Yorkville tour, the tour beginning at 9 am and the outing with 5 people are three different tours"
                     ], [
                         noun([am], [ams]),
                         noun([tour], [tours]),
                         noun([outing], [outings]),
                         noun([person], [people]),
                         noun([hour], [hours]),
                         noun([group], [groups]),
                         noun([trip], [trips]),
                         pn([high, park]),
                         pn([casa, loma]),
                         pn([zachary]),
                         pn([yorkville]),
                         pn([janice]),
                         pn([oscar]),
                         pn([city, hall]),
                         pn([whitney]),
                         tvPrep([start], [at], [start], [starting]),
                         tvPrep([begin], [at], [begin], [beginning]),
                         prep([with]),
                         prep([from]),
                         prep([of])
                     ])).

% clue 2: ahead of the academic -> the person who is the academic
% clue 6: an unknown number of votes -> somewhat
% clue 10: one ended up with X and the other [ended up] with Y
% received(profession, votes) <-> finished_with(name, votes)
% Name or profession used for same type
problem(p18, problem(4, 5, [
                         "Al allen is from glendale",
                         "Kelly Kirby finished 1000 votes ahead of the person who acts as the academic",
                         "The academic received 500 votes less than the teacher",
                         "The candidate who received 10500 votes isn't the writer",
                         "Kelly Kirby isn't from Olema",
                         "The glendale native finished somewhat ahead of the Olema native",
                         "Bev Baird ended up with 8500 votes",
                         "Ed Ewing finished 500 votes ahead of the Evansdale native",
                         "The man who received 9500 votes isn't the doctor",
                         "Of the person acting as academic and Al Allen, one ended up with 10000 votes and the other ended up with 8500 votes",
                         "The politician who finished with 10500 votes isn't from Lakota",
                         "The person acting as doctor was either the politician who finished with 10000 votes or Kelly Kirby"

                     ], [
                         noun([vote], [votes]),
                         noun([person], [people]),
                         noun([native], [natives]),
                         noun([politician], [politicians]),
                         noun([candidate], [candidates]),
                         noun([man], [men]),
                         pn([al, allen]),
                         pn([kelly, kirby]),
                         pn([bev, baird]),
                         pn([ed, ewing]),
                         pn([academic]),
                         pn([doctor]),
                         pn([writer]),
                         pn([teacher]),
                         pn([glendale]),
                         pn([olema]),
                         pn([evansdale]),
                         pn([lakota]),
                         tvPrep([finished], [with], [finish], [finished]),
                         tvPrep([ended, up], [with], [end, up], [ended, up]),
                         tvPrep([acts], [as], [act], [acting]),
                         tv([received], [receive]),
                         comp(higher, [ahead, of]),
                         comp(lower, [behind]),
                         prep([from])
                     ])).

% discovered_in vs discovered_by
% 1, 2, 4, 6, 9, 11) comet Whitaker discovered -> comet discovered by Whitaker
% Whitaker discovered his comet in 2010 -> The comet discovered by Whitaker was found in 2010
% 3, 4, 6) the one -> the comet
% 9) Whitaker's [comet]
% year: orbital vs time -> time replace "year" with "cycle"
problem(p19, problem(4, 5, [
                         "The comet discovered by Whitaker doesn't have an orbital period of 30 years",
                         "Gostroma was discovered 1 cycle after the comet discovered by Tillman",
                         "Of the comet discovered by Underwood and the comet with an orbital period of 42 years, one was found in 2009 and the other is Trosny",
                         "The comet with an orbital period of 21 years is either the comet discovered by Whitaker or Casputi",
                         "The comet discovered in 2010 doesn't have an orbital period of 21 years",
                         "The comet discovered by Tillman, the comet discovered in 2011 and Casputi are three different comets",
                         "Sporrin wasn't found in 2010",
                         %% "Whitaker discovered his comet in 2010",
                         "Whitaker's comet was discovered in 2010",
                         "The comet discovered by Parks was discovered 1 cycle before Whitaker's comet",
                         "The comet discovered in 2011 doesn't have an orbital period of 47 years",
                         "The comet discovered by Underwood has an orbital period of either 47 or 58 years"
                     ], [
                         noun([comet], [comets]),
                         noun([year], [years]),
                         noun([cycle], [cycles]),
                         noun([orbital, period], [orbital, periods]),
                         pn([whitaker]),
                         pn([gostroma]),
                         pn([tillman]),
                         pn([trosny]),
                         pn([casputi]),
                         pn([sporrin]),
                         pn([parks]),
                         pn([underwood]),
                         %% tv([discovered], [discover]),
                         tv([has], [have]),
                         tvPrep([discovered], [by], [discover], [discovered]),
                         %% tvPrep([has, an, orbital, period], [of], [have, an, orbital, period], [having, an, orbital, period]),
                         tvPrep([discovered], [in], [discover], [discovered]),
                         tvPrep([found], [in], [find], [found]),
                         prep([with]),
                         prep([of])
                         %% prep([with, an, orbital, period, of])
                     ])).


% 3) the one -> the building
% 5, 9) dropped: was [said to be] haunted by
% 7, 10, 11) dropped: house [priscilla] visited in ...
problem(p20, problem(4, 5, [
                         "Hughenden wasn't investigated in march",
                         "The home on Circle Drive was investigated sometime before Wolfenden",
                         "Of the building haunted by Lady Grey and the building haunted by Victor, one was Markmanor and the other was visited in January",
                         "The house haunted by Victor was visited 1 month after the house haunted by Lady Grey",
                         "Of the home on Bird Road and Barnhill, one was visited in January and the other was haunted by Brunhilde",
                         "Markmanor was visited 1 month after the home on Grant Place",
                         "The house visited in march wasn't located on Circle Drive",
                         "Hughenden wasn't haunted by Abigail",
                         "Wolfenden was haunted by Brunhilde",
                         "The building visited in May wasn't located on Fifth Avenue",
                         "The home visited in April was either Markmanor or the home haunted by Brunhilde"
                     ], [
                         noun([home], [homes]),
                         noun([building], [buildings]),
                         noun([house], [houses]),
                         noun([month], [months]),
                         pn([hughenden]),
                         pn([circle, drive]),
                         pn([wolfenden]),
                         pn([lady, grey]),
                         pn([victor]),
                         pn([markmanor]),
                         pn([bird, road]),
                         pn([barnhill]),
                         pn([brunhilde]),
                         pn([grant, place]),
                         pn([priscilla]),
                         pn([fifth, avenue]),
                         pn([abigail]),
                         pnn([march], 3),
                         pnn([january], 1),
                         pnn([may], 5),
                         pnn([april], 4),
                         tvPrep([investigated], [in], [investigate], [investigated]),
                         tvPrep([haunted], [by], [haunt], [haunted]),
                         tvPrep([visited], [in], [visit], [visited]),
                         tvPrep([located], [on], [locate], [located]),
                         prep([on])
                     ])).

% EXTRA, for fun
% "the one" -> the person
% dropped "exactly"
% "... fewer facebook friends than" -> "... facebook friends less than"
% use different verbs!!!
problem(p93, problem(4, 5, [
                         "Opal is connected to 64 LinkedIn connections",
                         "The person followed by 809 Twitter followers, the person with 140 facebook friends and the person connected to 78 linkedin connections are three different people",
                         "Of rosie and neil, one is connected to 68 linkedin connections and the other is followed by 789 twitter followers",
                         "The person connected to 57 linkedin connections has 10 facebook friends less than the person followed by 715 twitter followers",
                         "Arnold isn't followed by 589 twitter followers",
                         "The person followed by 809 twitter followers isn't connected to 68 linkedin connections",
                         "Of the person connected to 57 linkedin connections and arnold, one has 140 facebook friends and the other is followed by 789 twitter followers",
                         "opal doesn't have 150 facebook friends",
                         "the person connected to 57 linkedin connections has 10 facebook friends less than georgia",
                         "The person with 130 facebook friends is either arnold or the person followed by 715 twitter followers",
                         "the person followed by 789 twitter followers has somewhat less than rosie"
                     ], [
                         noun([linkedin, connection], [linkedin, connections]),
                         noun([twitter, follower], [twitter, followers]),
                         noun([facebook, friend], [facebook, friends]),
                         noun([person], [people]),
                         pn([opal]),
                         pn([rosie]),
                         pn([neil]),
                         pn([arnold]),
                         pn([georgia]),
                         tvPrep([connected], [to], [connect], [connected]),
                         tvPrep([followed], [by], [follow], [followed]),
                         tv([has], [have]),
                         prep([with])
                     ])).

problem(p25, problem(4, 5, [
                         "Of Flowcarts and the application with 5500000 downloads, one was made by Vortia and the other was released in May",
                         "The app released in July, the app developed by Apptastic and Vitalinks are three different games",
                         "Neither the game released by Gadingo nor the apptastic app has 2300000 downloads",
                         "The five apps are Bubble Boms, the app released in April, the app released in July, the application released by Apptastic and the app released by Digibits",
                         "Vortia's app came out in march",
                         "Angry Ants was released 2 months earlier than the app with 6800000 downloads",
                         "Flowcarts doesn't have 4200000 downloads",
                         "The game released in July is either the game with 6800000 downloads or the app released by Gadingo"
                     ], [
                         noun([application], [applications]),
                         noun([app], [apps]),
                         noun([download], [downloads]),
                         noun([game], [games]),
                         noun([month], [months]),
                         pn([flowcarts]),
                         pn([vortia]),
                         pn([apptastic]),
                         pn([vitalinks]),
                         pn([gadingo]),
                         pn([bubble, boms]),
                         pn([digibits]),
                         pn([angry, ants]),
                         pnn([may], 5),
                         pnn([july], 7),
                         pnn([april], 4),
                         pnn([march], 3),
                         tv([has], [have]),
                         tvPrep([made], [by], [make], [made]),
                         tvPrep([developed], [by], [develop], [developed]),
                         tvPrep([released], [in], [release], [released]),
                         tvPrep([released], [by], [release], [released]),
                         tvPrep([came, out], [in], [come, out], [came, out]),
                         prep([with]),
                         comp(lower, [earlier, than])
                     ])).
