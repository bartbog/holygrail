% By Tias, for Holy Grail Challenge
%
% A Bargain
% Submitted By: geecee
% Difficulty: easy
% http://logicgridpuzzles.com/puzzles/show_logic.php?ID=16
%
% Benny, Carla and Daniella each picked up a bargain in the January sales with all three items having a reasonable saving on the original selling price - the biggest being $11.50. 
% From this information and the following clues, for each buyer, can you determine the item they bought, the color and the amount saved on the original selling price?
%
%                |           Item           |     Color      |    Savings     |
%                | Trousers Jacket Umbrella | Red Green Blue | 5.0  9.0  11.5 |
% Name  Benny    |                          |                |                |
%       Carla    |                          |                |                |
%       Daniella |__________________________|________________|________________|
% Savings  5.0   |                          |                |
%          9.0   |                          |                |
%          11.5  |__________________________|________________|
% Color  Red     |                          |
%        Green   |                          |
%        Blue    |__________________________|
%
% 1) The blue jacket was not bought by Benny.
% 2) Daniella was pleased to have $9.00 knocked off the item she bought.
% 3) The red item had more knocked off than the umbrella.
% 4) The trousers did not have $5.00 knocked off and were not bought by Benny or Carla.

include "globals.mzn";

% options
enum Name = {Benny, Carla, Daniella};
enum Item = {Trousers, Jacket, Umbrella};
enum Color = {Red, Green, Blue};
%set of float: Savings = {5.0, 9.0, 11.5};
enum Savings = {i50, i90, i115}; % integer strings, x10 multiplier
array[Savings] of int: vSavings = [50, 90, 115];

% matrix variables
% Q: should we build the full matrix, so also the reverse indexed?, now for values, depends on having right order...
array[Item] of var Name: Name_Item;
array[Color] of var Name: Name_Color;
array[Savings] of var Name: Name_Savings;
array[Item] of var dom_array(vSavings): vSavings_Item;
array[Color] of var dom_array(vSavings): vSavings_Color;
array[Item] of var Color: Color_Item;

% uniqueness constraints
constraint all_different(Name_Item) /\ all_different(Name_Color) /\ all_different(Name_Savings);
constraint all_different(vSavings_Item) /\ all_different(vSavings_Color);
constraint all_different(Color_Item);

% connection constraints
constraint forall (i in Item, c in Color) (
                Name_Item[i] = Name_Color[c] <-> Color_Item[i] = c );
constraint forall (i in Item, s in Savings) (
                Name_Item[i] = Name_Savings[s] <-> vSavings_Item[i] = vSavings[s] );
constraint forall (c in Color, s in Savings) (
                Name_Color[c] = Name_Savings[s] <-> vSavings_Color[c] = vSavings[s] );


% Clue constraints
% 1) The blue jacket was not bought by Benny.
constraint Color_Item[Jacket] = Blue /\
           % Name_Item[Jacket] = Name_Color[Blue]
           Name_Item[Jacket] != Benny /\ Name_Color[Blue] != Benny;

% 2) Daniella was pleased to have $9.00 knocked off the item she bought.
constraint Name_Savings[i90] = Daniella;

% 3) The red item had more knocked off than the umbrella.
constraint vSavings_Color[Red] > vSavings_Item[Umbrella];

% 4) The trousers did not have $5.00 knocked off and were not bought by Benny or Carla.
constraint vSavings_Item[Trousers] != 50 /\
           Name_Item[Trousers] != Benny /\ Name_Item[Trousers] != Carla;

solve satisfy;

