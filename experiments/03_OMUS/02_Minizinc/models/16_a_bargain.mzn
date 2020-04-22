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

% Values
enum Name = {Benny, Carla, Daniella};
enum Item = {Trousers, Jacket, Umbrella};
enum Color = {Red, Green, Blue};
%set of float: Savings = {5.0, 9.0, 11.5};
enum Savings = {i50, i90, i115}; % integer strings, x10 multiplier
array[Savings] of int: vSavings = [50, 90, 115];

% Matrix variables, all views
% Name:
array[Item] of var Name: Name_Item;
array[Color] of var Name: Name_Color;
array[Savings] of var Name: Name_Savings;
% Item:
array[Name] of var Item: Item_Name;
array[Color] of var Item: Item_Color;
array[Savings] of var Item: Item_Savings;
% vSavings:
array[Name] of var dom_array(vSavings): vSavings_Name;
array[Item] of var dom_array(vSavings): vSavings_Item;
array[Color] of var dom_array(vSavings): vSavings_Color;
% Color:
array[Name] of var Color: Color_Name;
array[Item] of var Color: Color_Item;
array[Savings] of var Color: Color_Savings;

% Symmetry connection constraints, upper triangle
constraint forall (s in Savings) ( vSavings_Name[Name_Savings[s]] = vSavings[s] );
constraint forall (s in Savings) ( vSavings_Item[Item_Savings[s]] = vSavings[s] );
constraint forall (s in Savings) ( vSavings_Color[Color_Savings[s]] = vSavings[s] );
constraint forall (n in Name) ( Name_Item[Item_Name[n]] = n );
constraint forall (n in Name) ( Name_Color[Color_Name[n]] = n );
constraint forall (i in Item) ( Item_Color[Color_Item[i]] = i );

% Transitive connection constraints, upper triangle
% Name: Savings + Item, Savings + Color, Item + Color
constraint forall (s in Savings) ( Name_Savings[s] = Name_Item[Item_Savings[s]] );
constraint forall (s in Savings) ( Name_Savings[s] = Name_Color[Color_Savings[s]] );
constraint forall (h in Item) ( Name_Item[h] = Name_Color[Color_Item[h]] );
% Color: Savings + Item, (Savings + Color, Item + Color)
constraint forall (s in Savings) ( Color_Savings[s] = Color_Item[Item_Savings[s]] );
% (Item: Savings + Color)


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

