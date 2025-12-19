

%dishwashing_setup
:- dynamic holding/2.
:- dynamic numHolding/2.
:- dynamic faucetOn/1.
:- dynamic loc/3.
:- dynamic wet/2.
:- dynamic dirty/2.
:- dynamic soapy/2.
:- dynamic plate/1.
:- dynamic glassware/1.

:- [planner].

% inital states
%:- [dishwashingInit1].
%:- [dishwashingInit2].
:- [dishwashingInit3].


%% Goal states for dishwashingInit1
goal_state(11, S) :-
    holding(brush, S),
    soapy(brush, S).

goal_state(12, S) :-
    loc(brush, dish_rack, S),
    loc(sponge, counter, S).

goal_state(13, S) :-
    not(dirty(g1, S)),
    not(soapy(g1, S)).

goal_state(14, S) :-
    not(dirty(g1, S)),
    not(soapy(g1, S)),
    loc(g1, dish_rack, S),
    not(faucetOn(S)).

goal_state(15, S) :-
    not(dirty(g1, S)),
    not(soapy(g1, S)),
    loc(g1, dish_rack, S),
    not(soapy(brush, S)),
    loc(brush, dish_rack, S),
    not(faucetOn(S)).

%% Goal states for dishwashingInit2
goal_state(21, S) :-
    not(dirty(p1, S)),
    not(soapy(p1, S)).

goal_state(22, S) :-
    not(dirty(p1, S)),
    not(soapy(p1, S)),
    loc(p1, dish_rack, S),
    not(dirty(p2, S)),
    not(soapy(p2, S)),
    loc(p2, dish_rack, S).

%% Goal states for dishwashingInit3
goal_state(31, S) :-
    not(dirty(p1, S)),
    not(soapy(p1, S)),
    not(dirty(g1, S)),
    not(soapy(g1, S)),
    loc(p1, dish_rack, S),
    loc(g1, dish_rack, S).

% auxilary dishwashing

place(counter).
place(dish_rack).

scrubber(sponge).
scrubber(brush).

dish(X) :- glassware(X).
dish(X) :- plate(X).

item(X) :- glassware(X).
item(X) :- plate(X).
item(X) :- scrubber(X).

% precondition_axioms_dishwashing

% pick up an item
poss(pickUp(X, P), S) :-
    item(X),
    place(P),
    loc(X, P, S),
    not(holding(X, S)),
    numHolding(N, S),
    N < 2.

% put down an item
poss(putDown(X, P), S) :-
    item(X),
    place(P),
    holding(X, S),
    numHolding(N, S),
    N > 0.

% turn on faucet
poss(turnOnFaucet, S) :-
    not(faucetOn(S)),
    numHolding(N, S),
    N =< 1.

% turn off faucet
poss(turnOffFaucet, S) :-
    faucetOn(S),
    numHolding(N, S),
    N =< 1.

% add soap to scrubber
poss(addSoap(X), S) :-
    scrubber(X),
    holding(X, S),
    numHolding(N, S),
    N =< 1.

% scrub a glassware
poss(scrub(X, brush), S) :-
    glassware(X),
    holding(X, S),
    holding(brush, S).

% scrub a plate
poss(scrub(X, sponge), S) :-
    plate(X),
    holding(X, S),
    holding(sponge, S).

% rinse dish/item
poss(rinse(X), S) :-
    item(X),
    holding(X, S),
    faucetOn(S).

% successor_state_axioms_dishwashing

% holding/2: X is held after picking it up
holding(X, [pickUp(X, _) | S]).

% holding/2: X continues to be held unless it is put down
holding(X, [Action | S]) :-
    not(Action = putDown(X, _)),
    holding(X, S).

% loc/3: X is at place P after being put down at P
loc(X, P, [putDown(X, P) | S]).

% loc/3: X stays at P unless it is picked up or put down somewhere else
loc(X, P, [Action | S]) :-
    not(Action = pickUp(X, _)),
    not(Action = putDown(X, _)),
    loc(X, P, S).

% faucetOn/1: faucet is on after turnOnFaucet
faucetOn([turnOnFaucet | S]).

% faucetOn/1: faucet stays on unless turned off
faucetOn([Action | S]) :-
    not(Action = turnOffFaucet),
    faucetOn(S).

% numHolding/2: increase by 1 when picking up a new item
numHolding(N1, [pickUp(X, _) | S]) :-
    numHolding(N, S),
    not(holding(X, S)),
    N < 2,
    N1 is N + 1.

% numHolding/2: decrease by 1 when putting down a held item
numHolding(N1, [putDown(X, _) | S]) :-
    numHolding(N, S),
    holding(X, S),
    N > 0,
    N1 is N - 1.

% numHolding/2: otherwise stays the same
numHolding(N, [Action | S]) :-
    not(Action = pickUp(_, _)),
    not(Action = putDown(_, _)),
    numHolding(N, S).

% soapy/2: scrubber becomes soapy after addSoap(X)
soapy(X, [addSoap(X) | S]) :-
    scrubber(X),
    holding(X, S).

% soapy/2: dish X becomes soapy when scrubbed with a soapy scrubber Y
soapy(X, [scrub(X, Y) | S]) :-
    scrubber(Y),
    dish(X),
    soapy(Y, S).

% soapy/2: X remains soapy unless it is rinsed
soapy(X, [Action | S]) :-
    soapy(X, S),
    not(Action = rinse(X)).

% dirty/2: X remains dirty unless rinsed while soapy
dirty(X, [Action | S]) :-
    dirty(X, S),
    not((Action = rinse(X), soapy(X, S))).

% wet/2: X becomes wet after being rinsed
wet(X, [rinse(X) | S]).

% wet/2: wetness persists (no drying action)
wet(X, [Action | S]) :-
    wet(X, S).

% declarative_heuristics_dishwashing

% there is no glassware in this world, time shortening for state 22. 
no_glassware :-
    not(glassware(_)).

% at least one dish is still dirty, time shortening for state 31
some_dirty(S) :-
    dish(X),
    dirty(X, S).

% cannot pick up something you are already holding
useless(pickUp(X, _), S) :-
    holding(X, S).

% cannot put down something you are not holding
useless(putDown(X, _), S) :-
    not(holding(X, S)).

% cannot turn on faucet if already on
useless(turnOnFaucet, S) :-
    faucetOn(S).

% cannot turn off faucet if already off
useless(turnOffFaucet, S) :-
    not(faucetOn(S)).

% cannot add soap to scrubber that is already soapy
useless(addSoap(X), S) :-
    soapy(X, S).

% cannot scrub dish with scrubber that is not soapy
useless(scrub(X, Y), S) :-
    dish(X),
    scrubber(Y),
    not(soapy(Y, S)).

% cannot pick up if both hands are full
useless(pickUp(_, _), S) :-
    numHolding(N, S),
    N >= 2.

% adding soap to something that is not a scrubber
useless(addSoap(X), S) :-
    not(scrubber(X)).

% rinsing when faucet is off
useless(rinse(X), S) :-
    not(faucetOn(S)).

% scrubbing a dish that is already clean
useless(scrub(X, _), S) :-
    dish(X),
    not(dirty(X, S)).

% rinsing an item that is neither dirty nor soapy
useless(rinse(X), S) :-
    item(X),
    not(dirty(X, S)),
    not(soapy(X, S)).

% if there is no glassware at all, any action involving the brush is useless
useless(pickUp(brush, _), _) :-
    no_glassware.

useless(putDown(brush, _), _) :-
    no_glassware.

useless(addSoap(brush), _) :-
    no_glassware.

useless(scrub(_, brush), _) :-
    no_glassware.
 
% turning off the faucet while some dish is still dirty is useless
useless(turnOffFaucet, S) :-
    some_dirty(S).

% putting a dirty glass g1 back on the counter is useless
useless(putDown(g1, counter), S) :-
    dirty(g1, S).

% putting a clean plate p1 back on the counter is useless
useless(putDown(p1, counter), S) :-
    not(dirty(p1, S)),
    not(soapy(p1, S)).