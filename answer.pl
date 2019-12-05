% ----------------------------------------------------------------------------
% AUTHORSHIP
% This code was made by
% Lachlan Charles Douglas Piper
% Student at University of Melbourne
% Student ID: 912229
% Copyright 2019 Lachlan Piper.  All rights reserved.
% This Copyright relates to the CODE ONLY, and not project specifications or
% test code.
%
% This file contains a working solution to the Melbourne University subject
% COMP30020 Declarative Programming's second project, 2019. It is written in
% Prolog.
%
% This is the only file related to this solution.
%
% ----------------------------------------------------------------------------
% LIBRARY USE
% Uses the SWIPL and clpfd (Constraint logic programming over finite domains)
% libraries.
%
% clpfd functions used in this code:
%   - #=
%   - transpose/2
%   - all_distinct/1
%   - ins/2
%   - label/1
%   - sum/3
%
% The specifications regarding the problem this file solves are found below:
% ----------------------------------------------------------------------------
% PROJECT SPECIFICATION: PETER SCHACHTE - COMP30020
% DECLARATIVE PROGRAMMING - SEMESTER 2 - 2019 - THE UNIVERSITY OF MELBOURNE
% A maths puzzle is a square grid of squares, each to be filled in with a single
% digit 1–9 (zero is not permitted) satisfying these constraints:
%
%  - each row and each column contains no repeated digits.
%
%  - all squares on the diagonal line from upper left to lower right contain the
%    same value; and.
%
%  - the heading of reach row and column (leftmost square in a row and topmost
%    square in a column) holds either the sum or the product of all the digits
%    in that row or column.
%
% Note that the row and column headings are not considered to be part of the row
% or column, and so may be filled with a number larger than a single digit. The
% upper left corner of the puzzle is not meaningful.
%
% When the puzzle is originally posed, most or all of the squares will be empty,
% with the headings filled in. The goal of the puzzle is to fill in all the
% squares according to the rules. A proper maths puzzle will have at most one
% solution.
%
% Here is an example blank puzzle (left) and solved puzzle (right):
%               __ __ __ __            __ __ __ __
%              |  |14|10|35|          |  |14|10|35|
%              |14|  |  |  |   -->    |14| 7| 2| 1|
%              |15|  |  |  |   -->    |15| 3| 7| 5|
%              |28|  |  |  |          |28| 1| 1| 7|
%               __ __ __ __            __ __ __ __
%
% You will write Prolog code to solve maths puzzles. Your program should supply
% a predicate puzzle_solution(Puzzle) that holds when Puzzle is the
% representation of a solved maths puzzle.
%
% A maths puzzle will be represented as a list of lists, each of the same
% length, representing a single row of the puzzle. The first element of each
% list is considered to be the header for that row. Each element but the first
% of the first list in the puzzle is considered to be the header of the
% corresponding column of the puzzle. The first element of the first element of
% the list is the corner square of the puzzle, and thus is ignored.
%
% You can assume that when your puzzle_solution/1 predicate is called, its
% argument will be a proper list of proper lists, and all the header squares of
% the puzzle (plus the ignored corner square) are bound to integers. Some of the
% other squares in the puzzle may also be bound to integers, but the others will
% be unbound. When puzzle_solution/1 succeeds, its argument must be ground. You
% may assume your code will only be tested with proper puzzles, which have at
% most one solution. Of course, if the puzzle is not solvable, the predicate
% should fail, and it should never succeed with a puzzle argument that is not a
% valid solution.
%
% END SPECIFICATIONS
% ----------------------------------------------------------------------------
% ASSUMPTIONS
%
% Assumption 1: Input to the goal puzzle_solution/1 will have AT LEAST all
% values in the header squares of the puzzle filled in and bound to integers.
%
% Assumption 2: This code will only be tested on puzzles that have only one
% single solution.
%
% Assumption 3: All input to puzzle_solution/1 will an NxN list, and does not
% need to be checked to be square.
%
% Assumption 4: Heading values do not need to be unique; there can be duplicate
% values in the headers
%
% ----------------------------------------------------------------------------
% ABOUT THIS CODE
% puzzle_solution(Puzzle) holds when a solution to the given puzzle is found.
% This is done by placing a number of constraints on the input, namely
% (and in order):
% 1. The diagonals in the puzzle must be the same.
% 2. the numbers in each row must be between 1 and 9 inclusive.
% 3. There must be no duplicates in any row.
% 4. Then, each row is checked to make sure the header value is either the sum
%    or product of the other numbers in the row.
%
% The Puzzle matrix is then Transposed so constraints 3 and 4 can be tested on
% the columns as if they were rows.
%
% Finally, once we have constrained variables to these domains, we make sure
% they are all ground values.
% ----------------------------------------------------------------------------
:- ensure_loaded(library(clpfd)).
% ----------------------------------------------------------------------------

puzzle_solution(Puzzle) :-
    maplist(same_length(Puzzle),Puzzle),
    transpose(Puzzle, Trans_Puzzle),
    find_diagonals(Puzzle),
    check_nums(Puzzle),
    check_dup(Puzzle), check_dup(Trans_Puzzle),
    check_valid(Puzzle),

    check_valid(Trans_Puzzle).

    %check_grounded(Puzzle).
    %check mate!

%------------------------------------------------------------------------------
%--------- ----------Below is for equating diagonals---------------------------
% find_diagonals/1 equates all values along the left-right, top-bottom diagonal
% of Puzzle. It discards the Header row, then looks at the top left value in the
% puzzle, which is the value all others will be compared to. It passes this
% information to a helper to continue the check. It holds when all diagonal
% values are the same.
find_diagonals([_| [NumberRow|Rows] ]) :-
    nth0(1, NumberRow, DiagVal),
    find_diag_helper(2, Rows, DiagVal).


% find_diag_helper/3 is a helper function. It takes an Index, a list of rows
% the diagonal value all diagonals are required to have. It looks at the value
% of a row at a given point, compares it to the current diagonal value, then
% moves to the next row's diagonal. It holds when all diagonal values are the
% same.
find_diag_helper(_, [] ,_).
find_diag_helper(Index, [Row|Rows] ,DiagVal):-
    nth0(Index, Row, DiagVal),
    Index1 #= Index + 1,
    find_diag_helper(Index1, Rows, DiagVal).
%------------------------------------------------------------------------------
%------------------- Below regards constraining numbers -----------------------
% check_nums/1 takes a list of rows as it's argument, dropping the first
% (header) row. It then passes every row to it's helper function,
% constrain_nums/1. It holds when the contraints imposed by this helper hold.
check_nums([]).
check_nums([_Heading|NumberRows]):-
    maplist(constrain_nums, NumberRows).

% constrain_nums/1 takes a row, and constrains the header (Total value of the
% row not including itself) to be >=1, and all other values to be in the range
% 1 to 9 inclusive. It holds when this is the case.
constrain_nums([_Total|Row]):-
    %Row ins 1..9.
    maplist(between(1,9),Row).

%------------------------------------------------------------------------------
% --- Below here determines if a row/column is valid, under the constraints ---
% ---------------------- given by project spec --------------------------------
% check_valid/1 takes a list of rows, and passes them to a helper function for
% further analysis on if these rows are valid under the specifications given by
% the project. It holds when the analysis of all rows holds.
check_valid([_Heading|Rows]):-
    maplist(check_row_valid, Rows).

% check_row_valid/1 takes a row and holds when EITHER the sum of the values
% of the row are equal to the header of that row, or the product of the values
% of the row are equal to the header of that row.
check_row_valid([Header|Vals]):- sum(Vals, #=, Header);prod(Vals, Header, 1).

% prod/3 takes a list of numbers from a row (not including the header), the
% header (or total to be achieved), and an accumulator (Prod). It goes through
% each element of Num|Nums is multiplied together. It holds when Prod == Total
% and there are no more elements to multiply.
prod([],X,X).
prod([Num|Nums], Total, Prod):-
    Prod1 #= Prod * Num,
    prod(Nums, Total, Prod1).

%------------------------------------------------------------------------------
%- Below involves checking a row (or transposed column) for duplicate values --
%------------------------------------------------------------------------------
% check_dup/1 takes a list of rows as it's argument and passes each row to
% a helper fuction for further analysis on that row. It holds when the
% analysis on every row holds.
check_dup([_Heading|Rows]):-
    maplist(check_row, Rows).


% check_row/1 takes a row as its argument and holds if all the elements in that
% row are distinct.
check_row([_Head|Elems]):-
    all_distinct(Elems).

%------------------------------------------------------------------------------
% ---- below regards making sure all values of a puzzle are grounded ----------
% check_grounded/1 takes a list of all rows as it's argument. It discards the
% header row (as this is assumed to be grounded) and holds when all following
% rows are grounded. The use of label here makes sure we have tried all possible
% values for variables until they are ground.
check_grounded([_|Rows]) :-
  maplist(label, Rows).
%------------------------------------------------------------------------------
