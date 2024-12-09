-- === PEARL ASSIGNMENT 010, FUNCTIONAL PROGRAMMING ===


{-
  Take your time and carefully read these rules before you start!

  Rules:
    * Submission deadline: Friday 27 September, 2024, 23:59h.
    * Late submission until Sunday, 29 September, 2024, 23:59h. Late submissions cannot get the bonus.
    * The assignment must be made in groups of AT MOST two students.
    * Complete this file, and submit it on Canvas.

    * We will grade most submissions automatically. In particular:
      * for each function we ask you to implement, replace the default stub by your implementation.
        DO NOT CHANGE THE FUNCTION NAME OR PARAMETERS
        (you are welcome to add your own auxiliary functions)
      * do not change any other parts of this file.
      * do not import additional modules. You don't need them.
        * Careful: some editors seem to automatically add some Windows-specific modules.
        * We will strip whatever import declaration you have from the file anyway, and replace it by the original one. If your program doesn't compile anymore, you'll fail the assignment!
      * if you choose to not implement a function, leave the default stub.
        DO NOT REMOVE THE FUNCTION
      * IF YOU DO NOT FOLLOW THE ABOVE RULES: you are likely to fail the assignment, independently of whether your code might work on your machine or not.

  Grading:
    To pass, you must have no more than 4 missing/incorrect answers. An answer is incorrect if a function does not provide the correct answer within a reasonable amount of time. We'll give your program enough time such that you can go for nice and simple solutions without worrying about efficiency. Just don't do obviously inefficient things.
    As a rule of thumb: all tests that we provide in this file should run in less than 10 seconds (except the efficiency tests for the recursive and unit-propagation solver, see comments there)

    To get the bonus, all questions must be answered correctly, and your code must be clean and readable.

    A question is graded as correct if it passes our regression tests.
    The tests we will use are similar to the quickCheck properties we provide, except that:
      * they depend less on each other: many properties use concepts that you were asked to implement yourself. Our tests will use our (correct) reference implementations there. Note that this is to your advantage, as it minimizes follow-up errors)

      * they may be more exhaustive. We tried to include as many tests as we could without disclosing the solutions.
        However, we will also test your implementations against our reference implementation.


    SUBMIT YOUR SOLUTION IN ANY CASE, EVEN IF YOU THINK YOU DON'T HAVE ENOUGH CORRECT ANSWERS!
    WE MIGHT ADJUST THE GRADING AFTERWARDS TO ALLOW MORE FAILED QUESTIONS, IF WE SEE THAT THE ASSIGNMENT WAS TOO HARD.

  You are welcome (and encouraged) to implement additional tests!

  Note that this is a project assignment rather than an exam. As such, the later questions heavily depend on the earlier ones being done correctly! We have tried to help you by specifying exhaustive test properties, in particular against the basic concepts on which the later questions depend. Do not continue until you think that you have got the earlier questions right!

  You can execute the main function to get an overview of how many of the provided QuickCheck tests already succeed,
  in ghci, just type
  > main

  (initially, everything will fail)

-}


{-
If you want to provide feedback or comment, please leave it here. Unfortunately, we will not see comments on Canvas.
------------------------------------------------------------------------------

Andrei Ursachi - 3351912
Dominika Kapla - 3406636


------------------------------------------------------------------------------
-}


module SAT where

-- DO NOT MODIFY OR ADD IMPORTS
import Test.QuickCheck
import Data.List
import Data.Maybe




{-

  The Boolean Satisfiability Problem (SAT) is to decide whether a given formula over Boolean variables and
  the operators and, or, not can be satisfied, i.e., if the variables can be assigned values such that the formula holds. See also https://en.wikipedia.org/wiki/Boolean_satisfiability_problem for more information and background.

  For example, consider the formula F1 "(a or b) and (not a or b)".
  This formula can be satisfied by assigning a=True and b=True.

  Now consider the formula F2 "(a or b) and (not a) and (not b)".
  There is no assignment to a or b such that this formula holds.
  We can see this as follows: because of the second conjunct "(not a)",
  we have to assign a=False, and because of the third conjunct "(not b)", we have
  to assign b=False. However, with this assignment, the first conjunct "(a or b)" does not hold.

  It is common to only consider formulas in conjunctive normal form (CNF).
  A CNF formula is a conjunction of clauses, where a clause is a disjunction of literals, and a literal is
  a variable or a negated variable. For example, the formula "(a or b) and (not a or b)" is in CNF over the variables a and b. Its clauses are "a or b" and "not a or b", and its literals are a, b, and not b.

  We also assume that a clause does not contain the same variable twice:
  1) if it contains the same literal twice, e.g., "a or a or b", this is the same as "a or b".
  2) if it contains opposite literals, e.g., "a or not a or b", the clause is always true.

  Thus, these assumptions do not limit the expressiveness of CNF, but they do make algorithms simpler,
  as less corner-cases have to be considered!


  The standard representation for CNF formulas uses positive integers for the variables.
  A literal is represented by a non-zero integer, negative integers meaning negated variables.
  Clauses are represented as lists of literals, and the CNF itself is a list of clauses.

  For example, the above formulas F1 and F2 could be represented as

  F1 [[1,2],[-1,2]]
  F2 [[1,2],[-1],[-2]]

  In Haskell, we can define the above concepts as follows:
-}

type Var = Int
type Lit = Int
type Clause = [Lit]
type Cnf = [Clause]

-- These are the two formulas F1 and F2 from above
cnf1 :: Cnf
cnf1 = [[1,2],[-1,2]]

cnf2 :: Cnf
cnf2 = [[1,2],[-1],[-2]]

{- Question 1: 
  To warm up, implement a function that checks that a list has no duplicate elements.
  Note: Eq a would be enough, but you can implement it more efficiently when you know Ord a. (You are not required to)
-}

isDistinct :: Ord a => [a] -> Bool
isDistinct xs
    | xs == [] = True
    | head xs `elem` tail xs = False
    | otherwise = isDistinct (tail xs)

-- This property tests the implementation of isDistinct
prop_isDistinct :: [Int] -> Bool
prop_isDistinct xs = isDistinct xs == (nub xs == xs)

{- Question 2: 
  Implement a function to check that a clause (list of Integers) is well-formed,
  that is, it contains no 0s, no duplicates, and no opposite literals (both, l and -l).
-}
isNotOpposite :: (Ord a, Num a) => [a] -> Bool
isNotOpposite xs
    | xs == [] = True
    | (-1 * (head xs)) `elem` tail xs = False
    | otherwise = isNotOpposite (tail xs)

isWfClause :: Clause -> Bool
isWfClause cl = isDistinct cl && not (0 `elem` cl) && isNotOpposite cl

prop_wfClause = withMaxSuccess 1 $ all isWfClause wf_clauses && all (not.isWfClause) nwf_clauses
  where
    wf_clauses = [
        [],
        [1],
        [1,2,-3],
        [2,-3,1],
        [-1,8]
      ]

    nwf_clauses = [
        -- contains zero
        [0],
        [0,0,0],
        [1,2,0],

        -- duplicates
        [1,1,2,3,4,-5],
        [1,3,4,3,-5],

        -- opposite literals
        [1,2,-1],
        [1,2,-1,0], -- also has zero
        [2,1,3,4,-5,-3],
        [1,-1,1,-1,1], -- also has dup
        [1,-1,1,0,-1,1] -- also has dup and 0
      ]


{- Question 3: 
  Implement a function to check that all clauses of a Cnf are well-formed.
-}
isWfCnf :: Cnf -> Bool
isWfCnf cnf
    | cnf == [] = True
    | isWfClause (head cnf) = isWfCnf (tail cnf)
    | otherwise = False


{- From now on, you can assume that, unless otherwise mentioned, the Cnfs passed to your functions are well-formed! -}

{- Question 4: 

  Implement functions to return the literals and the variables of a Cnf, without duplicates
-}

litsOfCnf :: Cnf -> [Lit]
litsOfCnf [] = []
litsOfCnf cnf = removeDuplicates [x | l <- cnf, x <- l]
  where
    removeDuplicates [] = []
    removeDuplicates (x:xs)
        | x `elem` xs = removeDuplicates xs
        | otherwise = x : removeDuplicates xs

varsOfCnf :: Cnf -> [Var]
-- nub removes all the dupplicates
varsOfCnf cnf = nub [abs var | clause <- cnf, var <- clause]

-- The next properties test your implementation of litsOfCnf and varsOfCnf

-- Sometimes, just explicitly testing for some fixed input can uncover trivial errors
-- We use withMaxSuccess to prevent the exact same test being repeated 100 times.
prop_litsOfCnfFixed = withMaxSuccess 1 $
     litsOfCnf [] == []
  && litsOfCnf [[]] == []
  && sort (litsOfCnf [[1,2],[-1],[1,2,-3,4],[-2,7]]) == [-3,-2,-1,1,2,4,7]


prop_varsOfCnfFixed = withMaxSuccess 1 $
     varsOfCnf [] == []
  && varsOfCnf [[]] == []
  && sort (varsOfCnf [[1,2],[-1],[1,2,-3,4],[-2,7]]) == [1,2,3,4,7]


-- Test with random well-formed CNFs
prop_litsOfCnf cnf = isWfCnf cnf ==> isDistinct (litsOfCnf cnf) --EXCLUDE
prop_varsOfCnf cnf = isWfCnf cnf ==> isDistinct (varsOfCnf cnf) && all (>0) (varsOfCnf cnf) --EXCLUDE

{-
  Note: when you run the above properties, you might get results like

  ghci> quickCheck prop_litsOfCnf
  +++ OK, passed 100 tests; 727 discarded.

  or even

  ghci> quickCheck prop_litsOfCnf
  *** Gave up! Passed only 93 tests; 1000 discarded tests.

  This is because the default generator used by quickCheck for [[Int]] is likely to generate a list of lists that
  contains a zero somewhere, and thus is not a well formed Cnf. Those test cases are discarded, and if too many are discarded, quickCheck gives up.

  To alleviate this problem, we have to use a custom quickCheck generator.
  You don't need to know how to implement these generators (we've done that for you at the and of this file),
  but we show you how to use them. Here are the two properties again, using a custom generator:
-}

prop_litsOfCnf' = forAll genCnf $ \cnf -> isDistinct (litsOfCnf cnf)
prop_varsOfCnf' = forAll genCnf $ \cnf -> isDistinct (varsOfCnf cnf) && all (>0) (varsOfCnf cnf)

{-
  The generator genCnf generates only well-formed Cnfs.
  Of course, we can verify this statement:
-}

prop_testGenCnf = forAll genCnf $ \cnf -> isWfCnf cnf
-- If this test fails for you, your isWfCnf function is too strict, rejecting actually well-formed CNFs


{-
  An assignment assigns truth values (True or False) to variables.
  We represent assignments as a list of those literals that are true under the assignment.
  For example, assigning variables 1,3 to true, and 2,4 to false is represented as [1,3,-2,-4].
-}

type Assignment = [Lit]


{-
  Like for clauses, we do not want duplicate variables in an assignment:
    1) duplicate literals, such as in "[1,-2,1,1,-2,-2,-2]" are simply redundant
    2) opposite literals, such as in "[1,-1,2,3]" make no sense (variable 1 cannot be true and false at the same time)

  Also, a 0 makes no sense, as it does not corresponds to any variable.

  These are exactly the same conditions as for a well-formed clause, so we can simply reuse the check here:
-}
isWfAss :: Assignment -> Bool
isWfAss = isWfClause

-- The genAss generator creates well-formed assignments.
-- If you get an error here, your isWfClause (that we used for isWfAss) is too strict, rejecting actually well-formed clauses/assignments!)
prop_genAssWf = forAll genAss isWfAss

{-
  Form now on, you can assume that assignments passed to your functions are well-formed
-}



{- Question 5: 
  Write functions to evaluate a literal, a clause, and a formula, wrt. a given assignment.

  Note that the assignment may not assign all variables (i.e., for a variable v, it may contain neither v nor -v).
  This means that the formula should hold independent of the value of v.
  To achieve that, you can evaluate both, v and -v to False.

  Intuitively, we have:
  1) A literal evaluates to True iff it is contained in the assignment.
  2) A clause evaluates to True iff it contains a literal that evaluates to True.
  3) A Cnf evaluates to True if all its clauses evaluate to True.

  Note the following two corner cases:
    An empty clause, i.e., one that contains no literals at all, is always False.
    An empty formula, i.e., one that has no clauses, is always True.

  Terminology: if a formula (clause/literal) evaluates to true wrt. an assignment,
  we also say that "the assignment satisfies the formula".

  A formula that cannot be satisfied by any assignment is "unsatisfiable".

-}

-- A literal evaluates to true iff it is contained in the assignment.
evalLit :: Assignment -> Lit -> Bool
evalLit a l = l `elem` a -- We have implemented this one for you

-- A clause evaluates to True iff it contains at least one literal that evaluates to True
evalClause :: Assignment -> Clause -> Bool
evalClause _ [] = False
evalClause a (c:cl)
    | c `elem` a = True
    | otherwise = evalClause a cl

-- A Cnf evaluates to True if all its clauses evaluate to True.
evalCnf :: Assignment -> Cnf -> Bool
evalCnf _ [] = True
evalCnf a (cl:cls)
    | evalClause a cl = evalCnf a cls
    | otherwise = False

-- Corner case: empty clause is always false
prop_evalEmptyClause = forAll genAss $ \a -> not $ evalClause a []
-- Corner case: empty formula is always true
prop_evalEmptyCnf = forAll genAss $ \a -> evalCnf a []

-- Some fixed tests:
prop_evalFixed = withMaxSuccess 1 $
     evalCnf [] [] -- The empty formula is always true
  && not (evalCnf [] [ [] ]) -- A formula that contains the empty clause is always false
  && evalCnf [1,2] [ [1,2],[-2,1],[-1,2] ] -- The clauses of this formula are always true
  && evalCnf [2,1] [ [2,1],[-2,1],[-1,2] ] -- You must not assume sortedness of assignments (or clauses)
  && not (evalCnf [1,2] [ [-1,2], [-1,-2] ]) -- The second clause is False
  && not (evalCnf [1,2] [ [-1], [-1,-2] ]) -- Both clauses are False

  -- Assigning variables that do not occur in the formula simply has no effect
  && evalCnf [2,1,5,-42] [ [2,1],[-2,1],[-1,2] ] -- same as above
  && not (evalCnf [1,2,-3,4,-5,6] [ [-1,2], [-1,-2] ]) -- same as above

  -- Partial assignments
  && evalCnf [2,1] [ [1,2], [3,4,1], [-1,-3,-4,2] ] -- Partial assignments are OK, if the formula is true no matter the values of the unassigned variables

  && not (evalCnf [1,2] [ [-1,2], [-1,-2,3] ]) -- The second clause is not guaranteed to be true (for -3 it's actually false)
  && not (evalCnf [1,2,-3] [ [-1,2], [-1,-2,3] ])
  && evalCnf [1,2,3] [ [-1,2], [-1,-2,3] ] -- and for 3, it's true



{-
  Note: many of the subsequent tests depend on evalCnf being correct, so make double-sure you got that right.
  Otherwise subsequent tests may not detect errors or reject correct implementations!
-}


{- Question 6: 
  An assignment that assigns exactly the variables of a formula (not more, not less) is called "exact".

  Implement a function to check if a (well-formed) assignment assigns exactly a given (distinct) list of variables.
-}

isExactAss :: [Var] -> Assignment -> Bool
isExactAss vars a
    | length vars /= length a = False
    | otherwise = sort (nub [abs x | x <- vars]) == sort (nub [abs x | x <- a])

prop_isExactAss = withMaxSuccess 1 $
     isExactAss [1,3,5] [-3,1,-5] -- Make sure you don't rely on the order of variables!
  && isExactAss [5,1,3] [-3,1,-5] -- Make sure you don't rely on the order of variables! (I added this case)
  && isExactAss [] []
  && not (isExactAss [1,3] [-3,1,-5])
  && not (isExactAss [1,3,5,6] [-3,1,-5])
  && not (isExactAss [] [-3,1,-5])
  && not (isExactAss [1,2,3] [])


{- Question 7: 

  Given a list of variables (without duplicates), implement a function that returns a list of all assignments to exactly those variables, without duplicates.

  Note the corner case that there are no variables. In this case, there is one assignment, that assigns no variables.

  For n variables, how many assignments are there?
-}

allAss :: [Var] -> [Assignment]
allAss [] = [[]]
allAss (v:vs) = [v:a | a <- allAss vs] ++ [-v:a | a <- allAss vs]

numAss :: Int -> Int  -- Number of assignments for n variables
numAss n = 2 ^ n

prop_allAssNoVars = allAss [] == [[]]

prop_allAss = forAll (resize 10 $ dlistOf genVar) $ \vs -> let as = allAss vs in
     isDistinct as -- No duplicate assignments are returned
  && all (\a -> isWfAss a && isExactAss vs a) as  -- All generated assignments are well-formed and exact

prop_numAss = forAll (resize 10 $ dlistOf genVar) $ \vs ->
  length (allAss vs) == numAss (length vs) -- Check that correct length is computed


{- Question 8: 
  Implement a brute-force SAT solver: for a given Cnf, enumerate all (exact) assignments,
  and check if there is one that satisfies the Cnf.

  If you find one, return Just it. If the formula is unsatisfiable, return Nothing.
-}

satsolverBf :: Cnf -> Maybe Assignment
satsolverBf cnf =
    let vars = varsOfCnf cnf
        assignments = allAss vars
    in goodAssignments assignments cnf

goodAssignments :: [Assignment] -> Cnf -> Maybe Assignment
goodAssignments [] _ = Nothing
goodAssignments (a:assignm) cnf
    | evalCnf a cnf = Just a
    | otherwise = goodAssignments assignm cnf

-- Template for a property that checks a sat-solver:
gen_prop_satsolver solver = forAll genCnf $ \cnf ->
  case solver cnf of
       Just a -> label "sat" $
         isWfAss a && evalCnf a cnf -- If solver returns an assignment, it is well-formed and satisfies the formula
       Nothing -> label (if [] `elem` cnf then "triv-unsat" else "unsat") $
         not$any (\a->evalCnf a cnf) (allAss (varsOfCnf cnf)) -- If solver returns Nothing, no assignment over the formula's variables satisfies the formula

prop_satsolverBf = gen_prop_satsolver satsolverBf


{- Question 9: 

  When we assign a literal, we can simplify the formula, using the well-known
  laws of logic: "not True == False", "not False == True", "True and a == a", etc.

  In essence, when assigning literal l, then
    1) all occurrences of -l can be removed from the clauses
    2) each clause that contains l can be removed from the formula

    For 1) after replacing l by False, the clause has the form (False or other-literals), which is other-literals.

    For 2) after replacing l by True, the clause has the form (True or ...), which is True.
    Thus, the formula has the form (True and other-clauses), which is other-clauses.

  Implement a function that simplifies a Cnf by assigning a literal l,
  i.e., removes all clauses that contain l from the formula,
  and all occurrences of -l from the clauses. For example
    assign -2 [ [1,2],[3],[1,-2]] == [ [1],[3] ]

-}

assign :: Cnf -> Lit -> Cnf
assign cnf l = [filter (/= -l) cl | cl <- cnf, not (l `elem` cl)]


-- After assigning a literal l, the corresponding variable does not occur in the formula any more.
-- Clauses containing l should have been removed altogether, and -l should have been removed from all clauses
prop_assign = forAll genCnfVar $ \(cnf,l) ->
  abs l `notElem` varsOfCnf (assign cnf l)

prop_assignFixed = withMaxSuccess 1 $
     assign [ [1,2],[3],[1,-2] ] (-2) `eqCnf` [ [1],[3] ]
  && assign [ [1,2],[3],[1,-2] ] 4    `eqCnf` [ [1,2],[3],[1,-2] ]
  && assign [ [1,2],[3],[1,-2] ] 3    `eqCnf` [ [1,2],[1,-2] ]
  && assign [ [1,2],[3],[1,-2] ] (-3) `eqCnf` [ [1,2],[],[1,-2] ]



{- We can also check if assign is consistent with the eval function you have implemented earlier:
  An assignment satisfies a formula, iff and only iff assigning all variables from the assignment yields the
  empty formula.

  If this property fails, something is wrong with at least one of the functions assign, allAss, or varsOfCnf.

  Note that we reduce the test size, as the test is exponential in the number of variables.
-}
prop_assign2 = withMaxSize 30 $ forAll genCnf $ \cnf -> all (check cnf) (allAss (varsOfCnf cnf))
  where
    check cnf a = evalCnf a cnf == (null $ assigns cnf a)
    assigns = foldl assign





{- Question 10: 

  We now implement a different SAT solving strategy:
    1. if the formula is empty, it's satisfiable
    2. if it contains the empty clause, its unsatisfiable
    otherwise:
    3. choose some literal l of the formula
    4. assign l, and try to recursively solve the resulting formula.
       If this succeeds, we have found a solution
    5. Otherwise, assign -l, and try to recursively solve the formula.
       If this succeeds, we have found a solution. If it fails, the formula is unsatisfiable.

  Implement this solving strategy as a recursive function.

-}


-- Return Just a satisfying assignment, or Nothing if there is none. Use recursive strategy described above.
satsolverRec :: Cnf -> Maybe Assignment
satsolverRec cnf
    -- CNF formula empty - satisfiable
    | cnf == [] = Just []
    -- CNF contains an empty clause - unsatisfiable
    | [] `elem` cnf = Nothing
    | otherwise = 
        -- Choose a literal and solve recursively
        let l = extract_literal cnf
            new_cnf = assign cnf l
        in case satsolverRec new_cnf of
            -- If assigning the literal succeeds, return the assignment
            Just assignment -> Just (l : assignment)
            -- If it fails, assign the negation and check
            Nothing ->
                let new_cnf_negate = assign cnf (-l)
                in case satsolverRec new_cnf_negate of
                    -- If the assignment of negation succeeds, return it
                    Just assignment -> Just ((-l) : assignment)
                    -- If both fail, return Nothing
                    Nothing -> Nothing -- we can use Just and Nothing because of the Maybe

extract_literal = head . head -- this get the first clause from cnf and after that it gets the first literal from the clause

prop_satsolverRec = gen_prop_satsolver (satsolverRec)


{-
  The formulas generated by genAntiBfCnf are easy for the recursive strategy.
  Assigning any variable to the "wrong" value results in an empty clause, such that the solver backtracks immediately.

  The brute-force solver, however, has to still go through all variables.

  If this test times out, check that you have implemented the correct recursive algorithm, in particular,
  that you terminate your search as soon as the empty clause is in the formula!

  To get an impression how these formulas look, use

  > antiBfCnf 5

  The ones created by the generator are the same formulas, just with randomly shuffled and renamed variables.

-}
prop_satsolverRecEfficient = forAll (genAntiBfCnf 30) $ \cnf -> within 10000000 (satsolverRec cnf == Nothing)


{- Question 11: 

  Recall how we argued that the formula cnf2 = [[1,2],[-1],[-2]] is unsatisfiable:

  We must assign the literal -1, otherwise the clause [-1] will be false, and thus the formula will be false.
  Analogously for -2, but then the first clause will be False.

  A clause that only contains a single literal is called a "unit clause", the literal a "unit literal".
  Every satisfying assignment for a formula must contain all unit literals of that formula.

  Thus, if we assign a unit literal in a formula, the resulting formula is satisfiable if and only if the
  original formula is satisfiable.

  Implement a function to find a unit literal in a formula. Return Just the unit literal, or Nothing if there is none.

  Then implement a function that repeatedly finds and assigns a unit literal in a formula,
  until there are no unit literals left.
  The function shall return the list of assigned literals and the new formula.

  This process is called "unit propagation"

-}

findUnit :: Cnf -> Maybe Lit -- return a unit literal of the formula, if there is any
findUnit [] = Nothing
findUnit (clause:clauses)
    -- length is 1 so we just get the value or nothing if we find nothing untill end of recursiveness
    | length clause == 1 = Just (head clause)
    | otherwise = findUnit clauses

propagateUnits :: Cnf -> ([Lit],Cnf) -- propagate unit literals until none are left
propagateUnits cnf = propagate [] cnf
  where
    propagate :: [Lit] -> Cnf -> ([Lit], Cnf)
    propagate ass_lit cnf =
        -- Search for unit literals in cnf
        case findUnit cnf of
            -- if no unit literal found return the current ass_lit and the cnf
            Nothing -> (ass_lit, cnf)
            -- if we found them we prepend them to the current ass_lit and we keep searching for more
            Just unit ->
                let new_cnf = assign cnf unit
                in propagate (unit : ass_lit) new_cnf

-- Note: unit propagation must be recursive, as propagating a unit literal can yield new unit literals:
prop_propagateUnitsIsRec = withMaxSuccess 1 $
     cnf' `eqCnf` []
  && sort uls == [-2,1,3]
  where
    cnf = [ [1,2], [-1,2,3], [-2] ]
    (uls,cnf') = propagateUnits cnf


prop_propagateUnits = forAll genCnf pr where
  pr cnf =
       isWfAss uls  -- The list of assigned unit literals is a valid assignment (no dups, no 0s, no opposite literals)
    && (all (\cl -> length cl /= 1) cnf') -- No more units left in formula after unit propagation
    && (null $ (map abs uls ++ vs') \\ vs) -- new formula does not contain any of the reportedly assigned variables (uls), nor any new variables. It may well contain less variables than the original formula, though!
    where
      (uls,cnf') = propagateUnits cnf
      vs = varsOfCnf cnf
      vs' = varsOfCnf cnf'

-- This test is exponential, so we use reduced test size
prop_propagateUnitsSlow = withMaxSize 30 $ forAll genCnf pr where
  pr cnf =
    all (\a -> evalCnf a cnf' == evalCnf (uls++a) cnf) (allAss vs') -- Evaluating the new formula yields the same result as evaluating the old formula (with the unit literals assigned according to uls)
    where
      (uls,cnf') = propagateUnits cnf
      vs = varsOfCnf cnf
      vs' = varsOfCnf cnf'




{- Question 12: 

  Amend the recursive sat solver from the previous question to perform unit-propagation before each step
-}

satsolverUp :: Cnf -> Maybe Assignment
satsolverUp cnf =
    -- start with unit propagation
    let (unit_lit, new_cnf) = propagateUnits cnf
    in case new_cnf of
        -- if the CNF formula is empty it is ok
        [] -> Just unit_lit
        -- if the CNF formula contains an empty clauses it is not good
        _ | [] `elem` new_cnf -> Nothing
        -- otherwise take the first literal and try solving reccursively
        _ -> 
            let l = extract_literal new_cnf
                new_cnf_2 = assign new_cnf l
            in case satsolverUp new_cnf_2 of
                -- if assigning the literal succeeds return the assignment
                Just assignment -> Just (unit_lit ++ (l : assignment))
                -- if it fails assign the negation and check
                Nothing ->
                    let new_cnf_2 = assign new_cnf (-l)
                    in case satsolverUp new_cnf_2 of
                        -- if assignment of negation succeeds return it
                        Just assignment -> Just (unit_lit ++ ((-l) : assignment))
                        -- if both fail nothing
                        Nothing -> Nothing




prop_satsolverUp = gen_prop_satsolver satsolverUp


{-
  The formulas generated by genAntiRecCnf are easy for the recursive strategy with unit propagation.
  Actually, unit-propagation reduces them to a formula containing the empty clause in a single step.

  However, they are hard for the brute-force solver and the recursive solver.

  If this test times out, check that you have implemented the unit propagation correctly, and actually are doing
  unit propagation before every step of your solver.

  Note: we've set the timeout to 2s here, and the generated formula are already quite big.
  However, even without optimizing for efficiency too much (just avoid obviously inefficient code), you should keep
  well within this time limit (if you implement the required algorithm).

-}
prop_satsolverUpEfficient = within 2000000 (forAll (genAntiRecCnf 50) $ \cnf -> satsolverUp cnf == Nothing)





{-
#################################

DO NOT MODIFY ANYTHING BELOW THIS LINE

-}

-- Check for CNFs being equal. Assumes well-formed CNF
eqCnf :: Cnf -> Cnf -> Bool
eqCnf a b = norm a == norm b where
  norm cnf = sort (nub (map sort cnf))


-- Naive disjoint list generator
dlistOf :: Eq a => Gen a -> Gen [a]
dlistOf g = fmap nub $ listOf g


genVarsN :: Int -> Gen [Int]
genVarsN s = sublistOf [1..s]

genClauseN :: Int -> Gen Clause
genClauseN s = do
  vars <- genVarsN s
  signs <- vectorOf (length vars) (elements [-1,1])
  return$ map (uncurry (*)) (vars `zip` signs)


-- Generate distinct list of positive Ints, over narrow range
genVars :: Gen [Int]
genVars = sized (\s -> genVarsN (s `div` 4))

genClause :: Gen Clause
genClause = sized (\s -> genClauseN (s `div` 4))

genVar :: Gen Var
genVar = choose (1, 10)

-- Generate a literal
genLiteral :: Gen Lit
genLiteral = do
  v <- genVar
  elements [v, -v]

-- Generator to shuffle CNF
shuffleCnf :: Gen Cnf -> Gen Cnf
shuffleCnf g = do
  cnf <- g
  cnf' <- mapM  shuffle cnf
  shuffle cnf'

renameCnf :: Gen Cnf -> Gen Cnf
renameCnf g = do
  cnf <- g
  let vars = varsOfCnf cnf
  perm <- shuffle vars
  let vm = perm `zip` [1..length vars]
  let rename v = fromJust (lookup (abs v) vm) * signum v

  let cnf' = map (map rename) cnf

  return cnf'


-- Generate wf Cnf
genCnf :: Gen Cnf
genCnf = shuffleCnf (dlistOf genClause)

-- Generate wf Cnf and a variable of this Cnf
genCnfVar = do
  cnf <- genCnf
  var <- elements $ varsOfCnf cnf
  return (cnf,var)

-- Generate a well-formed assignment without duplicates
genAssFor vars = do
  signs <- vectorOf (length vars) (elements [-1,1])
  return$ map (uncurry (*)) (vars `zip` signs)

genAss = do
  vars <- dlistOf genVar
  genAssFor vars



{- Formula where the brute-force solver is bad, but the recursive approach is fast.
  Only pure literals, and unit clauses which each literal, such that a wrong assignment
  immediately reduces the formula to unsat.
-}

antiBfCnf n = [[-l i | i<-[1..n]]] ++ [[l i] | i<-[1..n]] where
  l i | even i = i
      | odd i = -i

genAntiBfCnf n = (shuffleCnf.renameCnf) (return $ antiBfCnf n)


{- Formula that needs unit propagation for efficient solving.

  Unit propagation solves this formula in one step.
  The naive recursive solver must be lucky and assign the unit literal early to solve this quickly.
  The other clauses are engineered to keep many 'distractor' literals alive.

-}

genAntiRecCnfAux :: Int -> Gen Cnf
genAntiRecCnfAux n = do
  distractors <- vectorOf (n^2) (genClauseN n)
  let units = concat [ [ [i,n+1], [i,-(n+1)], [-i,n+1], [-i,-(n+1)] ] | i<-[1..n] ]
  -- let units = [ [-n-1], [n+1] ]

  return $ distractors ++ units

genAntiRecCnf n = (shuffleCnf.renameCnf) (genAntiRecCnfAux n)


checkLbl :: Testable a => String -> a -> IO ()
checkLbl l prop = do
  print ("Testing "++l)
  res <- quickCheckWithResult (stdArgs {chatty=False}) (within 10000000 prop)
  if isSuccess res then
    print ("OK "++l)
  else do
    print ("**FAIL** " ++ l ++ " " ++ (output res))



main = do
  checkLbl "prop_isDistinct" prop_isDistinct
  checkLbl "prop_isDistinct" prop_isDistinct
  checkLbl "prop_wfClause" prop_wfClause
  checkLbl "prop_litsOfCnfFixed" prop_litsOfCnfFixed
  checkLbl "prop_varsOfCnfFixed" prop_varsOfCnfFixed
  checkLbl "prop_litsOfCnf'" prop_litsOfCnf'
  checkLbl "prop_varsOfCnf'" prop_varsOfCnf'
  checkLbl "prop_testGenCnf" prop_testGenCnf
  checkLbl "prop_genAssWf" prop_genAssWf
  checkLbl "prop_evalEmptyClause" prop_evalEmptyClause
  checkLbl "prop_evalEmptyCnf" prop_evalEmptyCnf
  checkLbl "prop_evalFixed" prop_evalFixed
  checkLbl "prop_isExactAss" prop_isExactAss
  checkLbl "prop_allAssNoVars" prop_allAssNoVars
  checkLbl "prop_allAss" prop_allAss
  checkLbl "prop_numAss" prop_numAss
  checkLbl "prop_satsolverBf" prop_satsolverBf
  checkLbl "prop_assign" prop_assign
  checkLbl "prop_assignFixed" prop_assignFixed
  checkLbl "prop_assign2" prop_assign2
  checkLbl "prop_satsolverRec" prop_satsolverRec
  checkLbl "prop_satsolverRecEfficient" prop_satsolverRecEfficient
  checkLbl "prop_propagateUnitsIsRec" prop_propagateUnitsIsRec
  checkLbl "prop_propagateUnits" prop_propagateUnits
  checkLbl "prop_propagateUnitsSlow" prop_propagateUnitsSlow
  checkLbl "prop_satsolverUp" prop_satsolverUp
  checkLbl "prop_satsolverUpEfficient" prop_satsolverUpEfficient
