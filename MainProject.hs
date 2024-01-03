{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use if" #-}
{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use lambda-case" #-}
module FinalProject01 where

import Control.Applicative(liftA, liftA2, liftA3)
import Data.List

import CFGParsing
import Graphics.Win32 (restoreDC)

bottomUp :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
bottomUp cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([], input) in
  let goalConfig = ([NoBar start], []) in
  parser [shift, reduce] rules startingConfig goalConfig
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- IMPORTANT: Please do not change anything above here.
--            Write all your code below this line.
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--WARM UPS
isRuleCNF :: RewriteRule nt t -> Bool
isRuleCNF = \rule -> case rule of
                      NTRule lhs rhs -> length rhs == 2
                      -- NTRule lhs x:[] -> False
                      -- NTRule lhs [] -> False
                      -- NTRule lhs x:y:z:rest -> False
                      TRule lhs rhs -> True
                      NoRule -> True

isCNF :: CFG nt t -> Bool
isCNF cfg = 
  let (nts, ts, i, r) = cfg in
    and (map (\x -> isRuleCNF x) r)

pathsToGoalFSA :: (Eq st, Eq sy) => ((st,[sy]), [(st,[sy])]) -> [(st,sy,st)] -> [(st,[sy])] -> [[(st,[sy])]]

pathsToGoalFSA (current, history) rules goals =
  case elem current goals of --is the current configuration one of the goal configurations?
    True -> [history++[current]] --base case: current configuration is a goal configuration so we should return it along with the history
    False -> case current of 
              (curr_state, symbols) -> case null symbols of
                                        True -> [] --base case: reached a dead-end since we've exhausted the input, so we return an empty list 
                                        --False -> map (\config -> pathsToGoalFSA ((config, history++[current]) rules goals)) (consumeFSA rules current)
                                        False -> concatMap (\config -> pathsToGoalFSA (config, history ++ [current]) rules goals) (consumeFSA rules current)
                                        --recursive case. We still have some input left to process. Use consume FSA to find the list of all possible next steps
                                        --For each possible next step, call pathsToGoalFSA on that
                                        --False -> [pathsToGoalFSA (config, history++[current]) rules goals | config <- consumeFSA rules current]

--SHIFT
-- Applies to nonterminal rules. Look at the RHS of each nonterminal rule. Let n be the length of the RHS array. If the stack does not have at least n elements, 
-- do not consider the rule further. If the stack has at least n elements, confirm if the last n elements of the stack match the RHS exactly. If so, output a 
-- configuration where the stack has the last n elements replaced with the LHS of the rule and the input is unchanged.
shift :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shift rules (stk, inp) = case null inp of
                            True -> []
                            False -> concatMap (\r -> case r of
                                            NTRule lhs rhs -> []
                                            TRule lhs rhs -> case rhs == head inp of
                                                                True -> [ParseStep Shift (TRule lhs rhs) (stk++[NoBar lhs], tail inp)]
                                                                False -> []
                                          ) rules


--REDUCE
-- Applies to terminal rules. Look at the RHS of each terminal rule and see if it matches the first word in the input. If RHS of a terminal rule == first word 
-- in the input, output a configuration where the stack has LHS pushed onto it and the input has the first word removed.
reduce :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
reduce rules (stk, inp) = case null stk of
                            True -> [] --can't reduce anything if the stack is empty so return empty list
                            False -> concatMap (\r -> case r of
                                                TRule lhs rhs -> []
                                                NTRule lhs rhs -> case length stk >= length rhs of
                                                                    False -> []
                                                                    True -> case [NoBar s | s<-rhs] == drop (length stk - length rhs) stk of
                                                                              True -> [ParseStep Reduce (NTRule lhs rhs) (take (length stk - length rhs) stk ++ [NoBar lhs], inp)]
                                                                              False -> []
                                      ) rules
                                         
--BOTTOM-UP PARSER
-- Similar approach to FSA. We keep track of the current parse step and the history of parse steps. If the current configuration is the goal, 
-- we return the parsing history along with the current configuration. If the current configuration is not the goal, we find all possible next steps.
-- For each possible transition, for each possible next step in the transition, recursively call parserHelper on the output.

parser :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t         -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> [[ParseStep nt t]]  -- List of possible parses.

-- Parser function calls parserHelper
parser transitions rules startConfig goalConfig = 
  parserHelper transitions rules startConfig goalConfig ((ParseStep NoTransition NoRule startConfig),[])

--parserHelper takes in a parameter for the history
parserHelper :: (Eq nt, Eq t)
       => [[RewriteRule nt t] -> Config nt t -> [ParseStep nt t]]
          -- ^ List of transition steps. ^
       -> [RewriteRule nt t]  -- Rules from the CFG.
       -> Config nt t       -- Starting configuration.
       -> Config nt t         -- Goal configuration.
       -> (ParseStep nt t, [ParseStep nt t]) --current parse step and history of parse steps
       -> [[ParseStep nt t]]  -- List of possible parses.

parserHelper transitions rules currentConfig goalConfig (currentStep, history) = 
  case currentConfig == goalConfig of
    True -> [history++[currentStep]]
    False -> let nextSteps = concatMap (\f -> f rules currentConfig) transitions --list of all possible next steps from the current configuration
              in concatMap (\(ParseStep transition rule config) -> 
            parserHelper transitions rules config goalConfig (ParseStep transition rule config, history ++ [currentStep])) nextSteps



--MATCH
-- Applies to terminal rules. Similar to SHIFT, except we're removing the nonterminal instead of adding the nonterminal, and the nonterminal has to 
-- already be in the stack. Look at the top of the stack (i.e. the first element of the list) and see if it matches the first word of the input. 
-- This means iterating through the list of rules and checking if there is a terminal rule where the LHS == top of stack and RHS == first word of the input. 
-- If so, output a configuration where the stack has the top removed and the input has the first word removed.

match :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
match rules (stk, inp) = case null stk of
                          True -> [] --can't match any symbol of the stack to a word in the input if there is nothing on the stack
                          False -> case null inp of
                                    True -> [] --can't match any symbol of the stack to a word in the input if the input is null
                                    False -> concatMap (\r -> case r of
                                                          NTRule lhs rhs -> []
                                                          TRule lhs rhs -> case (NoBar lhs == (head stk) && rhs == head inp) of
                                                                              False -> []
                                                                              True -> [ParseStep Match (TRule lhs rhs) (tail stk, tail inp)]
                                              ) rules

--PREDICT
-- Applies to nonterminal rules. Look at the top of the stack, i.e. the first element. Iterate through the list of rules and if a rule is a 
-- nonterminal rule, check if the LHS of the rule == top of the stack. If so, output a configuration where the stack has the top element replaced 
-- with the RHS of the rule and the input is unchanged.

predict :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predict rules (stk, inp) = case null stk of
                            True -> [] --can't reduce anything if the stack is empty so return empty list
                            False -> concatMap (\r -> case r of
                                                  TRule lhs rhs -> []
                                                  NTRule lhs rhs -> case (NoBar lhs == head stk && length stk <= length inp) of
                                                                      False -> []
                                                                      True -> [ParseStep Predict (NTRule lhs rhs) ([NoBar i | i<-rhs] ++ tail stk, inp)]
                                                ) rules


--TOP-DOWN
topDown :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
topDown cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([NoBar start], input) in
  let goalConfig = ([], []) in
  parser [match, predict] rules startingConfig goalConfig


--MATCHLC
--Same as Match, except the top of the stack must be Bar
matchLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
matchLC rules (stk, inp) = 
    case null stk of
        True -> [] -- Can't match any symbol of the stack to a word in the input if there is nothing on the stack
        False -> case null inp of
            True -> [] -- Can't match any symbol of the stack to a word in the input if the input is null
            False -> case head stk of
                NoBar x -> []
                Bar x -> concatMap (\r -> case r of
                                NTRule lhs rhs -> []
                                TRule lhs rhs -> 
                                    case (lhs == x && rhs == head inp) of
                                        False -> []
                                        True -> [ParseStep Match (TRule lhs rhs) (tail stk, tail inp)]
                            ) rules


--SHIFTLC
-- Same as Shift, except we append to the beginning of the list rather than to the end.
shiftLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
shiftLC rules (stk, inp) = case null inp of
                            True -> []
                            False -> concatMap (\r -> case r of
                                            NTRule lhs rhs -> []
                                            TRule lhs rhs -> case rhs == head inp of
                                                                True -> [ParseStep Shift (TRule lhs rhs) ([NoBar lhs]++stk, tail inp)]
                                                                False -> []
                                          ) rules

-- Helper function to count the number of barred symbols on the stack
countBarred :: (Eq nt) => [Stack nt] -> Int
countBarred stk =
  case stk of
    [] -> 0
    x:rest -> case x of
                Bar y -> 1 + countBarred rest
                NoBar y -> 0 + countBarred rest

-- Helper function to count the number of unbarred symbols in the stack
countUnbarred :: (Eq nt) => [Stack nt] -> Int
countUnbarred stk =
  case stk of
    [] -> 0
    x:rest -> case x of
                NoBar y -> 1 + countBarred rest
                Bar y -> 0 + countBarred rest

-- PREDICTLC
-- Check that the stack is not empty and that the first symbol of the stack is not barred. Iterate through the list of rules. If a rule is nonterminal, 
-- check if the top of the stack == head of RHS. If so, replace the top of the stack with the tail of the RHS (barred) and the LHS (unbarred).
predictLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
predictLC rules (stk, inp) = 
    case null stk of
        True -> [] -- Can't reduce anything if the stack is empty so return empty list
        False -> case head stk of
            Bar x -> []
            NoBar x -> concatMap (\r -> case r of
                            TRule lhs rhs -> []
                            NTRule lhs rhs -> 
                                case (head rhs == x) of
                                    False -> []
                                    True -> case (countBarred stk <= length inp) && (countUnbarred stk <= length inp) of
                                        True -> [ParseStep Predict (NTRule lhs rhs) ([Bar i | i <- tail rhs] ++ [NoBar lhs] ++ tail stk, inp)]
                                        False -> []
                        ) rules



--CONNECTLC
-- Check that the stack is of length at least 2, the first element of the stack is not barred, and the second element is barred. Iterate through the 
-- list of rules. If a rule is nonterminal, check if the second element of the stack == LHS of the rule and the first element of the stack == head of RHS. 
-- If so, replace the first two elements of the stack with the tail of the RHS (barred).
connectLC :: (Eq nt, Eq t) => [RewriteRule nt t] -> Config nt t -> [ParseStep nt t]
connectLC rules (stk, inp) =
  case stk of
    [] -> [] --Stack cannot be empty
    stk1:[] -> [] --Stack cannot only have one element for the connectLC operation to be carried out
    stk1:stk2:rest -> case stk1 of
                      Bar x -> [] --First element of stack cannot be barred
                      NoBar x -> case stk2 of
                                    NoBar y -> [] --Second element of stack must be barred
                                    Bar y -> concatMap (\r -> case r of
                                                                TRule lhs rhs -> []
                                                                NTRule lhs rhs -> 
                                                                    case (lhs == y) && (x == head rhs) of
                                                                        False -> []
                                                                        True -> [ParseStep Connect (NTRule lhs rhs) ([Bar i | i <- tail rhs] ++ rest, inp)]
                                                            ) rules

--LEFT-CORNER
leftCorner :: (Eq nt, Eq t) => CFG nt t -> [t] -> [[ParseStep nt t]]
leftCorner cfg input =
  let (nts, ts, start, rules) = cfg in
  let startingConfig = ([Bar start], input) in
  let goalConfig = ([], []) in
  parser [shiftLC, predictLC, matchLC, connectLC] rules startingConfig goalConfig


-- TESTING (CFGs)
-- cfg5 :: CFG Cat String
-- cfg5 = ([S,NP,VP,PP,N,V,P,D,ORC,SRC,THAT,POSS,WHILE], 
--         ["adopted","had","Sam","that","cat","the", "petted","meowed", "Alex", "friend", "'s"], 
--         S,
--         [(NTRule S [NP,VP]), (NTRule S [WHILE,S,S]),
--          (NTRule NP [NP,POSS,N]), (NTRule NP [D,N,PP,SRC,ORC]), (NTRule NP [N,PP,SRC,ORC]),
--          (NTRule NP [D,N,SRC,ORC]), (NTRule NP [D,N,PP,SRC]), (NTRule NP [D,N,PP,ORC]),
--          (NTRule NP [D,N,PP]), (NTRule NP [D,N,SRC]), (NTRule NP [D,N,ORC]),
--          (NTRule NP [N,PP,SRC]), (NTRule NP [N,PP,ORC]), (NTRule NP [N,SRC,ORC]),
--          (NTRule NP [D,N]), (NTRule NP [N,PP]), (NTRule NP [N,SRC]), (NTRule NP [N,ORC]),
--          (NTRule VP [V,NP,PP]), (NTRule VP [V,NP]), (NTRule VP [V,PP]), (NTRule VP [V]),
--          (NTRule PP [P,NP]), (NTRule SRC [THAT,VP]), (NTRule ORC [NP,VP]), (NTRule VP [V,VP]),
--         (TRule  N "cat"), (TRule V "petted"), (TRule NP "Sam"), (TRule D "the"), (TRule V "meowed"),
--          (TRule NP "Alex"), (TRule V "adopted"), (TRule V "had"), (TRule N "friend"),
--          (TRule THAT "that"), (TRule POSS "'s")
--         ]
--        )

	-- • "Alex petted the cat Sam adopted"
	-- • "Alex petted the cat that Sam had adopted"
	-- • "The cat Sam adopted meowed"
	-- • "Alex 's cat meowed"
	-- • "Alex 's friend 's cat meowed"


-- cfg7 :: CFG Cat String
-- cfg7 = ([S,NP,VP,PP,N,V,P,D,ORC,SRC,THAT,POSS,WHILE], 
--         ["Alessandro","Maria","vede","cammina","gatta","la", "il","arancione", "che", "da", "a", "di", "un", "amico"], 
--         S,
--         [(NTRule S [NP,VP]), (NTRule S [WHILE,S,S]),
--          (NTRule NP [NP,POSS,N]), (NTRule NP [D,N,PP,SRC,ORC]), (NTRule NP [N,PP,SRC,ORC]),
--          (NTRule NP [D,N,SRC,ORC]), (NTRule NP [D,N,PP,SRC]), (NTRule NP [D,N,PP,ORC]),
--          (NTRule NP [D,N,PP]), (NTRule NP [D,N,SRC]), (NTRule NP [D,N,ORC]),
--          (NTRule NP [N,PP,SRC]), (NTRule NP [N,PP,ORC]), (NTRule NP [N,SRC,ORC]),
--          (NTRule NP [D,N]), (NTRule NP [N,PP]), (NTRule NP [N,SRC]), (NTRule NP [N,ORC]),
--         (NTRule VP [V,PP]), (NTRule VP [V]),
--          (NTRule PP [P,NP]), (NTRule SRC [THAT,VP]), (NTRule ORC [NP,VP]), (NTRule VP [V,VP]), (NTRule VP [NP, VP]),
--          (NTRule VP [V, PP]), (NTRule NP [NP,A]), (NTRule VP [V, NP]), (NTRule VP [V, NP, PP]),
--          (TRule NP "Alessandro"), (TRule NP "Maria"), (TRule V "vede"),
--          (TRule V "cammina"), (TRule NP "la"), (TRule D "la"), (TRule A "arancione"), (TRule N "gatta"), (TRule D "il"), (TRule THAT "che"), (TRule V "da"),
--          (TRule P "a"), (TRule P "di"), (TRule D "un"), (TRule N "amico")
--         ]
--        )

	-- • "Alessandro vede Maria"
	-- • "Alessandro la vede"
	-- • "Alessandro vede la gatta arancione"
	-- • "la gatta arancione cammina"
	-- • "la gatta Maria vede cammina"
	-- • "Alessandro da la gatta a Maria"
	-- • "Alessandro la da la gatta"
	-- • "la gatta di Alessandro cammina"
	-- • "la gatta di un amico di Alessandro cammina"
	-- • "Maria vede la gatta che cammina"


-- cfg6 :: CFG Cat String
-- cfg6 = ([S,NP,VP,PP,N,V,P,D,ORC,SRC,THAT,POSS,WHILE], 
--         ["baby","boy","actor","spouse","boss","award", "Mary","John","met","saw","won","the","on","in","with","that","'s","while", "watched", "cried"], 
--         S,
--         [(NTRule S [NP,VP]), (NTRule S [WHILE,S,S]),
--          (NTRule NP [NP,POSS,N]), (NTRule NP [D,N,PP,SRC,ORC]), (NTRule NP [N,PP,SRC,ORC]),
--          (NTRule NP [D,N,SRC,ORC]), (NTRule NP [D,N,PP,SRC]), (NTRule NP [D,N,PP,ORC]),
--          (NTRule NP [D,N,PP]), (NTRule NP [D,N,SRC]), (NTRule NP [D,N,ORC]),
--          (NTRule NP [N,PP,SRC]), (NTRule NP [N,PP,ORC]), (NTRule NP [N,SRC,ORC]),
--          (NTRule NP [D,N]), (NTRule NP [N,PP]), (NTRule NP [N,SRC]), (NTRule NP [N,ORC]),
--          (NTRule VP [V,NP,PP]), (NTRule VP [V,NP]), (NTRule VP [V,PP]), (NTRule VP [V]),
--          (NTRule PP [P,NP]), (NTRule SRC [THAT,VP]), (NTRule ORC [NP,V]),
--          (TRule N "baby"), (TRule N "boy"), (TRule N "actor"), (TRule N "spouse"), (TRule N "boss"), (TRule N "award"),
--          (TRule NP "Mary"), (TRule NP "John"),
--          (TRule V "met"), (TRule V "saw"), (TRule V "won"), (TRule V "cried"), (TRule V "watched"),
--          (TRule D "the"), (TRule P "on"), (TRule P "in"), (TRule P "with"),
--          (TRule THAT "that"), (TRule POSS "'s"), (TRule WHILE "while")
--         ]
--        )

-- "while John watched the baby that won cried"

-- TESTING SENTENCES (FOR ALL PARSING METHODS)
		-- ○ bottomUp cfg5 (words "while John watched the baby that won cried")
		-- ○ bottomUp cfg4 (words "the baby saw the boy")
		-- ○ bottomUp cfg4 (words "Mary 's baby won")
		-- ○ bottomUp cfg4 (words "Mary 's boss 's baby won")
		-- ○ bottomUp cfg4 (words "John met the boy that saw the actor")
		-- ○ bottomUp cfg4 (words "the actor the boy met won")
		-- ○ bottomUp cfg4 (words "the actor the boy the baby saw met won")
    -- words "watches spies with telescopes"
  	-- ○ topDown cfg4 (words "Mary 's boss 's baby won the award")
		-- ○ topDown cfg4 (words "Mary 's boss 's baby won the prize")
		-- ○ topDown cfg4 (words "John said hi to Mary")
    -- ○ topDown cfg4 (words "John met Mary")


-- TESTING (SHIFT)
		-- ○ shift [(TRule NP "John")] ([], ["Mary"]) 
		-- ○ shift [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]), (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([], ["watches"])
		-- ○ shift [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]), (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([], ["spies"])
		-- ○ shift [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]), (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([], ["watches", "spies", "with", "telescopes"])
		-- ○ shift [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]), (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([NoBar VP], ["spies","with","telescopes"])
		-- ○ shift [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]), (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")]  ([NoBar NP],["spies","with","telescopes"])
		-- ○ shift [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]), (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")]  ([NoBar NP],[])
		-- ○ shift [(TRule NP "Mary"), (TRule POSS "'s")] ([], ["Mary", "'s"])
	
-- TESTING (REDUCE)
-- Reduce [(NTRule S [NP,VP])] ([NoBar NP, NoBar VP], [""])
-- 		○ reduce [(NTRule S [NP,VP])] ([NoBar NP, NoBar VP], [])
-- 		○ reduce [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]),  (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([NoBar V, NoBar NP], ["with", "telescopes"])
-- 		○ reduce [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]),  (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([NoBar VP, NoBar P, NoBar NP], [])
-- 		○ reduce [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]),  (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([NoBar VP, NoBar N, NoBar NP], [])
-- 		○ reduce [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]),  (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([NoBar VP, NoBar PP], [])
-- 		○ reduce [(NTRule VP [V,NP]), (NTRule NP [NP,PP]), (NTRule PP [P,NP]), (NTRule VP [VP,PP]),  (TRule NP "telescopes"), (TRule VP "watches"), (TRule NP "watches"), (TRule P "with"), (TRule VP "spies"), (TRule NP "spies"), (TRule V "watches")] ([NoBar VP], [])
-- 		○ reduce [(NTRule S [NP,VP]), (NTRule S [WHILE,S,S]), (NTRule NP [NP,POSS,N]), (NTRule NP [D,N,PP,SRC,ORC]), (NTRule NP [N,PP,SRC,ORC]), (NTRule NP [D,N,SRC,ORC]), (NTRule NP [D,N,PP,SRC]), (NTRule NP [D,N,PP,ORC]), (NTRule NP [D,N,PP]), (NTRule NP [D,N,SRC]), (NTRule NP [D,N,ORC]), (NTRule NP [N,PP,SRC]), (NTRule NP [N,PP,ORC]), (NTRule NP [N,SRC,ORC]), (NTRule NP [D,N]), (NTRule NP [N,PP]), (NTRule NP [N,SRC]), (NTRule NP [N,ORC]), (NTRule VP [V,NP,PP]), (NTRule VP [V,NP]), (NTRule VP [V,PP]), (NTRule VP [V]), (NTRule PP [P,NP]), (NTRule SRC [THAT,VP]), (NTRule ORC [NP,V]), (TRule N "baby"), (TRule N "boy"), (TRule N "actor"), (TRule N "spouse"), (TRule N "boss"), (TRule N "award"), (TRule NP "Mary"), (TRule NP "John"), (TRule V "met"), (TRule V "saw"), (TRule V "won"), (TRule D "the"), (TRule P "on"), (TRule P "in"), (TRule P "with"), (TRule THAT "that"), (TRule POSS "'s"), (TRule WHILE "while")] ([NoBar V], [])
	
-- TESTING (PREDICT)
		-- ○ predict [(NTRule S [NP,VP])] ([], [])
		-- ○ predict [(NTRule S [NP,VP])] ([], words "watches spies with telescopes")
		-- ○ predict [(NTRule NP [D,N])] ([NoBar S], words "watches spies with telescopes")
		-- ○ predict [(NTRule S [NP,VP])] ([NoBar S], words "the baby saw the boy")
		-- ○ predict [(NTRule S [NP,VP]), (NTRule NP [D,N])] ([NoBar NP, NoBar VP],["the","baby","saw","the","boy"])
		-- ○ predict [(NTRule S [NP,VP]), (NTRule NP [D,N]), (NTRule VP [V,NP])] ([NoBar VP],["saw","the","boy"])

-- TESTING (MATCH)
		-- ○ match [(TRule NP "John")] ([], ["Mary"]) 
		-- ○ match [(TRule NP "John")] ([NoBar NP], ["Mary"]) 
		-- ○ match [(TRule NP "John"), (TRule NP "Mary")] ([NoBar NP], ["Mary"]) 
		-- ○ match [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([NoBar D, NoBar N, NoBar VP], words "the baby saw the boy") 
		-- ○ match [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([NoBar N, NoBar VP], ["baby","saw","the","boy"])
		-- ○ match [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([NoBar V, NoBar NP], ["saw","the","boy"])

-- TESTING (MATCHLC)
		-- ○ matchLC [(TRule NP "John")] ([], ["Mary"])
		-- ○ matchLC [(TRule NP "John")] ([NoBar NP], ["Mary"])
		-- ○ matchLC [(TRule NP "John"), (TRule NP "Mary")] ([NoBar NP], ["Mary"]) 
		-- ○ matchLC [(TRule NP "John"), (TRule NP "Mary")] ([Bar NP], ["Mary"]) 
		-- ○ matchLC [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([Bar N, NoBar NP, Bar S], words "baby saw the boy") 
		-- ○ matchLC [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([NoBar N, NoBar NP, Bar S], words "baby saw the boy")

-- TESTING (SHIFTLC)
		-- ○ matchLC [(TRule NP "John")] ([], ["Mary"])
		-- ○ matchLC [(TRule NP "John")] ([NoBar NP], ["Mary"])
		-- ○ matchLC [(TRule NP "John"), (TRule NP "Mary")] ([NoBar NP], ["Mary"]) 
		-- ○ matchLC [(TRule NP "John"), (TRule NP "Mary")] ([Bar NP], ["Mary"]) 
		-- ○ matchLC [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([Bar N, NoBar NP, Bar S], words "baby saw the boy") 
		-- ○ matchLC [(TRule NP "John"), (TRule D "the"), (TRule N "baby"), (TRule V "saw")] ([NoBar N, NoBar NP, Bar S], words "baby saw the boy") 

-- TESTING (PREDICTLC)
		-- ○ predictLC [(NTRule S [NP,VP])] ([], [])
		-- ○ predictLC [(NTRule S [NP,VP])] ([], words "watches spies with telescopes")
		-- ○ predictLC [(NTRule NP [D,N])] ([Bar NP], words "watches spies with telescopes")
		-- ○ predictLC [(NTRule S [NP,VP])] ([Bar S], words "the baby saw the boy")
		-- ○ predictLC [(NTRule S [NP,VP]), (NTRule NP [D,N])] ([NoBar D, Bar S],["baby","saw","the","boy"])

-- TESTING (CONNECTLC)
		-- ○ connectLC [(TRule NP "John")] ([], ["Mary"]) 
		-- ○ connectLC [(NTRule NP [D,N])] ([Bar NP], words "watches spies with telescopes")
		-- ○ connectLC [(NTRule NP [D,N])] ([NoBar NP], words "watches spies with telescopes")
		-- ○ connectLC [(NTRule NP [D,N])] ([NoBar D], words "watches spies with telescopes")
		-- ○ connectLC [(NTRule NP [D,N])] ([Bar D], words "watches spies with telescopes")
		-- ○ connectLC [(NTRule S [NP,VP]), (NTRule NP [D,N])] ([NoBar NP, Bar S],["saw","the","boy"])
		-- ○ connectLC [(NTRule S [NP,VP]), (NTRule NP [D,N]), (NTRule VP [V,NP])] ([NoBar V, Bar VP],["the","boy"])
		-- ○ connectLC [(NTRule S [NP,VP]), (NTRule NP [D,N]), (NTRule VP [V,NP])] ([NoBar D, Bar NP],["boy"])
		-- ○ connectLC [(NTRule S [NP,VP]), (NTRule NP [D,N]), (NTRule VP [V,NP]), (NTRule VP [V])] ([NoBar V, Bar VP],[])


