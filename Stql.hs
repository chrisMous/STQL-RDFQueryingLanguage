{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module Main where

import CourseworkHappy (
    FileCollection (Union, Filename, Intersection, Disjoint),
    Inputs (Inputs, Input),
    MathExp (MathExpInt, Negate, Div, Times, Sub, Add, MathExpVar),
    Var (Element, Collection),
    BoolExp (Not, Or, And, BoolExpBool, BoolExpVar, Contains, LessThan, GreaterThan, Equal),
    Comparable (CompString, CompBool, CompInt, CompVar),
    Cases (Cases, Case, ShortCase, ShortCases),
    Inserts (TripleToInsert, Triples),
    Triple (Triple, TripleVar),
    SubjectOption (SubjectVar, SubjectString),
    PredicateOption (PredVar, PredString),
    ObjectOption (ObURL, ObVar, ObString, ObBool, ObMathExp),
    Prog (Program1, Program2), parseCalc)
import Data.List.Split ( splitOn )
import Data.List ( isPrefixOf, stripPrefix, isInfixOf, union, (\\), intersect, isSuffixOf, group, sort, intercalate )
import Data.Maybe (fromJust, isNothing)
import System.Directory.Internal.Prelude( IOMode(ReadMode), getArgs )
import System.IO
import Data.Char (isSpace, isDigit)
import Text.Read (readMaybe)
import GHC.Data.Maybe (isJust)
import CourseworkAlex (alexScanTokens)

data Environment = Env [Variable]
    deriving Show

data Variable = Variable String [Subject] [Predicate] [Object] Int
    deriving Show
data Subject = Subject String
    deriving (Eq, Show)
data Predicate = Predicate String
    deriving (Eq, Show)
data Object =   URL String |
                Lit String |
                Int Int    |
                Bool Bool
    deriving (Eq, Show)



-- main function, runs the interpreter
main :: IO()
main = do
    filename <- getArgs
    handle <- openFile (head filename) ReadMode
    contents <- hGetContents handle
    let tokens = alexScanTokens contents
    let program = parseCalc tokens
    outputs <- interpret program
    -- checkValidity (head filename)
    let formatting = map replaceTF (appendList outputs)
    fname <- extractOutputFilename (head filename)
    putStr (unlines formatting)
    writeFile fname (unlines formatting)



{- | interpret function ties together all aspects of the interpreter, it builds the environment, checks the cases and inserts the triples to the output
    - Prog: program                 The program syntax tree
-}
interpret :: Prog -> IO [String]
interpret (Program1 inputs cases output) = do
    env <- buildEnvironment inputs
    let triples = removeDuplicates $ mainLoop1 [] cases env
    return triples
interpret (Program2 inputs output) = do
    env <- buildEnvironment inputs
    let triples = removeDuplicates $ mainLoop2 [] env
    return triples



{- | mainLoop1 interprets the program in the case that there are cases to check against
    - [String]: outputs             The recursively built list of output triples
    - Cases: cases                  The list of cases to check against
    - Environment: env              The environment to lookup variables in
-}
mainLoop1 :: [String] -> Cases -> Environment -> [String]
mainLoop1 outputs cases (Env []) = outputs
mainLoop1 outputs cases env = mainLoop1 (outputs ++ evaluateCases [] cases env) cases (iterateEnv env)



{- | mainLoop2 interprets the program in the case that there are no cases to check against, simply inserts all triples from the input to the output
    - [String]: outputs             The recursively built list of output triples
    - Environment: env              The environment to lookup variables in
-}
mainLoop2 :: [String] -> Environment -> [String]
mainLoop2 outputs (Env []) = outputs
mainLoop2 outputs env = mainLoop2 (outputs ++ getInserts [] env) (iterateEnv env)



{- | evaluateCases will loop through each case in the current step of computation and add to the list of outputs based on the boolean expression
    - [String]: outputs             The list of outputs so far
    - Cases: cases                  The different cases to check for
    - Environment: env              The environment to lookup variables in
-}
evaluateCases :: [String] -> Cases -> Environment -> [String]
evaluateCases outputs (Case inserts exp) env
    | evaluateBoolExp exp env == Just True = outputs ++ evaluateInserts [] inserts env
    | otherwise = outputs
evaluateCases outputs (Cases inserts exp cases) env
    | evaluateBoolExp exp env == Just True = evaluateCases (outputs ++ evaluateInserts [] inserts env) cases env
    | otherwise = evaluateCases outputs cases env
evaluateCases outputs (ShortCase exp) env
    | evaluateBoolExp exp env == Just True = outputs ++ getInserts [] env
    | otherwise = outputs
evaluateCases outputs (ShortCases exp cases) env
    | evaluateBoolExp exp env == Just True = evaluateCases (outputs ++ getInserts [] env) cases env
    | otherwise = evaluateCases outputs cases env



{- | evaluateInserts will take in the list of inserts and construct a string output from it
    - [String]: outputs             The list of outputs so far (recursively builds)
    - Inserts: inserts              The list of inserts to build from
    - Environment: env              The environment to build from
-}
evaluateInserts :: [String] -> Inserts -> Environment -> [String]
evaluateInserts outputs (TripleToInsert t) env
    | isJust result = outputs ++ [fromJust result]
    | otherwise = outputs
    where
        result = handleTriple t env
evaluateInserts outputs (Triples t ts) env
    | isJust result = evaluateInserts (outputs ++ [fromJust result]) ts env
    | otherwise = evaluateInserts outputs ts env
    where
        result = handleTriple t env



{- | handleTriple will take in a triple and build a single insert out of it
    - Triple: triple                The triple to construct
    - Environment: env              The environment to build variables from
-}
handleTriple :: Triple -> Environment -> Maybe String
handleTriple (TripleVar s) env = Just (getInsert s env)
handleTriple (Triple sub pred ob) env
    | isJust (fromObj ob env) && isJust (fromPred pred env) && isJust (fromSub sub env) = Just (fromJust (fromSub sub env) ++ " " ++ fromJust (fromPred pred env) ++ " " ++ fromJust (fromObj ob env))



{- | fromSub will convert a subject option into a string to be outputted, in the case that the subject cannot be evaluated, it returns Nothing
    - SubjectOption: sub            The subject option to generate
    - Environment: env              The environment to lookup variables in
-}
fromSub :: SubjectOption -> Environment -> Maybe String
fromSub (SubjectString s) env = Just $ "<" ++ s ++ ">"
fromSub (SubjectVar (Element n "subject")) env = Just (fromSubject $ getSubject n env)
fromSub (SubjectVar (Element n "pred")) env = Just (fromPredicate $ getPred n env)
fromSub (SubjectVar (Element n "object")) env
    | isValid ob = Just (fromObject ob)
    | otherwise = Nothing
    where
        ob = getObj n env
        isValid (URL s) = True
        isValid _ = False
fromSub _ _ = error "Invalid subject option"



{- | fromPred will convert a predicate option into a string to be outputted, in the case that the predicate cannot be evaluated, it returns nothing
    - PredicateOption: pred         The predicate option to generated
    - Environment: env              The environment to lookup variables in
-}
fromPred :: PredicateOption -> Environment -> Maybe String
fromPred (PredString s) env = Just $ "<" ++ s ++ ">"
fromPred (PredVar (Element n "subject")) env = Just (fromSubject $ getSubject n env)
fromPred (PredVar (Element n "pred")) env = Just (fromPredicate $ getPred n env)
fromPred (PredVar (Element n "object")) env
    | isValid ob = Just (fromObject ob)
    | otherwise = Nothing
    where
        ob = getObj n env
        isValid (URL s) = True
        isValid _ = False
fromPred _ _ = error "Invalid predciate option"



{- | fromObj will convert an object option into a string to be outputted, in the case that the predicate cannot be evaluated, it returns nothing
    - ObjectOption: ob              The object option to be generated
    - Environment: env              The environment to lookup variables in
-}
fromObj :: ObjectOption -> Environment ->  Maybe String
fromObj (ObURL s) env = Just $ "<" ++ s ++ ">"
fromObj (ObString s) env = Just s
fromObj (ObBool b) env = Just $ show b
fromObj (ObMathExp e) env
    | isJust $ evaluateMathExp e env = Just $ show $ fromJust $ evaluateMathExp e env
    | otherwise = Nothing
fromObj (ObVar (Element n "subject")) env = Just $ fromSubject $ getSubject n env
fromObj (ObVar (Element n "pred")) env = Just $ fromPredicate $ getPred n env
fromObj (ObVar (Element n "object")) env = Just $ fromObject $ getObj n env
fromObj (ObVar _) _ = error "Invalid Object option"



{- | fromSubject converts a subject variable type to a string for outputting
    - Subject: subject              The subject to convert
-}
fromSubject :: Subject -> String
fromSubject (Subject s) = "<" ++ s ++ ">"



{- | fromPredicate will convert a predicate to a string for outputting
    - Predicate: pred               The predicate to convert
-}
fromPredicate :: Predicate -> String
fromPredicate (Predicate s) = "<" ++ s ++ ">"



{- | fromObject will convert an object data type to a string for outputting#
    - Object: ob                    The object to convert
-}
fromObject :: Object -> String
fromObject (URL s) = "<" ++ s ++ ">"
fromObject (Lit s) = s
fromObject (Int i) = show i
fromObject (Bool b) = show b



{- | getInserts will build a list of inserts from the environment, by iterating through all variables and getting their current inserts
    - [String]: inserts             The inserts so far
    - Environment: env              The environment to loop through
-}
getInserts :: [String] -> Environment -> [String]
getInserts inserts (Env []) = inserts
getInserts inserts (Env (v:vs)) = getInserts (inserts ++ [getCurrentInsert v]) (Env vs)



{- | getInsert will take the name of a variable and return the current insert for that variable
    - String: name                  The name of the variable
    - Environment: env              The environment to search
-}
getInsert :: String -> Environment -> String
getInsert name (Env []) = error "Invalid variable name"
getInsert name1 (Env (v@(Variable name2 _ _ _ _):vs))
    | name1 == name2 = getCurrentInsert v
    | otherwise = getInsert name1 (Env vs)



{- | getCurrentInsert will take a variable and return the current insert for that variable
    - Variable: v                   The variable to get the insert from
-}
getCurrentInsert :: Variable -> String
getCurrentInsert (Variable _ ((Subject s):ss) ((Predicate p):ps) (o:os) 0) = "<" ++ s ++ "> <" ++ p ++ "> " ++ fromObject o
getCurrentInsert (Variable n (s:ss) (p:ps) (o:os) i) = getCurrentInsert (Variable n ss ps os (i-1))



{-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-}
{-    Boolean Expression evaluation    -}
{-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-}



{- | evaluateBoolExp will evaluate a boolean expression
    - BoolExp e                     The boolean expression to evaluate
    - Environment: env              The environment to retreive values from
-}
evaluateBoolExp :: BoolExp -> Environment -> Maybe Bool
evaluateBoolExp (BoolExpBool b) env = Just b
evaluateBoolExp (BoolExpVar (Element n t)) env
    | t == "object" = getBool $ getObj n env
    | otherwise = error "Invalid type Comparison"
    where
        getBool (Bool b) = Just b
        getBool _ = Nothing
evaluateBoolExp (Equal          (Collection _ _) _) _   = error "Invalid type Comparison"
evaluateBoolExp (Equal v comp)       env                = equal (varToComp v env) comp env

evaluateBoolExp (GreaterThan    (Collection _ _) _) _   = error "Invalid type Comparison"
evaluateBoolExp (GreaterThan v comp) env                = greaterThan (varToComp v env) comp env

evaluateBoolExp (LessThan       (Collection _ _) _) _   = error "Invalid type Comparison"
evaluateBoolExp (LessThan v comp)    env                = lessThan (varToComp v env) comp env

evaluateBoolExp (Contains       (Element _ _) _) _      = error "Invalid type Comparison"
evaluateBoolExp (Contains       (Collection n "subjects") comp) env = subContains (getSubjects n env) comp env
evaluateBoolExp (Contains       (Collection n "preds") comp) env = predContains (getPreds n env) comp env
evaluateBoolExp (Contains       (Collection n "objects") comp) env = objContains (getObjs n env) comp env
evaluateBoolExp (And e1 e2) env = do
    v1 <- evaluateBoolExp e1 env
    v2 <- evaluateBoolExp e2 env
    Just (v1 && v2)
evaluateBoolExp (Or e1 e2) env = do
    v1 <- evaluateBoolExp e1 env
    v2 <- evaluateBoolExp e2 env
    Just (v1 || v2)
evaluateBoolExp (Not e1) env = do
    v1 <- evaluateBoolExp e1 env
    Just (not v1)



{- | varToComp will convert a variable to a form which easier to compare with other values
    - Var: v                        The variable to convert
    - Environment: env              The environment to lookup the variable in
-}
varToComp :: Var -> Environment -> Comparable
varToComp (Element n "subject") env = extractFromSubject $ getSubject n env
    where
        extractFromSubject (Subject s) = CompString s
varToComp (Element n "pred") env    = extractFromPredicate (getPred n env)
    where
        extractFromPredicate (Predicate s) = CompString s
varToComp (Element n "object") env = extractFromObject (getObj n env)
    where
        extractFromObject (URL s) = CompString s
        extractFromObject (Lit s) = CompString s
        extractFromObject (Int s) = CompInt s
        extractFromObject (Bool s) = CompBool s



{- | objToComp will convert an object to it's corresponding comparable
    - Object: ob                    The object that needs to be compared to something
-}
objToComp :: Object -> Comparable
objToComp (URL s) = CompString s
objToComp (Lit s) = CompString s
objToComp (Int i) = CompInt i
objToComp (Bool b) = CompBool b



{- | equal will take in 2 comparables and compare the two of them, returning True if they are equal, 
    false if they are not, 
    or Nothing if they are incompatible data types
    - Comparable: c1                The first comparable
    - Comparable: c2                The second comparable
    - Environment: env              The environment to lookup any variables in
-}
equal :: Comparable -> Comparable -> Environment -> Maybe Bool
equal (CompInt i1) (CompString s2) env
    | s2 == "#URL" = Just False
    | s2 == "#Int" = Just True
    | s2 == "#Bool" = Just False
    | s2 == "#String" = Just False
    | otherwise = Nothing
equal (CompBool b1) (CompString s2) env
    | s2 == "#URL" = Just False
    | s2 == "#Int" = Just False
    | s2 == "#Bool" = Just True
    | s2 == "#String" = Just False
    | otherwise = Nothing
equal (CompVar v) c2 env = equal (varToComp v env) c2 env
equal c1 (CompVar v) env = equal c1 (varToComp v env) env
equal (CompString s1) (CompString s2) _ 
    | s2 == "#URL" && ("http" `isPrefixOf` s1) = Just True
    | s2 == "#String" = Just True
    | otherwise = Just (s1 == s2)
equal (CompInt i1) (CompInt i2) _ = Just (i1 == i2)
equal (CompBool b1) (CompBool b2) _ = Just (b1 == b2)
equal _ _ _ = Nothing



{- | greaterThan will compare 2 comparables and return True/False if c1 > c2, or Nothing if they are invalid data types
    - Comparable: c1                The first comparable
    - Comparable: c2                The second comparable
    - Environment: env              The environment to lookup variables in
-}
greaterThan :: Comparable -> Comparable -> Environment -> Maybe Bool
greaterThan (CompVar v) c2 env = greaterThan (varToComp v env) c2 env
greaterThan c1 (CompVar v) env = greaterThan c1 (varToComp v env) env
greaterThan (CompInt i1) (CompInt i2) _ = Just (i1 > i2)
greaterThan _ _ _ = Nothing



{- | lessThan will compare 2 comparables and return True/False if c1 < c2, or Nothing if they are invalid data types
    - Comparable: c1                The first comparable
    - Comparable: c2                The second comparable
    - Environment: env              The environment to lookup variables in
-}
lessThan :: Comparable -> Comparable -> Environment -> Maybe Bool
lessThan (CompVar v) c2 env = greaterThan (varToComp v env) c2 env
lessThan c1 (CompVar v) env = greaterThan c1 (varToComp v env) env
lessThan (CompInt i1) (CompInt i2) _ = Just (i1 < i2)
lessThan _ _ _ = Nothing



{- | subContains will see if a list of subjects contains a specific string
    - [Subject]: xs                 The list of subjects to search
    - Comparable: c                 The comparable to search for
    - Environment: env              The environment to lookup variables in    
-}
subContains :: [Subject] -> Comparable -> Environment -> Maybe Bool
subContains [] c env                            = Just False
subContains xs (CompVar v) env                  = subContains xs (varToComp v env) env
subContains ((Subject x):xs) (CompString s) env
    | x == s                                    = Just True
    | otherwise                                 = subContains xs (CompString s) env
subContains _ _ _                               = Nothing



{- | predContains will see if a list of predicates contains a specific string
    - [Predicate]: xs               The list of predicates to search
    - Comparable: c                 The comparable to search for
    - Environment: env              The environment to lookup variables in    
-}
predContains :: [Predicate] -> Comparable -> Environment-> Maybe Bool
predContains [] c env                           = Just False
predContains ps (CompVar v) env                 = predContains ps (varToComp v env) env
predContains ((Predicate x):ps) (CompString s) env
    | x == s                                    = Just True
    | otherwise                                 = predContains ps (CompString s) env
predContains _ _ _                              = Nothing



{- | objContains will see if a list of objects contains a specific comparable
    - [Object]: xs                  The list of objects to search
    - Comparable: c                 The comparable to search for
    - Environment: env              The environment to lookup variables in    
-}
objContains :: [Object] -> Comparable -> Environment -> Maybe Bool
objContains [] _ _                              = Just False
objContains os (CompVar v) env                  = objContains os (varToComp v env) env
objContains (o:os) c env
    | equal (objToComp o) c env == Just True    = Just True
    | otherwise                                 = objContains os c env



{-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-}
{-     Math Expression evaluation      -}
{-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-}



{- | evaluateMathExp will evaluate a maths expression
    - MathExp: e                    The expression to evaluate
    - Environment: env              The environment to retreive variables from
-}
evaluateMathExp :: MathExp -> Environment -> Maybe Int
evaluateMathExp (Negate e) env = do
    x <- evaluateMathExp e env
    Just (negate x)
evaluateMathExp (Div e1 e2) env = do
    x <- evaluateMathExp e1 env
    y <- evaluateMathExp e2 env
    Just (x `div` y)
evaluateMathExp (Times e1 e2) env = do
    x <- evaluateMathExp e1 env
    y <- evaluateMathExp e2 env
    Just (x * y)
evaluateMathExp (Sub e1 e2) env = do
    x <- evaluateMathExp e1 env
    y <- evaluateMathExp e2 env
    Just (x - y)
evaluateMathExp (Add e1 e2) env = do
    x <- evaluateMathExp e1 env
    y <- evaluateMathExp e2 env
    Just (x + y)
evaluateMathExp (MathExpInt n) env = Just n
evaluateMathExp (MathExpVar (Element n t)) env
    | t == "object" = getInt $ getObj n env
    | otherwise = error "Arithmetic Operation on Invalid type"
    where
        getInt (Int n) = Just n
        getInt _ = Nothing



{-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-}
{-      Environment Functionality      -}
{-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-}



{- | iterateEnv will progress the environment to it's next phase by incrementing various variable indexes by one
     one the environment has reached it's final phase, it will the increment to the empty list
    - Environment env               The environment to increment     
-}
iterateEnv :: Environment -> Environment
iterateEnv (Env []) = Env []
iterateEnv (Env (v:vs))
    | all isFinal (v:vs) = Env []
    | isFinal v = add (increment v) (iterateEnv (Env vs))
    | otherwise = add (increment v) (Env vs)
    where
        add :: Variable -> Environment -> Environment
        add x (Env xs) = Env (x : xs)
        increment :: Variable -> Variable
        increment (Variable name subs preds obs index) = Variable name subs preds obs ((index + 1) `mod` length subs)
        isFinal :: Variable -> Bool
        isFinal var@(Variable _ xs _ _ i) = i == length xs -1



{- | gets the current subject for a variable
    - String: varName               The name of the variable to search
    - Environment: e                The environment the variable should be in
-}
getSubject :: String -> Environment -> Subject
getSubject _ (Env []) = error "Variable doesn't exist"
getSubject varName (Env ((Variable name subs _ _ index):vs))
    | varName == name = findIndex subs index
    | otherwise = getSubject varName (Env vs)



{- | gets the current predicate for a variable
    - String: varName               The name of the variable to search
    - Environment: e                The environment the variable should be in
-}
getPred :: String -> Environment -> Predicate
getPred _ (Env []) = error "Variable doesn't exist"
getPred varName (Env ((Variable name _ preds _ index):vs))
    | varName == name = findIndex preds index
    | otherwise = getPred varName (Env vs)



{- | gets the current object for a variable
    - String: varName               The name of the variable to search
    - Environment: e                The environment the variable should be in
-}
getObj :: String -> Environment -> Object
getObj _ (Env []) = error "Variable doesn't exist"
getObj varName (Env ((Variable name _ _ obs index):vs))
    | varName == name = findIndex obs index
    | otherwise = getObj varName (Env vs)



{- | getSubjects will return the list of subjects stored in a given variable
    - String: varName               The name of the variable
    - Environment: env              The environment the variable should be in
-}
getSubjects :: String -> Environment -> [Subject]
getSubjects _ (Env []) = error "Variable doesn't exist"
getSubjects varName (Env ((Variable name subs _ _ _):vs))
    | varName == name = subs
    | otherwise = getSubjects varName (Env vs)



{- | getPreds will return the list of predicates stored in a given variable
    - String: varName               The name of the variable
    - Environment: env              The environment the variable should be in
-}
getPreds :: String -> Environment -> [Predicate]
getPreds _ (Env []) = error "Variable doesn't exist"
getPreds varName (Env ((Variable name _ preds _ _):vs))
    | varName == name = preds
    | otherwise = getPreds varName (Env vs)



{- | getObjs will return the list of objects stored in a given variable
- String: varName               The name of the variable
- Environment: env              The environment the variable should be in
-}
getObjs :: String -> Environment -> [Object]
getObjs _ (Env []) = error "Variable doesn't exist"
getObjs varName (Env ((Variable name _ _ obs _):vs))
    | varName == name = obs
    | otherwise = getObjs varName (Env vs)



{- | finds the value in a list at a given index
    - [a]: xs                       The list to search
    - Int: index                    The index of the element to find
-}
findIndex :: [a] -> Int -> a
findIndex [] _ = error "Index out of range"
findIndex (x:xs) 0 = x
findIndex (x:xs) n = findIndex xs (n-1)



{- | buildEnvironment will take the inputs part of the abstract syntax tree and build a complete environment out of it
    - Inputs: inputs                An AST describing the desired environment
-}
buildEnvironment :: Inputs -> IO Environment
buildEnvironment inputs = do
        vars <- makeEnv inputs
        return (Env vars)
    where
        makeEnv :: Inputs -> IO [Variable]
        makeEnv (Input fc name) = do
            triples <- buildFileCollection fc
            return [buildVariable name triples]
        makeEnv (Inputs fc name inputs) = do
            triples <- buildFileCollection fc
            nextVar <- makeEnv inputs
            return (buildVariable name triples : nextVar)



{- | buildVariable will construct an entire variable given a list of correctly formatted triple
    - String: name                  The name of the variable
    - [String]: triples             The triples to put into the variable
-}
buildVariable :: String -> [String] -> Variable
buildVariable name triples = Variable name getSubs getPreds getObs 0
    where
        getSubs = map (Subject . getIndex 0) triples'
        getPreds = map (Predicate . getIndex 1) triples'
        getObs = map (chooseType . getIndex 2) triples'
        triples' = map break triples
        break triple = map (remove "<" . remove ">") $ splitOn " " triple



{- | chooseType will decide what type of variable an object data field should take 
    - String: word                  The word being turned into a variable
-}
chooseType :: String -> Object
chooseType word
    | word == "true" = Bool True
    | word == "false" = Bool False
    | isPrefixOf "+" word && isJust (readMaybe $ tail word :: Maybe Int) = Int (fromJust $ readMaybe $ tail word)
    | isJust (readMaybe word :: Maybe Int) = Int (fromJust $ readMaybe word)
    | isPrefixOf "\"" word && isSuffixOf "\"" word = Lit word
    | otherwise = URL word



{- | Uses indexing to retrieve a value from a list
    - Int: n                        The index to take from
    - [a]: xs                       The list to search
-}
getIndex :: Int -> [a] -> a
getIndex _ [] = error "empty list"
getIndex 0 (x:xs) = x
getIndex n (x:xs) = getIndex (n-1) xs



{- | simplifyTTL will take a strig containing the entire contents of the ttl file and convert it to its simplest form 
     This includes removing any header info, expanding simplified triples, and inserting any prefixes and bases into all subejcts and predicates
     - String: contents             The contents of the ttl file to be formatted correctly
-}
simplifyTTL :: String -> [String]
simplifyTTL contents = init $ map (\s -> handlePrefixes s base prefixes) triples
    where
        sentences = map trim $ splitOn " ." (remove "\n" contents)
        triples = concatMap expandTriples (filter (not . isPrefixOf "@") sentences)
        base = remove "<" . remove ">" . fromJust $ stripPrefix "@base " $ head $ filter (isPrefixOf "@base ") sentences
        prefixes = map (splitAtFirst ':' . remove " <" . remove ">" . fromJust . stripPrefix "@prefix ") (filter (isPrefixOf "@prefix ") sentences)
        splitAtFirst x = fmap (drop 1) . break (x ==)



{- | expandTriples will take in a triple, as well as the base prefix and the set of other prefixes, it will then expand all triples so they meet the simplified form <><><>.
    - String: triple                the triple to expand
    - String: base                  the prefix to apply to all prefixed subjects and predicates
    - [String]: prefixes            the prefixes to apply to all elements which start with "p:"
-}
expandTriples :: String -> [String]
expandTriples triple
    | ',' `elem` triple = getTriples1 triple
    | ';' `elem` triple = getTriples2 triple
    | otherwise = [triple]
    where
        getTriples1 triple  = map ((getHeader1 triple ++ " ") ++ ) $ getList1 triple
        getHeader1 triple   = unwords . init $ splitOn " " $ head $ splitOn " , " triple
        getList1 triple     = last (splitOn " " $ head $ splitOn " , " triple) : tail (splitOn " , " triple)
        getTriples2 triple  = map ((getHeader2 triple ++ " ") ++ ) $ getList2 triple
        getHeader2 triple   = head $ splitOn " " triple
        getList2 triple     = (unwords . tail $ splitOn " " $ head $ splitOn " ; " triple) : tail (splitOn " ; " triple)




{- | handlePrefixes will eliminate the need for base and prefix definitions in the output file but applying them to all triples
    - String: triple                The triple having the prefixes manages
    - String: base                  The base prefix if no other prefix is present
    - [(String, String)]: prefixes  The list of prefixes in the form (name, prefix)
-}
handlePrefixes :: String -> String -> [(String, String)] -> String
handlePrefixes triple base prefixes = process . trim $ concatMap (applyPrefixes . trim . applyPrefixes . trim) (getElements triple)
    where
        applyPrefixes :: String -> String
        applyPrefixes element
            | "<http://" `isPrefixOf` element = element ++ "> "
            | "<" `isPrefixOf` element = "<" ++ base ++ fromJust (stripPrefix "<" element) ++ "> "
            | ":" `isInfixOf` element = ("<" ++ lookup (head $ splitOn ":" element) prefixes ++ concat (tail (splitOn ":" element)) ++ "> ")
            | otherwise = element ++ " "
        lookup prefixName [] = ""
        lookup prefixName (x:xs)
            | prefixName == fst x = snd x
            | otherwise = lookup prefixName xs
        getElements :: String -> [String]
        getElements triple
            | length (splitOn "> " triple) == 3 = splitOn "> " triple
            | length (splitOn ">" triple) == 3 = splitOn ">" triple
            | otherwise = splitOn " " triple
        process :: String -> String
        process element
            | ">>" `isPrefixOf` reverse element = reverse $ fromJust (stripPrefix ">" $ reverse element)
            | otherwise = element



{- | buildFileCollection will take in a filecollection and build the complete set of triple formed by the syntax tree
    - FileCollection: fc            The file collection to contruct
-}
buildFileCollection :: FileCollection -> IO [String]
buildFileCollection (Union fc1 fc2) = do
    x <- buildFileCollection fc1
    y <- buildFileCollection fc2
    return (x `union` y)
buildFileCollection (Intersection fc1 fc2) = do
    x <- buildFileCollection fc1
    y <- buildFileCollection fc2
    return (x `intersect` y)
buildFileCollection (Disjoint fc1 fc2) = do
    x <- buildFileCollection fc1
    y <- buildFileCollection fc2
    return (x \\ y)
buildFileCollection (Filename fn) = loadFileContents fn



{- | loadFileContents will take in a single file name and return the complete, expanded list of triples within that turtle file
    - String: filename              The name of the file to read
-}
loadFileContents :: String -> IO [String]
loadFileContents filename = do
    handle <- openFile filename ReadMode
    contents <- hGetContents handle
    return (simplifyTTL contents)



-- Auxillary function which removes leading and tailing spaces
trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace



-- Auxillary function which removes a substring from a string
remove :: String -> String -> String
remove w "" = ""
remove w s@(c:cs)
    | w `isPrefixOf` s = remove w (drop (length w) s)
    | otherwise = c : remove w cs



-- Auxillary function to remove duplicate elements in a list
removeDuplicates :: (Ord a) => [a] -> [a]
removeDuplicates = map head . group . sort



-- myPrint, helper function which prints a list on seperate lines
myPrint :: [String] -> IO ()
myPrint [] = return()
myPrint (x:xs) = do
    print x
    myPrint xs

{- | checkFileFormat will perform checks on a Turtle file to determine if it is valid or not
   | It first checks for errors in the Subjects and Predicates and then in the objects
          -x       The file undergoing checks that has an RDF format
-}
checkFileFormat :: String -> IO ()
checkFileFormat x = do
  theList <- loadFileContents x
  let checkSP = checkSubPred theList
  if checkSP == "" then pure() else print checkSP
  let findInts = map findNumbers theList
  let filteredList =  map replaceTrueFalse theList
  let spoLength = map length (filterLetters filteredList)
  let combinedLists = zipWith (+) findInts spoLength
  let checkFile = checkTriples combinedLists
  if checkFile == "" then pure() else print checkFile



--checks if the file is divided into strictly triples
--checkTriples :: (Foldable t, Eq a, Num a) => t a -> String
checkTriples xs | not (any (/= 3) xs) = ""
                | otherwise = error "Invalid File Format"

--checks if the correct amount of Subjects and Pedicates are present in the file
checkSubPred :: [[Char]] -> String
checkSubPred xs |  not $ all (>=2) $ map (length . filter (=='>')) xs  = error "Invalid File Format"
                | otherwise = ""
                
--filters out the signs of the numbers and finds them returning a one if they exist at a given sublist
findNumbers :: Num p => [Char] -> p
findNumbers s | any ((==True) . all isDigit) $ toSplit (filter (/= '+') (filter (/= '-') s)) = 1
              | otherwise = 0

filterLetters ::  [String] -> [String]
filterLetters = map (replace . filter ((.||||.)(== '>')(== '\"' )(== '?') (=='~')))

replace :: String -> String
replace ('\"' : '\"' :xs) =  '\"' : replace xs
replace (x:xs)       = x : replace xs
replace ""           = ""

replaceTrueFalse :: String -> String
replaceTrueFalse ('t' : 'r' : 'u' : 'e' : xs) =  '?' : replaceTrueFalse xs
replaceTrueFalse ('f' : 'a' : 'l' : 's' : 'e' : xs) =  '~' : replaceTrueFalse xs
replaceTrueFalse (x:xs)       = x : replaceTrueFalse xs
replaceTrueFalse ""           = ""

(.||||.) :: (a -> Bool) -> (a -> Bool) -> (a->Bool) -> (a -> Bool) -> (a -> Bool)
(.||||.) f g h z a  = f a || g a || h a || z a

(.||.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
(.||.) f g a  = f a || g a

(.&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
(.&&.) f g a  = f a && g a

--takes a string and returns a string array of the string contents without spaces
toSplit :: String -> [String]
toSplit = splitWords . dropWhile (==' ')
    where
        splitWords "" = []
        splitWords s =
          let word = takeWhile (/=' ') s
              (_, rest) = splitAt (length word) s
          in word : splitWords (dropWhile (==' ') rest)

getFilename :: String -> String
getFilename[] = []
getFilename ('h': 't' : 't' : 'p' : ':' : xs)  = ""
getFilename (x:xs) | x == '\"'  = getFilename xs
                   | otherwise = x:getFilename xs


extractOutputFilename :: FilePath -> IO String
extractOutputFilename filename = do
    handle <- openFile filename ReadMode
    contents <- hGetContents handle
    return $ last $ filter ((.&&.) (not.null) (/="<")) $ map getFilename (filter ('\"' `elem`) (splitOn " " contents))

extractInputFilenames :: FilePath -> IO [String]
extractInputFilenames filename = do
    handle <- openFile filename ReadMode
    contents <- hGetContents handle
    return $ init $ filter ((.&&.) (not.null) (/="<")) $ map getFilename (filter ('\"' `elem`) (splitOn " " contents))

checkValidity :: FilePath -> IO ()
checkValidity filename = do
    names <- extractInputFilenames filename
    let out = map checkFileFormat names
    sequence_ out

appendList :: [[Char]] -> [[Char]]
appendList [] = []
appendList (x:xs) = (x ++ " .") : appendList xs

replaceTF :: String -> String
replaceTF ('T' : 'r' : 'u' : 'e' : xs) =  't' : 'r' : 'u' : 'e': replaceTF xs
replaceTF ('F' : 'a' : 'l' : 's' : 'e' : xs) =  'f' : 'a' : 'l' : 's' : 'e'  : replaceTF xs
replaceTF ('>' : ' ' : '<' : xs) =  '>' : '<' : replaceTF xs
replaceTF (x:xs)  = x : replaceTF xs
replaceTF ""  = ""

{- | loadFileContents will take in a single file name and return the complete, expanded list of triples within that turtle file
    - String: filename              The name of the file to read
-}
loadFileContents' :: String -> IO String
loadFileContents' filename = do
    handle <- openFile filename ReadMode
    contents <- hGetContents handle
    return contents
