import System.Process

runTwee :: [String] -> [String] -> String -> IO Bool
runTwee args axioms conj = do
  output <-
    readProcess "/home/nick/.local/bin/twee"
    ("--quiet":"--no-proof":"--max-cps":"20000":"/dev/stdin":args)
    (unlines $ map axiom axioms ++ [conjecture conj])
  let
    res =
      case lines output of
        ["RESULT: Unsatisfiable (the axioms are contradictory)."] ->
          True
        ["RESULT: Theorem (the conjecture is true)."] ->
          True
        ["RESULT: GaveUp (couldn't solve the problem)."] ->
          False
        _ ->
          error output

  putStrLn (show (length axioms) ++ " => " ++ show res)
  return res

good, bad :: [String]
good = ["--no-simplify"]
bad = ["--always-simplify"]

axiom, conjecture :: String -> String
axiom xs = "cnf(axiom, axiom, " ++ xs ++ ")."
conjecture xs = "cnf(conjecture, conjecture, " ++ xs ++ ")."

simplifyConjecture :: [String] -> [String] -> String -> IO ([String], String)
simplifyConjecture axioms lemmas conjecture = do
  res <- loop (reverse lemmas)
  case res of
    Nothing ->
      return (lemmas, conjecture)
    Just (lemmas, conjecture) ->
      return (reverse lemmas, conjecture)
  where
    loop [] = return Nothing
    loop (lemma:lemmas) = do
      res <- loop lemmas
      case res of
        Just (lemmas, conjecture) ->
          return (Just (lemmas, conjecture))
        Nothing -> do
          res <- runTwee bad axioms lemma
          case res of
            True -> return Nothing
            False -> return (Just (lemmas, lemma))

maximiseAxioms :: [String] -> [String] -> String -> IO [String]
maximiseAxioms axioms lemmas conjecture = loop [] (reverse lemmas)
  where
    loop axioms' [] = return (axioms ++ axioms')
    loop axioms' (lemma:lemmas) = do
      res <- runTwee bad (axioms ++ axioms' ++ [lemma]) conjecture
      case res of
        False ->
          loop (lemma:axioms') lemmas
        True ->
          loop axioms' lemmas

minimiseAxioms :: [String] -> String -> IO [String]
minimiseAxioms axioms conjecture = loop [] axioms
  where
    loop axioms [] = return (reverse axioms)
    loop axioms (axiom:axioms') = do
      res <- runTwee good (axioms ++ axioms') conjecture
      case res of
        True -> do
          res <- runTwee bad (axioms ++ axioms') conjecture
          case res of
            False ->
              loop axioms axioms'
            True ->
              loop (axiom:axioms) axioms'
        False ->
          loop (axiom:axioms) axioms'

selectAxiom :: [String] -> [String] -> String -> IO String
selectAxiom axioms axioms' conjecture = loop axioms
  where
    loop [] = error "no axiom worked"
    loop (axiom:axioms) = do
      res <- runTwee good (axiom:axioms') conjecture
      case res of
        True -> do
          res <- runTwee bad (axiom:axioms') conjecture
          case res of
            False ->
              return axiom
            True ->
              loop axioms
        False ->
          loop axioms

reduceAxioms :: [String] -> [String] -> String -> IO [String]
reduceAxioms axioms lemmas conjecture = loop [] axioms
  where
    loop chosen [] = return chosen
    loop chosen (axiom:axioms) = do
      axiom' <- selectAxiom (reverse lemmas ++ [axiom]) (chosen ++ axioms) conjecture
      loop (axiom':chosen) axioms

minimise :: IO [String]
minimise = do
  axioms <- lines <$> readFile "axioms.p"
  lemmas <- lines <$> readFile "lemmas.p"
  [conjecture] <- lines <$> readFile "conjecture.p"
  axioms' <- reduceAxioms axioms lemmas conjecture
  writeFile "axioms2.p" (unlines axioms')
  return axioms'
