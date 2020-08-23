module Xenon.ConstantConfig where

-- | include every variable in the kvars. better for ctx-gen
includeEveryVariable :: Bool
includeEveryVariable = False

-- | guess qualifiers
enableQualifierGuess :: Bool
enableQualifierGuess = True

-- | call `dot` to generate the .pdf files from .dot files
generateGraphPDF :: Bool
generateGraphPDF = True

-- | if the number of nodes is greater than this, do not generate the graph
maxFeasibleNodeCount :: Int
maxFeasibleNodeCount = 50

doNotMarkSubmoduleVariables :: Bool
doNotMarkSubmoduleVariables = True

inlineAllModules :: Bool
inlineAllModules = False