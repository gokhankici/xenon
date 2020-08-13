module Iodine.ConstantConfig where

-- | include every variable in the kvars. better for ctx-gen
includeEveryVariable :: Bool
includeEveryVariable = False

-- | guess qualifiers
enableQualifierGuess :: Bool
enableQualifierGuess = True

-- | call `dot` to generate the .pdf files from .dot files
generateGraphPDF :: Bool
generateGraphPDF = True

doNotMarkSubmoduleVariables :: Bool
doNotMarkSubmoduleVariables = True