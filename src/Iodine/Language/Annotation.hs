{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}

module Iodine.Language.Annotation where

import           Iodine.Types

import           Control.Lens
import           Control.Monad
import           Data.Aeson
import           Data.Aeson.Types
import qualified Data.ByteString.Lazy as B
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T
import           Polysemy
import           Polysemy.Reader

data Annotations =
  Annotations { _sources       :: HS.HashSet Id
              , _sinks         :: HS.HashSet Id
              , _initialEquals :: HS.HashSet Id
              , _alwaysEquals  :: HS.HashSet Id
              , _assertEquals  :: HS.HashSet Id
              , _tagEquals     :: HS.HashSet Id
              }
  deriving (Show)

emptyAnnotations :: Annotations
emptyAnnotations = Annotations mempty mempty mempty mempty mempty mempty

data Qualifier =
    QImplies Id (L Id)
  | QIff     Id (L Id)
  | QPairs   (L Id)
  deriving (Show)

data ModuleAnnotations =
  ModuleAnnotations { _moduleAnnotations :: Annotations
                    , _moduleQualifiers  :: L Qualifier
                    , _clocks            :: HS.HashSet Id
                    }
  deriving (Show)

emptyModuleAnnotations :: ModuleAnnotations
emptyModuleAnnotations = ModuleAnnotations emptyAnnotations mempty mempty

data AnnotationFile =
  AnnotationFile { _afAnnotations :: HM.HashMap Id ModuleAnnotations -- ^ module -> annotations
                 , _afTopModule   :: Id                              -- ^ name of the top module
                 }
  deriving (Show)

makeLenses ''Annotations
makeLenses ''ModuleAnnotations
makeLenses ''AnnotationFile

parseAnnotations :: B.ByteString -> AnnotationFile
parseAnnotations bs =
  case eitherDecode bs >>= validateAnnotationFile of
    Right af -> af
    Left msg -> error $ "Parsing annotation file failed:\n" ++ msg

-- | 1. top module has source and sink annotations
validateAnnotationFile :: AnnotationFile -> Either String AnnotationFile
validateAnnotationFile af =
  let topModuleName = af ^. afTopModule
      mAnnots       = (^. moduleAnnotations) <$> HM.lookup topModuleName (af ^. afAnnotations)
  in case mAnnots of
       Nothing     -> Left "Top module does not exist"
       Just annots ->
         if | HS.null (annots ^. sources) -> Left $ "Top module has no source! " ++ show annots
            | HS.null (annots ^. sinks)   -> Left $ "Top module has no sink! " ++ show annots
            | otherwise -> Right af


instance FromJSON Annotations where
  parseJSON =
    withObjectKeys "Annotations" objKeys $ \o -> do
    let allKeys   = HM.keysSet o
        validKeys = HS.fromList ["source", "sink", "initial_eq", "always_eq", "assert_eq"]
        keyDiff   = HS.difference allKeys validKeys
    unless (HS.null keyDiff) $
      parserThrowError [] ("invalid keys " ++ show keyDiff)
    Annotations
      <$> o .:? "source"     .!= mempty
      <*> o .:? "sink"       .!= mempty
      <*> o .:? "initial_eq" .!= mempty
      <*> o .:? "always_eq"  .!= mempty
      <*> o .:? "assert_eq"  .!= mempty
      <*> o .:? "tag_eq"     .!= mempty
      where
        objKeys = ["source", "sink", "initial_eq", "always_eq", "assert_eq", "tag_eq"]


instance FromJSON Qualifier where
  parseJSON = withObject "Qualifier" $ \o -> do
    t :: String <- o .: "type"
    case t of
      "implies" -> QImplies <$> o .: "lhs" <*> o .: "rhs"
      "iff"     -> QIff     <$> o .: "lhs" <*> o .: "rhs"
      "pairs"   -> QPairs   <$> o .: "variables"
      _         -> typeMismatch ("unknown qualifier type: " ++ t) (toJSON t)

instance FromJSON ModuleAnnotations where
  parseJSON = withObjectKeys "ModuleAnnotation" objKeys $ \o ->
    ModuleAnnotations
    <$> o .:? "annotations" .!= emptyAnnotations
    <*> o .:? "qualifiers"  .!= mempty
    <*> parseClock o "clock"
    where
      objKeys = ["annotations", "qualifiers", "clock", "blocklist"]

instance FromJSON AnnotationFile where
  parseJSON = withObjectKeys "AnnotationFile" ["modules", "top_module", "history", "blocklist"] $ \o ->
    AnnotationFile
    <$> o .:  "modules"
    <*> o .:  "top_module"

withObjectKeys :: String -> [T.Text] -> (Object -> Parser a) -> Value -> Parser a
withObjectKeys typ keys parser = withObject typ parser'
  where
    parser' o =
      let extraKeys = HM.keysSet o `HS.difference` HS.fromList keys
      in if HS.null extraKeys
         then parser o
         else fail $ "Unexpected keys " ++ show (HS.toList extraKeys) ++ " in object " ++ show (encode o)

parseClock :: Object -> T.Text -> Parser (HS.HashSet Id)
parseClock o k =
  case HM.lookup k o of
    Nothing          -> return mempty
    Just (String v)  -> return $ HS.singleton v
    Just a@(Array _) -> parseJSON a
    Just v           -> fail $ "Unexpected " ++ show v ++ ". Expected String or Array of Strings"



toModuleAnnotations :: Id -> AnnotationFile -> ModuleAnnotations
toModuleAnnotations m = (^. afAnnotations . to find)
  where
    find = HM.lookupDefault emptyModuleAnnotations m

getModuleAnnotations :: Member (Reader AnnotationFile) r => Id -> Sem r ModuleAnnotations
getModuleAnnotations = asks . toModuleAnnotations

toAnnotations :: Id -> AnnotationFile -> Annotations
toAnnotations m = view moduleAnnotations . toModuleAnnotations m

getAnnotations :: Member (Reader AnnotationFile) r => Id -> Sem r Annotations
getAnnotations = asks . toAnnotations

getQualifiers :: Member (Reader AnnotationFile) r => Id -> Sem r (L Qualifier)
getQualifiers m = asks (view moduleQualifiers . toModuleAnnotations m)

getSources :: Member (Reader AnnotationFile) r => Id -> Sem r (HS.HashSet Id)
getSources m = (^. sources) <$> getAnnotations m

getSinks :: Member (Reader AnnotationFile) r => Id -> Sem r (HS.HashSet Id)
getSinks m = (^. sinks) <$> getAnnotations m

getClocks :: Member (Reader AnnotationFile) r => Id -> Sem r (HS.HashSet Id)
getClocks m = asks (view clocks . toModuleAnnotations m)

annotationVariables :: Annotations -> Ids
annotationVariables a =
  (a ^. sources) <>
  (a ^. sinks) <>
  (a ^. initialEquals) <>
  (a ^. alwaysEquals) <>
  (a ^. assertEquals) <>
  (a ^. tagEquals)
