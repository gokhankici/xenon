{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Iodine.Language.Annotation where

import           Iodine.Types

import           Control.Lens
import           Control.Monad
import           Data.Aeson
import           Data.Aeson.Types
import qualified Data.ByteString.Lazy as B
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM
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

data Qualifier =
    QImplies Id (L Id)
  | QIff     Id (L Id)
  | QPairs   (L Id)
  deriving (Show)

data ModuleAnnotations =
  ModuleAnnotations { _moduleAnnotations :: Annotations
                    , _moduleQualifiers  :: L Qualifier
                    , _clock             :: Maybe Id
                    }
  deriving (Show)

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
  case eitherDecode bs of
    Right af -> af
    Left msg -> error $ "Parsing annotation file failed:\n" ++ msg

instance FromJSON Annotations where
  parseJSON = withObject "Annotations" $ \o -> do
    let allKeys   = HM.keysSet o
        validKeys = HS.fromList ["source", "sink", "initial_eq", "always_eq", "assert_eq"]
        keyDiff   = HS.difference allKeys validKeys
    unless (HS.null keyDiff) $
      parserThrowError [] ("invalid keys " ++ show keyDiff)
    annot <-
      Annotations
      <$> o .:  "source"
      <*> o .:  "sink"
      <*> o .:? "initial_eq" .!= mempty
      <*> o .:? "always_eq"  .!= mempty
      <*> o .:? "assert_eq"  .!= mempty
      <*> o .:? "tag_eq"     .!= mempty
    return $
      annot & tagEquals %~ mappend (annot ^. sources <> annot ^. sinks)


instance FromJSON Qualifier where
  parseJSON = withObject "Qualifier" $ \o -> do
    t :: String <- o .: "type"
    case t of
      "implies" -> QImplies <$> o .: "lhs" <*> o .: "rhs"
      "iff"     -> QIff     <$> o .: "lhs" <*> o .: "rhs"
      "pairs"   -> QPairs   <$> o .: "variables"
      _         -> typeMismatch ("unknown qualifier type: " ++ t) (toJSON t)

instance FromJSON ModuleAnnotations where
  parseJSON = withObject "ModuleAnnotation" $ \o ->
    ModuleAnnotations
    <$> o .:  "annotations"
    <*> o .:? "qualifiers" .!= mempty
    <*> o .:? "clock"

instance FromJSON AnnotationFile where
  parseJSON = withObject "AnnotationFile" $ \o ->
    AnnotationFile
    <$> o .:  "modules"
    -- <*> o .:? "qualifiers" .!= mempty
    <*> o .:  "top_module"


toModuleAnnotations :: Id -> AnnotationFile -> ModuleAnnotations
toModuleAnnotations m = (^. afAnnotations . to find)
  where
    errMsg = "Module " ++ show m ++ " not found in annotations"
    find   = HM.lookupDefault (error errMsg) m

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

getClock :: Member (Reader AnnotationFile) r => Id -> Sem r (Maybe Id)
getClock m = asks (view clock . toModuleAnnotations m)
