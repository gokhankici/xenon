{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}

module Iodine.Language.Annotation where

import           Iodine.Types
import           Iodine.ConstantConfig

import           Control.Effect.Reader
import           Control.Lens
import           Control.Monad
import           Data.Aeson
import           Data.Aeson.Types
import qualified Data.ByteString.Lazy as B
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.List (sort)
import qualified Data.Text as T
import           Data.Hashable
import GHC.Generics (Generic)

data Annotations =
  Annotations { _sources       :: HS.HashSet Id
              , _sinks         :: HS.HashSet Id
              , _initialEquals :: HS.HashSet Id
              , _alwaysEquals  :: HS.HashSet Id
              , _assertEquals  :: HS.HashSet Id
              , _tagEquals     :: HS.HashSet Id
              , _cannotMarks   :: HS.HashSet Id
              , _instanceInitialEquals :: HS.HashSet InstanceEquals
              , _instanceAlwaysEquals :: HS.HashSet InstanceEquals
              }
  deriving (Show, Read)

emptyAnnotations :: Annotations
emptyAnnotations =
  Annotations mempty mempty mempty mempty mempty mempty mempty mempty mempty

data InstanceEquals =
  InstanceEquals { _instanceEqualsParentModule :: Id
                 , _instanceEqualsInstanceName :: Id
                 , _instanceEqualsVariables    :: HS.HashSet Id
                 }
  deriving (Show, Read, Eq, Generic)

instance Hashable InstanceEquals

data Qualifier =
    QImplies Id (L Id)
  | QIff     Id (L Id)
  | QPairs   (L Id)
  deriving (Show, Read)

data ModuleAnnotations =
  ModuleAnnotations { _moduleAnnotations :: Annotations
                    , _moduleQualifiers  :: L Qualifier
                    , _clocks            :: HS.HashSet Id
                    , _canInline         :: Bool
                    }
  deriving (Show, Read)

emptyModuleAnnotations :: ModuleAnnotations
emptyModuleAnnotations = ModuleAnnotations emptyAnnotations mempty mempty False

data AnnotationFile =
  AnnotationFile { _afAnnotations :: HM.HashMap Id ModuleAnnotations -- ^ module -> annotations
                 , _afTopModule   :: Id     -- ^ name of the top module
                 , _afIncludeDirs :: [Id]   -- ^ can be relative to the verilog file
                 }
  deriving (Show, Read)

makeLenses ''InstanceEquals
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

instance FromJSON InstanceEquals where
  parseJSON =
    withObjectKeys "InstanceEquals" validKeys $ \o ->
      InstanceEquals
      <$> o .: "parent_module"
      <*> o .: "instance_name"
      <*> o .: "variables"
    where
      validKeys = ["parent_module", "instance_name", "variables"]

instance FromJSON Annotations where
  parseJSON =
    withObjectKeys "Annotations" validKeys $ \o -> do
    let allKeys   = HM.keysSet o
        keyDiff   = HS.difference allKeys (HS.fromList validKeys)
    unless (HS.null keyDiff) $
      parserThrowError [] ("invalid keys " ++ show keyDiff)
    Annotations
      <$> o .:? "source"       .!= mempty
      <*> o .:? "sink"         .!= mempty
      <*> o .:? "initial_eq"   .!= mempty
      <*> o .:? "always_eq"    .!= mempty
      <*> o .:? "assert_eq"    .!= mempty
      <*> o .:? "tag_eq"       .!= mempty
      <*> o .:? "cannot_mark"  .!= mempty
      <*> o .:? "instance_initial_eq" .!= mempty
      <*> o .:? "instance_always_eq"  .!= mempty
      where
        validKeys = [ "source"
                    , "sink"
                    , "initial_eq"
                    , "always_eq"
                    , "assert_eq"
                    , "tag_eq"
                    , "ignore"
                    , "cannot_mark"
                    , "instance_initial_eq"
                    , "instance_always_eq"
                    ]

instance ToJSON Annotations where
  toJSON a = Object o'
    where
      o' = addIE "instance_initial_eq" instanceInitialEquals $
           addIE "instance_always_eq"  instanceAlwaysEquals o
      addIE k l =
        let ie = a ^. l
        in if HS.null ie
           then id
           else HM.insert k (toJSON ie)
      o = HM.fromList $ fmap (fmap toJSON) $
          filter (not . null . snd) $
          fmap (sort . HS.toList . (a ^.)) <$> fields
      fields = [ ("source",        sources)
               , ("sink",          sinks)
               , ("initial_eq",    initialEquals)
               , ("always_eq",     alwaysEquals)
               , ("assert_eq",     assertEquals)
               , ("tag_eq",        tagEquals)
               , ("cannot_mark",   cannotMarks)
               ]

instance ToJSON InstanceEquals where
  toJSON iie = Object $ HM.fromList
    [ ("parent_module", toJSON $ iie ^. instanceEqualsParentModule)
    , ("instance_name", toJSON $ iie ^. instanceEqualsInstanceName)
    , ("variables", toJSON $ iie ^. instanceEqualsVariables)
    ]

instance FromJSON Qualifier where
  parseJSON = withObject "Qualifier" $ \o -> do
    t :: String <- o .: "type"
    case t of
      "implies" -> QImplies <$> o .: "lhs" <*> o .: "rhs"
      "iff"     -> QIff     <$> o .: "lhs" <*> o .: "rhs"
      "pairs"   -> QPairs   <$> o .: "variables"
      _         -> typeMismatch ("unknown qualifier type: " ++ t) (toJSON t)

instance ToJSON Qualifier where
  toJSON (QImplies l r) =
    Object (mempty & (at "type" ?~ String "implies") .
                     (at "lhs"  ?~ toJSON l) .
                     (at "rhs"  ?~ toJSON r) )
  toJSON (QIff l r) =
    Object (mempty & (at "type" ?~ String "iff") .
                     (at "lhs"  ?~ toJSON l) .
                     (at "rhs"  ?~ toJSON r) )
  toJSON (QPairs vs) =
    Object (mempty & (at "type"      ?~ String "pairs") .
                     (at "variables" ?~ toJSON vs))

instance FromJSON ModuleAnnotations where
  parseJSON = withObject "ModuleAnnotation" $ \o ->
    fmap fixInline $
    ModuleAnnotations
    <$> o .:? "annotations" .!= emptyAnnotations
    <*> o .:? "qualifiers"  .!= mempty
    <*> parseClock o "clock"
    <*> o .:? "inline"      .!= False
    where
      fixInline :: ModuleAnnotations -> ModuleAnnotations
      fixInline = if inlineAllModules
                  then canInline .~ True
                  else id

instance ToJSON ModuleAnnotations where
  toJSON ma =
    Object $ mempty & (at "annotations" ?~ toJSON (ma ^. moduleAnnotations)) .
                      (at "qualifiers"  ?~ toJSON (ma ^. moduleQualifiers)) .
                      (at "clock"       ?~ toJSON (ma ^. clocks)) .
                      (at "inline"      ?~ toJSON (ma ^. canInline))

instance FromJSON AnnotationFile where
  parseJSON = withObject "AnnotationFile" $ \o ->
    AnnotationFile
    <$> o .:  "modules"
    <*> o .:  "top_module"
    <*> o .:? "include_dirs" .!= mempty
    -- where
    --   objKeys = ["modules", "top_module", "history", "blocklist", "qualifiers", "qualifiers-history"]

instance ToJSON AnnotationFile where
  toJSON af =
    Object $ mempty & (at "modules" ?~ toJSON (toJSON <$> af ^. afAnnotations)) .
                      (at "top_module" ?~ toJSON (af ^. afTopModule)) .
                      (at "include_dirs" ?~ toJSON (af ^. afIncludeDirs))

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

getModuleAnnotations :: Has (Reader AnnotationFile) sig m => Id -> m ModuleAnnotations
getModuleAnnotations = asks . toModuleAnnotations

toAnnotations :: Id -> AnnotationFile -> Annotations
toAnnotations m = view moduleAnnotations . toModuleAnnotations m

getAnnotations :: Has (Reader AnnotationFile) sig m => Id -> m Annotations
getAnnotations = asks . toAnnotations

getQualifiers :: Has (Reader AnnotationFile) sig m => Id -> m (L Qualifier)
getQualifiers m = asks (view moduleQualifiers . toModuleAnnotations m)

getSources :: Has (Reader AnnotationFile) sig m => Id -> m (HS.HashSet Id)
getSources m = (^. sources) <$> getAnnotations m

getSinks :: Has (Reader AnnotationFile) sig m => Id -> m (HS.HashSet Id)
getSinks m = (^. sinks) <$> getAnnotations m

getClocks :: Has (Reader AnnotationFile) sig m => Id -> m (HS.HashSet Id)
getClocks m = asks (view clocks . toModuleAnnotations m)

annotationVariables :: Annotations -> Ids
annotationVariables a =
  (a ^. sources) <>
  (a ^. sinks) <>
  (a ^. initialEquals) <>
  (a ^. alwaysEquals) <>
  (a ^. assertEquals) <>
  (a ^. tagEquals)
