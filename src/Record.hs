module Record(
    tMut,
    tName,
    tTyp,
    eMut,
    eName,
    eTyp,
    eExp
)
where
import Types (TRecordProp (TRecordProp), ERecordProp (ERecordProp), Mutability, Typ, Expr)

tMut :: TRecordProp -> Mutability
tMut (TRecordProp m _ _) = m

tName :: TRecordProp -> String
tName (TRecordProp _ n _) = n

tTyp :: TRecordProp -> Typ
tTyp (TRecordProp _ _ t) = t

eMut :: ERecordProp -> Mutability
eMut (ERecordProp m _ _ _) = m

eName :: ERecordProp -> String
eName (ERecordProp _ n _ _) = n

eTyp :: ERecordProp -> Typ
eTyp (ERecordProp _ _ t _) = t

eExp :: ERecordProp -> Expr
eExp (ERecordProp _ _ _ e) = e