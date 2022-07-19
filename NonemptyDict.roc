interface NonemptyDict
    exposes [
        NonemptyDict,
        toDict,
        fromDict,
        get,
        walk,
        insert,
        len,
        remove,
        contains,
        single,
        keys,
        values,
        insertAll,
        keepShared,
        removeAll,
    ]
    imports [
        Bool.{ Bool },
        Result.{ Result },
        NonemptyList.{ NonemptyList },
        Dict.{ Dict },
    ]


NonemptyDict k v := NonemptyList [Pair k v]


toDict : NonemptyDict k v -> Dict k v
toDict = \@NonemptyDict nonempty ->
    NonemptyList.toList nonempty
    |> List.walk Dict.empty (\dict, Pair key value -> Dict.insert dict key value)


fromDict : Dict k v -> Result (NonemptyDict k v) [ DictIsEmpty ]*
fromDict = \dict ->
    list = List.map2 (Dict.keys dict) (Dict.values dict) Pair
    when NonemptyList.fromList list is
        Ok nonempty ->
            @NonemptyDict nonempty |> Ok

        Err ListIsEmpty ->
            Err DictIsEmpty


get : NonemptyDict k v, k -> Result v [KeyNotFound]*
get = \@NonemptyDict list, needle ->
    when NonemptyList.find list (\Pair key _ -> key == needle) is
        Ok (Pair _ v) ->
            Ok v

        Err NotFound ->
            Err KeyNotFound


walk : NonemptyDict k v, state, (state, k, v -> state) -> state
walk = \@NonemptyDict list, initialState, transform ->
    NonemptyList.walk list initialState (\state, Pair k v -> transform state k v)


insert : NonemptyDict k v, k, v -> NonemptyDict k v
insert = \@NonemptyDict list, k, v ->
    when NonemptyList.findIndex list (\Pair key _ -> key == k) is
        Err NotFound ->
            insertFresh (@NonemptyDict list) k v

        Ok index ->
            list
            |> NonemptyList.set index (Pair k v)
            |> @NonemptyDict


len : NonemptyDict k v -> Nat
len = \@NonemptyDict list ->
    NonemptyList.len list


remove : NonemptyDict k v, k -> Dict k v
remove = \nonemptyDict, key ->
    Dict.remove (toDict nonemptyDict) key


contains : NonemptyDict k v, k -> Bool
contains = \@NonemptyDict list, needle ->
    step = \_, Pair key _val ->
        if key == needle then
            Break {}
        else
            Continue {}

    when NonemptyList.iterate list {} step is
        Continue _ -> False
        Break _ -> True


single : k, v -> NonemptyDict k v
single = \key, value ->
    Pair key value |> NonemptyList.single |> @NonemptyDict


## Returns a [NonemptyList] of the dictionary's keys.
keys : NonemptyDict k v -> NonemptyList k
keys = \@NonemptyDict list ->
    NonemptyList.map list (\Pair k _ -> k)


## Returns a [NonemptyList] of the Dict's values
values : NonemptyDict k v -> NonemptyList v
values = \@NonemptyDict list ->
    NonemptyList.map list (\Pair _ v -> v)


insertAll : NonemptyDict k v, NonemptyDict k v -> NonemptyDict k v
insertAll = \xs, @NonemptyDict ys ->
    NonemptyList.walk ys xs (\state, Pair k v -> insertIfVacant state k v)


keepShared : NonemptyDict k v, NonemptyDict k v -> Dict k v
keepShared = \@NonemptyDict xs, ys ->
    dictY = toDict ys
    List.keepIf (NonemptyList.toList xs) (\Pair k _ -> Dict.contains dictY k)
    |> List.walk Dict.empty (\dict, Pair k v -> Dict.insert dict k v)


removeAll : NonemptyDict k v, NonemptyDict k v -> Dict k v
removeAll = \xs, @NonemptyDict ys ->
    List.walk (NonemptyList.toList ys) (toDict xs) (\state, Pair k _ -> Dict.remove state k)


## Internal helper function to insert a new association
##
## Precondition: `k` should not exist in the Dict yet.
insertFresh : NonemptyDict k v, k, v -> NonemptyDict k v
insertFresh = \@NonemptyDict list, k, v ->
    list
    |> NonemptyList.append (Pair k v)
    |> @NonemptyDict


insertIfVacant : NonemptyDict k v, k, v -> NonemptyDict k v
insertIfVacant = \dict, key, value ->
    if contains dict key then
        dict
    else
        insert dict key value