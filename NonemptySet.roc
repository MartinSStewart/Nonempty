interface NonemptySet
    exposes [
        NonemptySet,
        single,
        walk,
        insert,
        len,
        remove,
        contains,
        toList,
        #fromList,
        union,
        intersection,
        difference,
    ]
    imports [
        List,
        Bool.{ Bool },
        Dict.{ Dict },
        NonemptyDict.{ NonemptyDict },
        NonemptyList.{ NonemptyList },
        Set.{ Set }
    ]

NonemptySet k := NonemptyDict k {}

fromDict : NonemptyDict k {} -> NonemptySet k
fromDict = \dict -> @NonemptySet dict

toDict : NonemptySet k -> NonemptyDict k {}
toDict = \@NonemptySet dict -> dict

#fromSet : Set k -> Result (NonemptySet k) [ SetIsEmpty ]*
#fromSet = \set ->
#    when Set.toList set |> NonemptyDict.fromDict is
#        Ok ok ->
#            fromDict ok |> Ok
#
#        Err DictIsEmpty ->
#            Err SetIsEmpty


single : k -> NonemptySet k
single = \key ->
    @NonemptySet (NonemptyDict.single key {})

## Make sure never to insert a *NaN* to a [NonemptySet]! Because *NaN* is defined to be
## unequal to *NaN*, adding a *NaN* results in an entry that can never be
## retrieved or removed from the [NonemptySet].
insert : NonemptySet k, k -> NonemptySet k
insert = \@NonemptySet dict, key ->
    dict
    |> NonemptyDict.insert key {}
    |> @NonemptySet

len : NonemptySet k -> Nat
len = \@NonemptySet dict ->
    NonemptyDict.len dict

## Drops the given element from the set.
remove : NonemptySet k, k -> Set k
remove = \@NonemptySet dict, key ->
    NonemptyDict.remove dict key |> Dict.keys |> Set.fromList

contains : NonemptySet k, k -> Bool
contains = \set, key ->
    set
    |> NonemptySet.toDict
    |> NonemptyDict.contains key

toList : NonemptySet k -> NonemptyList k
toList = \@NonemptySet dict ->
    NonemptyDict.keys dict

#fromList : NonemptyList k -> NonemptySet k
#fromList = \list ->
#    NonemptyList.toList list |> Set.fromList

union : NonemptySet k, NonemptySet k -> NonemptySet k
union = \@NonemptySet dict1, @NonemptySet dict2 ->
    @NonemptySet (NonemptyDict.insertAll dict1 dict2)

intersection : NonemptySet k, NonemptySet k -> Set k
intersection = \@NonemptySet dict1, @NonemptySet dict2 ->
    NonemptyDict.keepShared dict1 dict2 |> Dict.keys |> Set.fromList

difference : NonemptySet k, NonemptySet k -> Set k
difference = \@NonemptySet dict1, @NonemptySet dict2 ->
    NonemptyDict.removeAll dict1 dict2 |> Dict.keys |> Set.fromList

walk : NonemptySet k, state, (state, k -> state) -> state
walk = \set, state, step ->
    NonemptyDict.walk (NonemptySet.toDict set) state (\s, k, _ -> step s k)