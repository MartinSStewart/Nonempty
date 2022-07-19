interface NonemptyList
    exposes [
        NonemptyList,
        toList,
        fromList,
        len,
        get,
        set,
        swap,
        replace,
        append,
        appendFromList,
        prepend,
        prependFromList,
        concat,
        concatListLeft,
        concatListRight,
        single,
        repeat,
        reverse,
        contains,
        walk,
        walkBackwards,
        sum,
        product,
        any,
        all,
        keepIf,
        dropIf,
        keepOks,
        keepErrs,
        map,
        map2,
        map3,
        map4,
        mapWithIndex,
        sortWith,
        sortAsc,
        sortDesc,
        first,
        last,
        dropFirst,
        dropLast,
        takeFirst,
        takeLast,
        drop,
        dropAt,
        min,
        max,
        joinMap,
        find,
        findIndex,
        iterate,
        sublist,
        intersperse,
        split
    ]
    imports [
        Bool.{ Bool },
        Result.{ Result },
        List
    ]

## A list that contains at least one element.
NonemptyList a :=
    { rest: (List a), lastItem: a }


## Convert a NonemptyList to an ordinary list
toList : NonemptyList a -> List a
toList = \@NonemptyList { rest, lastItem } ->
    List.append rest lastItem


fromList : List a -> Result (NonemptyList a) [ ListIsEmpty ]*
fromList = \list ->
    when List.get list (List.len list - 1) is
        Ok value ->
            @NonemptyList { rest: List.dropLast list, lastItem: value } |> Ok

        Err OutOfBounds ->
            Err ListIsEmpty

## Get the number of elements in a list.
## Since the list is nonempty, this will always be greater than 0.
len : NonemptyList a -> Nat
len = \@NonemptyList { rest } ->
    List.len rest + 1

## Get an element from a list as a given index
##
## >>> list = NonemptyList.appendFromList [ "a", "b" ] "c"
## >>> NonemptyList.get list 2 == Ok "c"
## >>> NonemptyList.get list 3 == Err OutOfBounds
get : NonemptyList a, Nat -> Result a [ OutOfBounds ]*
get = \nonempty, index ->
    (@NonemptyList { rest, lastItem }) = nonempty
    if index == len nonempty - 1 then
        Ok lastItem
    else
        List.get rest (Num.subSaturated index 1)

## Replaces the element at the given index with a replacement.
##
## >>> list = NonemptyList.appendFromList [ "a", "b" ] "c"
## >>> list2 = NonemptyList.set list 1 "B"
## >>> list2 == NonemptyList.appendFromList [ "a", "B" ] "c"
##
## If the given index is outside the bounds of the list, returns the original
## list unmodified.
##
## To drop the element at a given index, instead of replacing it, see [NonemptyList.dropAt].
set : NonemptyList a, Nat, a -> NonemptyList a
set = \nonempty, index, value ->
    (@NonemptyList { rest, lastItem }) = nonempty
    if index == len nonempty - 1 then
        @NonemptyList { rest: rest, lastItem: value }
    else
        { rest: List.set rest (Num.subSaturated index 1) value, lastItem: lastItem }
            |> @NonemptyList


swap : NonemptyList a, Nat, Nat -> NonemptyList a
swap = \nonempty, left, right ->
    (@NonemptyList { rest, lastItem }) = nonempty
    lastIndex = len nonempty - 1
    if left != lastIndex && right != lastIndex then
        @NonemptyList { rest: List.swap rest left right, lastItem: lastItem }

    else if left != lastIndex then
        when List.get rest left is
            Ok leftValue ->
                @NonemptyList { rest: List.set rest left lastItem, lastItem: leftValue }

            Err _ ->
                nonempty

    else if right != lastIndex then
        when List.get rest right is
            Ok rightValue ->
                @NonemptyList { rest: List.set rest right lastItem, lastItem: rightValue }

            Err _ ->
                nonempty

    else
        nonempty


replace : NonemptyList a, Nat, a -> { list: NonemptyList a, value: a }
replace = \nonempty, index, value ->
    when get nonempty index is
        Ok oldValue ->
            { list: set nonempty index value, value: oldValue }

        Err _ ->
            { list: nonempty, value: value }


append : NonemptyList a, a -> NonemptyList a
append = \(@NonemptyList { rest, lastItem }), value ->
    @NonemptyList { rest: List.append rest lastItem, lastItem: value }


appendFromList : List a, a -> NonemptyList a
appendFromList = \rest, lastItem ->
    @NonemptyList { rest: rest, lastItem: lastItem }


prepend : NonemptyList a, a -> NonemptyList a
prepend = \(@NonemptyList { rest, lastItem }), value ->
    @NonemptyList { rest: List.prepend rest value, lastItem: lastItem }


prependFromList : List a, a -> NonemptyList a
prependFromList = \list, item ->
    when List.get list (List.len list - 1) is
        Ok value ->
            @NonemptyList { rest: List.prepend (List.dropLast list) item, lastItem: value }

        Err _ ->
            @NonemptyList { rest: [], lastItem: item }


concat : NonemptyList a, NonemptyList a -> NonemptyList a
concat = \a, (@NonemptyList { rest, lastItem }) ->
    @NonemptyList { rest: List.concat (toList a) rest, lastItem: lastItem }


concatListLeft : List a, NonemptyList a -> NonemptyList a
concatListLeft = \a, (@NonemptyList { rest, lastItem }) ->
    @NonemptyList { rest: List.concat a rest, lastItem: lastItem }


concatListRight : NonemptyList a, List a -> NonemptyList a
concatListRight = \nonempty, list ->
    when List.last list is
        Ok lastItem ->
            { rest: List.concat (toList nonempty) (List.dropLast list), lastItem: lastItem }
                |> @NonemptyList

        Err _ ->
            nonempty


single : a -> NonemptyList a
single = \item ->
    @NonemptyList { rest: [], lastItem: item }


repeat : a, Nat -> NonemptyList a
repeat = \value, count ->
    @NonemptyList { rest: List.repeat value (count - 1), lastItem: value }


reverse : NonemptyList a -> NonemptyList a
reverse = \nonempty ->
    reverseHelp nonempty 0 (Num.subSaturated (len nonempty) 1)


reverseHelp : NonemptyList a, Nat, Nat -> NonemptyList a
reverseHelp = \nonempty, left, right ->
    if left < right then
        reverseHelp (swap nonempty left right) (left + 1) (right - 1)
    else
        nonempty


contains : NonemptyList a, a -> Bool
contains = \nonempty, value ->
    any nonempty (\x -> x == value)


walk : NonemptyList a, b, (b, a -> b) -> b
walk = \(@NonemptyList { rest, lastItem }), initialValue, walkFunc ->
     List.walk rest initialValue walkFunc
        |> walkFunc lastItem


walkBackwards : NonemptyList a, b, (b, a -> b) -> b
walkBackwards = \(@NonemptyList { rest, lastItem }), initialValue, walkFunc ->
      walkFunc initialValue lastItem
        |> (\value -> List.walk rest value walkFunc)


sum : NonemptyList (Num a) -> Num a
sum = \(@NonemptyList { rest, lastItem }) ->
    List.sum rest + lastItem


product : NonemptyList (Num a) -> Num a
product = \(@NonemptyList { rest, lastItem }) ->
    List.product rest * lastItem


any : NonemptyList a, (a -> Bool) -> Bool
any = \(@NonemptyList { rest, lastItem }), predicate ->
    List.any rest predicate || predicate lastItem


all : NonemptyList a, (a -> Bool) -> Bool
all = \(@NonemptyList { rest, lastItem }), predicate ->
    List.all rest predicate && predicate lastItem


keepIf : NonemptyList a, (a -> Bool) -> List a
keepIf = \(@NonemptyList { rest, lastItem }), predicate ->
    list = List.keepIf rest predicate
    if predicate lastItem then
        List.append list lastItem
    else
        list


dropIf : NonemptyList a, (a -> Bool) -> List a
dropIf = \(@NonemptyList { rest, lastItem }), predicate ->
    list = List.dropIf rest predicate
    if predicate lastItem then
        list
    else
        List.append list lastItem


keepOks : NonemptyList before, (before -> Result after *) -> List after
keepOks = \(@NonemptyList { rest, lastItem }), toResult ->
    list = List.keepOks rest toResult
    when toResult lastItem is
        Ok ok ->
            List.append list ok

        Err _ ->
            list


keepErrs : NonemptyList before, (before -> Result * after) -> List after
keepErrs = \(@NonemptyList { rest, lastItem }), toResult ->
    list = List.keepErrs rest toResult
    when toResult lastItem is
        Ok _ ->
            list

        Err err ->
            List.append list err


map : NonemptyList a, (a -> b) -> NonemptyList b
map = \(@NonemptyList { rest, lastItem }), mapFunc ->
    (@NonemptyList { rest: List.map rest mapFunc, lastItem: mapFunc lastItem })


map2 : NonemptyList a, NonemptyList b, (a, b -> c) -> NonemptyList c
map2 = \a, b, mapFunc ->
    when List.map2 (toList a) (toList b) mapFunc |> fromList is
        Ok nonempty ->
            nonempty

        Err _ ->
            # This should never happen
            mapFunc (last a) (last b) |> single


map3 : NonemptyList a, NonemptyList b, NonemptyList c, (a, b, c -> d) -> NonemptyList d
map3 = \a, b, c, mapFunc ->
    when List.map3 (toList a) (toList b) (toList c) mapFunc |> fromList is
        Ok nonempty ->
            nonempty

        Err _ ->
            # This should never happen
            mapFunc (last a) (last b) (last c) |> single


map4 : NonemptyList a, NonemptyList b, NonemptyList c, NonemptyList d, (a, b, c, d -> e) -> NonemptyList e
map4 = \a, b, c, d, mapFunc ->
    when List.map4 (toList a) (toList b) (toList c) (toList d) mapFunc |> fromList is
        Ok nonempty ->
            nonempty

        Err _ ->
            # This should never happen
            mapFunc (last a) (last b) (last c) (last d) |> single


mapWithIndex : NonemptyList a, (a, Nat -> b) -> NonemptyList b
mapWithIndex = \(@NonemptyList { rest, lastItem }), mapFunc ->
    @NonemptyList { rest: List.mapWithIndex rest mapFunc, lastItem: mapFunc lastItem (List.len rest) }


#range : Int a, Int a -> NonemptyList (Int a)
#range = \start, end ->
#    when Num.compare start end is
#        GT -> []
#        EQ -> single start
#        LT ->
#            end2 = end - 1
#            length = Num.intCast (end2 - start)
#
#            { rest: rangeHelp (List.withCapacity length) start end2
#            , lastItem: end
#            }
#                |> @NonemptyList


#rangeHelp : List (Int a), Int a, Int a -> List (Int a)
#rangeHelp = \accum, start, end ->
#    if end <= start then
#        accum
#    else
#        rangeHelp (List.appendUnsafe accum start) (start + 1) end


sortWith : NonemptyList a, (a, a -> [ LT, EQ, GT ]) -> NonemptyList a
sortWith = \nonempty, sortFunc ->
    when toList nonempty |> List.sortWith sortFunc |> fromList is
        Ok nonempty2 -> nonempty2
        Err _ ->
            # This should never happen
            nonempty


sortAsc : NonemptyList (Num a) -> NonemptyList (Num a)
sortAsc = \nonempty ->
    sortWith nonempty Num.compare


sortDesc : NonemptyList (Num a) -> NonemptyList (Num a)
sortDesc = \nonempty ->
    sortWith nonempty (\a, b -> Num.compare b a)


first : NonemptyList a -> a
first = \(@NonemptyList { rest, lastItem }) ->
    List.first rest |> Result.withDefault lastItem


last : NonemptyList a -> a
last = \(@NonemptyList { lastItem }) ->
    lastItem


dropFirst : NonemptyList a -> List a
dropFirst = \nonempty ->
    toList nonempty |> List.dropFirst


dropLast : NonemptyList a -> List a
dropLast = \(@NonemptyList { rest }) ->
    rest


takeFirst : NonemptyList a, Nat -> List a
takeFirst = \nonempty, count ->
    List.takeFirst (toList nonempty) count


takeLast : NonemptyList a, Nat -> List a
takeLast = \nonempty, count ->
    List.takeLast (toList nonempty) count


drop : NonemptyList a, Nat -> List a
drop = \nonempty, count ->
    List.drop (toList nonempty) count


dropAt : NonemptyList a, Nat -> List a
dropAt = \nonempty, index ->
    List.dropAt (toList nonempty) index


min : NonemptyList (Num a) -> Num a
min = \(@NonemptyList { rest, lastItem }) ->
    when List.min rest is
        Ok value ->
            if value < lastItem then
                value
            else
                lastItem

        Err _ ->
            lastItem


max : NonemptyList (Num a) -> Num a
max = \(@NonemptyList { rest, lastItem }) ->
    when List.max rest is
        Ok value ->
            if value > lastItem then
                value
            else
                lastItem

        Err _ ->
            lastItem


joinMap : NonemptyList a, (a -> NonemptyList b) -> NonemptyList b
joinMap = \nonempty, mapper ->
    when List.joinMap (toList nonempty) (\item -> mapper item |> toList) |> fromList is
        Ok nonempty2 ->
            nonempty2

        Err _ ->
            # This should never happen
            last nonempty |> mapper


find : NonemptyList a, (a -> Bool) -> Result a [NotFound]*
find = \nonempty, predicate ->
    List.find (toList nonempty) predicate


## Returns the index at which the first element in the list
## satisfying a predicate function can be found.
## If no satisfying element is found, an `Err NotFound` is returned.
findIndex : NonemptyList elem, (elem -> Bool) -> Result Nat [NotFound]*
findIndex = \nonempty, matcher ->
    foundIndex = iterate nonempty 0 \index, elem ->
        if matcher elem then
            Break index
        else
            Continue (index + 1)

    when foundIndex is
        Break index -> Ok index
        Continue _ -> Err NotFound


iterate : NonemptyList elem, s, (s, elem -> [Continue s, Break b]) -> [Continue s, Break b]
iterate = \nonempty, init, func ->
    iterHelp nonempty init func 0 (len nonempty)


## internal helper
iterHelp : NonemptyList elem, s, (s, elem -> [Continue s, Break b]), Nat, Nat -> [Continue s, Break b]
iterHelp = \list, state, f, index, length ->
    if index < length then
        when f state (getUnsafe list index) is
            Continue nextState ->
                iterHelp list nextState f (index + 1) length

            Break b ->
                Break b
    else
        Continue state


## Remove this as soon as List.iterate is exposed
getUnsafe : NonemptyList a, Nat -> a
getUnsafe = \list, index ->
    when get list index is
        Ok ok ->
            ok

        Err _ ->
            getUnsafe list index

sublist : NonemptyList a, { start: Nat, len: Nat } -> List a
sublist = \nonempty, config ->
    List.sublist (toList nonempty) config


intersperse : NonemptyList a, a -> NonemptyList a
intersperse = \(@NonemptyList { rest, lastItem }), value ->
    @NonemptyList { rest: List.append (List.intersperse rest value) value, lastItem: lastItem }


split : NonemptyList a, Nat -> { before: List a, others: List a }
split = \nonempty, index ->
    List.split (toList nonempty) index
